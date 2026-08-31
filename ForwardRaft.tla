----------------------------- MODULE ForwardRaft -------------------------------
\*
\* TLA+ Specification for Tarantool Raft Protocol with Limbo
\*
\* This specification models a modified Raft consensus protocol used in
\* Tarantool DBMS. The key difference from vanilla Raft is the separation of
\* leader election (Raft) and transaction processing (Limbo).
\*
\* Main features:
\* - Vanilla Raft elections with terms and votes
\* - Limbo module for transaction processing with PROMOTE and CONFIRM entries
\* - Vector clock (vclock) for tracking confirmed transactions per node
\* - PROMOTE entry requirement: new leader must get quorum on PROMOTE before
\*   committing old-term transactions (fixing split-brain issue)
\*

EXTENDS TLC, Integers, Sequences, FiniteSets

--------------------------------------------------------------------------------
\*
\* Constants
\*

\* Node IDs in the cluster
CONSTANT NodeIDs
CONSTANT VoterIDs

\* All transactions to execute (set of identifiers)
CONSTANT AllTransactions

\* Maximum term allowed before stopping
CONSTANT MaxTerm

\* Initial limbo owner (must be in NodeIDs)
CONSTANT InitialLimboOwner

\* Null value
CONSTANT NULL

\* Entry types
CONSTANT EntryTypeTransaction
CONSTANT EntryTypePromote
CONSTANT EntryTypeConfirm

\* Raft states
CONSTANT RaftStateFollower
CONSTANT RaftStateLeader

\* Limbo states
CONSTANT LimboStateReplica
CONSTANT LimboStateLeader

\* Transaction result types
CONSTANT TxnResultCommit
CONSTANT TxnResultRollback
CONSTANT TxnResultUnknown

CONSTANT NodeRoleCandidate
CONSTANT NodeRoleVoter

\* Symmetry - all nodes and transactions are equivalent
Perms == Permutations(NodeIDs) \union Permutations(AllTransactions)

\* Maximum expected journal length per node
MaxJournalLength == (MaxTerm * 2 + Cardinality(AllTransactions) * 2) * Cardinality(NodeIDs)

--------------------------------------------------------------------------------
\*
\* Variables
\*

\* Per-node state
VARIABLE Nodes

\* Remaining transactions to create (set)
VARIABLE TransactionsToDo

\* Completed transactions: map from transaction data -> result (commit/rollback)
VARIABLE TransactionsDone

\* Highest term that has elected a leader (0 initially)
VARIABLE LeaderTerm

\* Terms that have created a transaction: map from term -> 0 or 1
VARIABLE TransactionTerms

vars == <<Nodes, TransactionsToDo, TransactionsDone, LeaderTerm, TransactionTerms>>

--------------------------------------------------------------------------------
\*
\* Helper functions for object field manipulation
\*

\* Single field setters - operate on node objects directly
SetRaftTerm(v, s) == [s EXCEPT !.raft_term = v]
SetRaftState(v, s) == [s EXCEPT !.raft_state = v]
SetLimboState(v, s) == [s EXCEPT !.limbo_state = v]
SetLimboTerm(v, s) == [s EXCEPT !.limbo_term = v]
SetLimboOwner(v, s) == [s EXCEPT !.limbo_owner = v]
SetLimboVclock(v, s) == [s EXCEPT !.limbo_vclock = v]
SetLimboTermMap(v, s) == [s EXCEPT !.limbo_term_map = v]
SetLimboPromotions(v, s) == [s EXCEPT !.limbo_promotions = v]
SetLimbo(v, s) == [s EXCEPT !.limbo = v]
SetData(v, s) == [s EXCEPT !.data = v]
SetNextLSN(v, s) == [s EXCEPT !.next_lsn = v]
JournalAppend(entry, node) == [node EXCEPT !.journal = Append(node.journal, entry)]

\* Array operations
ArrLen(s) == Len(s)
ArrLast(s) == s[Len(s)]
ArrIsEmpty(s) == Len(s) = 0
ArrAppend(v, s) == Append(s, v)

\* Update a node in the Nodes dictionary
NodesUpdate(nid, node) == [Nodes EXCEPT ![nid] = node]

\* Vclock operations
VclockSet(vclock, nid, val) == [vclock EXCEPT ![nid] = val]

\* Transaction result tracking helpers
TxnMarkCommit(txn_data) ==
    /\ Assert(TransactionsDone[txn_data] \in {TxnResultUnknown, TxnResultCommit},
             "Transaction cannot be committed after rollback")
    /\ TransactionsDone' = [TransactionsDone EXCEPT ![txn_data] = TxnResultCommit]

TxnMarkRollback(txn_data) ==
    /\ Assert(TransactionsDone[txn_data] \in {TxnResultUnknown, TxnResultRollback},
             "Transaction cannot be rolled back after commit")
    /\ TransactionsDone' = [TransactionsDone EXCEPT ![txn_data] = TxnResultRollback]

--------------------------------------------------------------------------------
\*
\* Constructors and helpers
\*

\* Quorum size calculation
Quorum == (Cardinality(NodeIDs) \div 2) + 1

\* Check if the system should stop making progress
\* (either max term reached or all transactions done)
ShouldStop ==
    \/ \E nid \in NodeIDs: Nodes[nid].raft_term >= MaxTerm
    \/ \A t \in AllTransactions: TransactionsDone[t] # TxnResultUnknown

\* Create a new transaction entry. It carries no term - the receivers derive
\* it from the origin's component in their limbo term map.
EntryNewTransaction(origin_id, lsn, data) == [
    type |-> EntryTypeTransaction,
    origin_id |-> origin_id,
    lsn |-> lsn,
    data |-> data
]

\* Create a new PROMOTE entry. The term map carries the terms of all the
\* promotions squashed into this one - one PROMOTE can represent a whole
\* chain of them, with terms of different origins, or even multiple terms
\* of the same origin (then only the biggest one is kept).
EntryNewPromote(origin_id, lsn, raft_term, prev_owner, confirm_lsn,
                confirmed_vclock, term_map) == [
    type |-> EntryTypePromote,
    origin_id |-> origin_id,
    lsn |-> lsn,
    raft_term |-> raft_term,
    prev_owner |-> prev_owner,
    confirm_lsn |-> confirm_lsn,
    confirmed_vclock |-> confirmed_vclock,
    term_map |-> term_map
]

\* Create a new CONFIRM entry
EntryNewConfirm(origin_id, lsn, owner_id, confirm_lsn) == [
    type |-> EntryTypeConfirm,
    origin_id |-> origin_id,
    lsn |-> lsn,
    owner_id |-> owner_id,
    confirm_lsn |-> confirm_lsn
]

\* Check if two entries are equal (same origin and LSN)
EntriesEqual(e1, e2) ==
    /\ e1.origin_id = e2.origin_id
    /\ e1.lsn = e2.lsn

\* Check if a promotion entry is valid (has origin_id field)
PromoteIsValid(promote) ==
    "origin_id" \in DOMAIN promote

\* Create an invalid/empty promotion entry
PromoteEmpty == [null |-> NULL]

\* Check if a transaction entry is valid (has origin_id field)
TxnIsValid(txn) ==
    "origin_id" \in DOMAIN txn

\* Create an invalid/empty transaction entry
TxnEmpty == [null |-> NULL]

\* Promotions dictionary operations
PromotionsEmpty == [i \in NodeIDs |-> PromoteEmpty]
PromotionsSet(nid, promote, promotions) == [promotions EXCEPT ![nid] = promote]
PromotionsRemoveUpToTerm(term, promotions) ==
    [nid \in DOMAIN(promotions) |->
        IF PromoteIsValid(promotions[nid]) /\ promotions[nid].raft_term <= term
        THEN PromoteEmpty
        ELSE promotions[nid]]
PromotionsFindPending(nid, confirm_lsn, promotions) ==
    LET promote == promotions[nid]
    IN IF PromoteIsValid(promote) /\ promote.confirm_lsn = confirm_lsn
       THEN promote
       ELSE PromoteEmpty
PromotionsGetLatest(promotions) ==
    IF \E nid \in DOMAIN(promotions): PromoteIsValid(promotions[nid])
    THEN LET latestNid == CHOOSE nid \in DOMAIN(promotions):
                /\ PromoteIsValid(promotions[nid])
                /\ \A otherNid \in DOMAIN(promotions):
                    PromoteIsValid(promotions[otherNid]) =>
                    promotions[nid].raft_term >= promotions[otherNid].raft_term
         IN promotions[latestNid]
    ELSE PromoteEmpty

\* Check if node has an entry in its journal
HasEntry(node, entry) ==
    \E i \in DOMAIN(node.journal):
        EntriesEqual(node.journal[i], entry)

\* Count how many nodes have a specific entry and have term <= given term
\* This ensures we only count acknowledgments from nodes that haven't moved to a higher term
CountNodesWithEntry(entry, max_term) ==
    Cardinality({nid \in NodeIDs:
        /\ HasEntry(Nodes[nid], entry)
        /\ Nodes[nid].raft_term <= max_term})

\* Check if all journal entries from 'from' node are present in 'to' node
JournalIsFullyReplicatedTo(from, to) ==
    \A i \in DOMAIN(from.journal):
        HasEntry(to, from.journal[i])

\* Create new node state
NodeNew(nid) == [
    role |-> IF nid \in VoterIDs THEN NodeRoleVoter ELSE NodeRoleCandidate,
    journal |-> <<>>,
    raft_term |-> 1,
    raft_state |-> RaftStateFollower,
    limbo_state |-> LimboStateReplica,
    limbo_term |-> 1,
    limbo_owner |-> InitialLimboOwner,
    limbo_vclock |-> [i \in NodeIDs |-> -1],
    \* Last known term of each node, taken from that node's last confirmed
    \* PROMOTE. Used to find the term of the incoming transactions by their
    \* origin, like the real code does.
    limbo_term_map |-> [i \in NodeIDs |-> 0],
    limbo_promotions |-> PromotionsEmpty,
    limbo |-> TxnEmpty,
    data |-> <<>>,
    next_lsn |-> 1
]

\* Initialize state
Init ==
    /\ Nodes = [nid \in NodeIDs |-> NodeNew(nid)]
    /\ TransactionsToDo = AllTransactions
    /\ TransactionsDone = [t \in AllTransactions |-> TxnResultUnknown]
    /\ LeaderTerm = 0
    /\ TransactionTerms = [term \in 1..MaxTerm |-> 0]

--------------------------------------------------------------------------------
\*
\* Raft election actions
\*

\* Node randomly bumps its term to start an election
NodeBumpTerm(nid) ==
    LET node == Nodes[nid]
    IN
    /\ ~ShouldStop
    /\ node.role = NodeRoleCandidate
    /\ node.raft_state = RaftStateFollower
    \* ---
    /\ Nodes' = NodesUpdate(nid,
                SetRaftTerm(node.raft_term + 1,
                SetLimboState(LimboStateReplica,
                node)))
    /\ UNCHANGED<<TransactionsToDo, TransactionsDone, LeaderTerm, TransactionTerms>>

\* Node becomes Raft leader after having quorum of nodes with same term and fully replicated journals
NodeBecomeLeader(nid) ==
    LET node == Nodes[nid]
        term == node.raft_term
    IN
    /\ term > LeaderTerm
    /\ node.role = NodeRoleCandidate
    /\ Assert(node.raft_state = RaftStateFollower, "Node can't be leader with term > leader's")
    /\ LET quorum_nodes == {other_nid \in NodeIDs:
               /\ JournalIsFullyReplicatedTo(Nodes[other_nid], node)
               /\ Nodes[other_nid].raft_term = term}
       IN Cardinality(quorum_nodes) >= Quorum
    \* ---
    /\ Assert(term > LeaderTerm, "New leader term must be greater than previous leader term")
    /\ Nodes' = NodesUpdate(nid, SetRaftState(RaftStateLeader, node))
    /\ LeaderTerm' = term
    /\ UNCHANGED<<TransactionsToDo, TransactionsDone, TransactionTerms>>

\* Node randomly steps down from leader (simulating crash/restart)
NodeStepDown(nid) ==
    LET node == Nodes[nid]
    IN
    /\ node.raft_state = RaftStateLeader \/ node.limbo_state = LimboStateLeader
    \* ---
    /\ Nodes' = NodesUpdate(nid,
                SetRaftState(RaftStateFollower,
                SetLimboState(LimboStateReplica,
                node)))
    /\ UNCHANGED<<TransactionsToDo, TransactionsDone, LeaderTerm, TransactionTerms>>

\* Node observes higher term from another node and steps down
NodeObserveHigherTerm(dst_nid, src_nid) ==
    LET dst_node == Nodes[dst_nid]
        src_term == Nodes[src_nid].raft_term
    IN
    /\ src_nid # dst_nid
    /\ src_term > dst_node.raft_term
    \* ---
    /\ Nodes' = NodesUpdate(dst_nid,
                SetRaftTerm(src_term,
                SetRaftState(RaftStateFollower,
                SetLimboState(LimboStateReplica,
                dst_node))))
    /\ UNCHANGED<<TransactionsToDo, TransactionsDone, LeaderTerm, TransactionTerms>>

--------------------------------------------------------------------------------
\*
\* Limbo PROMOTE actions
\*

\* Raft leader writes PROMOTE right after winning the elections, without
\* waiting for the pending txns to reach a quorum of replicas. The elections
\* guarantee the leader already has every entry which could have gathered a
\* quorum anywhere, and the quorum on the PROMOTE itself transitively
\* certifies the leader's whole journal before anything gets confirmed -
\* the PROMOTE is the last journal entry and the replication is strictly
\* ordered.
LimboWritePromote(nid) ==
    LET node == Nodes[nid]
    IN
    /\ node.raft_state = RaftStateLeader
    /\ node.raft_term > node.limbo_term
    /\ LET old_promote == node.limbo_promotions[nid]
       IN IF PromoteIsValid(old_promote) THEN old_promote.raft_term < node.raft_term ELSE TRUE
    \* ---
    /\ LET latest_promote == PromotionsGetLatest(node.limbo_promotions)
           has_pending == PromoteIsValid(latest_promote)
           \* prev_owner: use latest (previous) promote's origin_id if exists, otherwise current limbo owner
           prev_owner == IF has_pending
                         THEN latest_promote.prev_owner
                         ELSE node.limbo_owner
           \* confirm_lsn: use latest (previous) promote's if exists, otherwise limbo/vclock
           confirm_lsn == IF has_pending
                          THEN latest_promote.confirm_lsn
                          ELSE IF TxnIsValid(node.limbo)
                               THEN node.limbo.lsn
                               ELSE node.limbo_vclock[node.limbo_owner]
           \* confirmed_vclock: use latest promote's if exists, otherwise limbo vclock
           base_vclock == IF has_pending
                          THEN latest_promote.confirmed_vclock
                          ELSE node.limbo_vclock
           \* term_map: accumulate the chain's terms the same way as the
           \* confirmed vclock, folding this promotion's own term in
           base_term_map == IF has_pending
                            THEN latest_promote.term_map
                            ELSE node.limbo_term_map
           entry == EntryNewPromote(
               nid,
               node.next_lsn,
               node.raft_term,
               prev_owner,
               confirm_lsn,
               VclockSet(base_vclock, prev_owner, confirm_lsn),
               VclockSet(base_term_map, nid, node.raft_term)
           )
           old_promote == node.limbo_promotions[nid]
           new_promotions == PromotionsSet(nid, entry, node.limbo_promotions)
       IN
       /\ Assert(~PromoteIsValid(old_promote) \/ old_promote.raft_term <= entry.raft_term,
                 "New PROMOTE must have term >= old PROMOTE term")
       /\ Assert(~PromoteIsValid(old_promote) \/ old_promote.lsn < entry.lsn,
                 "New PROMOTE must have LSN > old PROMOTE LSN")
       /\ Nodes' = NodesUpdate(nid,
                    SetLimboPromotions(new_promotions,
                    SetNextLSN(node.next_lsn + 1,
                    JournalAppend(entry, node))))
    /\ UNCHANGED<<TransactionsToDo, TransactionsDone, LeaderTerm, TransactionTerms>>

\* Leader confirms PROMOTE after quorum receives it
LimboConfirmPromote(nid) ==
    LET node == Nodes[nid]
        promote_entry == node.limbo_promotions[nid]
    IN
    /\ node.raft_state = RaftStateLeader
    /\ PromoteIsValid(promote_entry)
    /\ promote_entry.raft_term = node.raft_term
    /\ CountNodesWithEntry(promote_entry, node.raft_term) >= Quorum
    \* ---
    /\ Assert(promote_entry.raft_term > node.limbo_term,
              "Local pending promote's term is always bigger than the last confirmed limbo term")
    /\ Assert(\A i \in DOMAIN(node.limbo_promotions):
                  ~PromoteIsValid(node.limbo_promotions[i]) \/ node.limbo_promotions[i].raft_term <= node.raft_term,
              "No promotion can have bigger term than current node term")
    /\ LET has_txn == TxnIsValid(node.limbo)
           txn_entry == node.limbo
           \* Commit/rollback transaction based on this PROMOTE's confirm_lsn
           owner_matches == has_txn /\ txn_entry.origin_id = promote_entry.prev_owner
           should_commit == owner_matches /\ txn_entry.lsn <= promote_entry.confirm_lsn
           confirm_entry == EntryNewConfirm(
               nid,
               node.next_lsn,
               promote_entry.prev_owner,
               promote_entry.confirm_lsn
           )
           new_data == IF should_commit THEN ArrAppend(txn_entry.data, node.data) ELSE node.data
       IN
       /\ Assert(\A i \in NodeIDs:
                   promote_entry.confirmed_vclock[i] >= node.limbo_vclock[i],
                 "PROMOTE's confirmed_vclock must be >= limbo vclock")
       /\ Assert(\A i \in NodeIDs:
                   promote_entry.term_map[i] >= node.limbo_term_map[i],
                 "PROMOTE's term map must be >= the local term map")
       /\ Assert(\E i \in NodeIDs:
                   promote_entry.term_map[i] > node.limbo_term_map[i],
                 "PROMOTE's term map must advance at least one component")
       /\ IF has_txn
          THEN IF should_commit
               THEN TxnMarkCommit(txn_entry.data)
               ELSE TxnMarkRollback(txn_entry.data)
          ELSE UNCHANGED TransactionsDone
       /\ Nodes' = NodesUpdate(nid,
                    SetLimboTerm(promote_entry.raft_term,
                    SetLimboOwner(nid,
                    SetLimboVclock(promote_entry.confirmed_vclock,
                    SetLimboTermMap(promote_entry.term_map,
                    SetLimboPromotions(PromotionsEmpty,
                    SetLimbo(TxnEmpty,
                    SetData(new_data,
                    SetNextLSN(node.next_lsn + 1,
                    SetLimboState(LimboStateLeader,
                    JournalAppend(confirm_entry, node)))))))))))
    /\ UNCHANGED<<TransactionsToDo, LeaderTerm, TransactionTerms>>

--------------------------------------------------------------------------------
\*
\* Limbo transaction actions
\*

\* Limbo leader creates a new transaction
LimboCreateTransaction(nid) ==
    LET node == Nodes[nid]
    IN
    /\ node.limbo_state = LimboStateLeader
    /\ ~TxnIsValid(node.limbo)
    /\ TransactionTerms[node.limbo_term] = 0
    \* ---
    /\ \E txn_data \in TransactionsToDo:
        LET entry == EntryNewTransaction(nid, node.next_lsn, txn_data)
        IN
        /\ TransactionsToDo' = TransactionsToDo \ {txn_data}
        /\ TransactionTerms' = [TransactionTerms EXCEPT ![node.limbo_term] = 1]
        /\ Nodes' = NodesUpdate(nid,
                    SetLimbo(entry,
                    SetNextLSN(node.next_lsn + 1,
                    JournalAppend(entry, node))))
        /\ UNCHANGED<<TransactionsDone, LeaderTerm>>

\* Limbo leader confirms transaction after quorum receives it
LimboConfirmTransaction(nid) ==
    LET node == Nodes[nid]
        txn_entry == node.limbo
    IN
    /\ node.limbo_state = LimboStateLeader
    /\ TxnIsValid(node.limbo)
    /\ CountNodesWithEntry(txn_entry, node.raft_term) >= Quorum
    \* ---
    /\ LET confirm_entry == EntryNewConfirm(
               nid,
               node.next_lsn,
               nid,
               txn_entry.lsn
           )
       IN
       /\ Assert(txn_entry.lsn >= node.limbo_vclock[nid],
                 "Vclock LSN must not decrease")
       /\ TxnMarkCommit(txn_entry.data)
       /\ Nodes' = NodesUpdate(nid,
                    SetLimbo(TxnEmpty,
                    SetLimboVclock(VclockSet(node.limbo_vclock, nid, txn_entry.lsn),
                    SetData(ArrAppend(txn_entry.data, node.data),
                    SetNextLSN(node.next_lsn + 1,
                    JournalAppend(confirm_entry, node))))))
    /\ UNCHANGED<<TransactionsToDo, LeaderTerm, TransactionTerms>>

--------------------------------------------------------------------------------
\*
\* Replication actions
\*

\* Find the next journal entry to replicate (first one not present on destination)
\* Returns 0 if destination has all entries, otherwise returns the index
NextEntryToReplicate(src_node, dst_node) ==
    IF \E i \in DOMAIN(src_node.journal): ~HasEntry(dst_node, src_node.journal[i])
    THEN CHOOSE i \in DOMAIN(src_node.journal):
        /\ ~HasEntry(dst_node, src_node.journal[i])
        /\ \A j \in DOMAIN(src_node.journal):
            ~HasEntry(dst_node, src_node.journal[j]) => i <= j
    ELSE 0

\* Apply a PROMOTE entry to destination node
ReplicatePromote(entry, dst_nid) ==
    LET dst_node == Nodes[dst_nid]
    IN
    /\ IF entry.raft_term <= dst_node.limbo_term
       THEN
           \* Ignore old PROMOTE (already confirmed)
           Nodes' = NodesUpdate(dst_nid, JournalAppend(entry, dst_node))
       ELSE
           \* New term PROMOTE - store directly
           LET old_promote == dst_node.limbo_promotions[entry.origin_id]
               new_promotions == PromotionsSet(entry.origin_id, entry, dst_node.limbo_promotions)
           IN
           /\ Assert(~PromoteIsValid(old_promote) \/ old_promote.raft_term <= entry.raft_term,
                     "New PROMOTE must have term >= old PROMOTE term")
           /\ Assert(~PromoteIsValid(old_promote) \/ old_promote.lsn < entry.lsn,
                     "New PROMOTE must have LSN > old PROMOTE LSN")
           /\ Nodes' = NodesUpdate(dst_nid,
                        SetLimboState(LimboStateReplica,
                        SetLimboPromotions(new_promotions,
                        JournalAppend(entry, dst_node))))
    /\ UNCHANGED TransactionsDone

\* Apply CONFIRM on PROMOTE entry to destination node
ReplicateConfirmPromote(entry, dst_nid, promote) ==
    LET dst_node == Nodes[dst_nid]
        has_txn == TxnIsValid(dst_node.limbo)
        txn_entry == dst_node.limbo
        \* Commit/rollback transaction based on this PROMOTE's confirm_lsn
        owner_matches == has_txn /\ txn_entry.origin_id = promote.prev_owner
        should_commit == owner_matches /\ txn_entry.lsn <= promote.confirm_lsn
        \* Always clear limbo (commit if covered, rollback if not)
        new_data == IF should_commit THEN ArrAppend(txn_entry.data, dst_node.data) ELSE dst_node.data
        \* Remove promotions with term <= confirmed promote's term, keep higher ones
        new_promotions == PromotionsRemoveUpToTerm(promote.raft_term, dst_node.limbo_promotions)
    IN
    /\ Assert(has_txn => txn_entry.origin_id = dst_node.limbo_owner,
             "Transaction origin must match current limbo owner")
    /\ Assert(entry.confirm_lsn = promote.confirm_lsn,
             "CONFIRM lsn must match pending PROMOTE confirm_lsn")
    /\ Assert(\A i \in NodeIDs:
                promote.confirmed_vclock[i] >= dst_node.limbo_vclock[i],
              "PROMOTE's confirmed_vclock must be >= limbo vclock")
    /\ Assert(\A i \in NodeIDs:
                promote.term_map[i] >= dst_node.limbo_term_map[i],
              "PROMOTE's term map must be >= the local term map")
    /\ Assert(\E i \in NodeIDs:
                promote.term_map[i] > dst_node.limbo_term_map[i],
              "PROMOTE's term map must advance at least one component")
    /\ IF has_txn
       THEN IF should_commit
            THEN TxnMarkCommit(txn_entry.data)
            ELSE TxnMarkRollback(txn_entry.data)
       ELSE UNCHANGED TransactionsDone
    /\ Nodes' = NodesUpdate(dst_nid,
                 SetLimboTerm(promote.raft_term,
                 SetLimboOwner(promote.origin_id,
                 SetLimboVclock(promote.confirmed_vclock,
                 SetLimboTermMap(promote.term_map,
                 SetLimboPromotions(new_promotions,
                 SetLimbo(TxnEmpty,
                 SetData(new_data,
                 JournalAppend(entry, dst_node)))))))))

\* Apply CONFIRM on transaction entry to destination node
ReplicateConfirmTransaction(entry, dst_nid) ==
    LET dst_node == Nodes[dst_nid]
        new_vclock == VclockSet(dst_node.limbo_vclock, entry.owner_id, entry.confirm_lsn)
        txn_entry == dst_node.limbo
    IN
    /\ Assert(TxnIsValid(dst_node.limbo),
             "No transaction to confirm")
    /\ Assert(txn_entry.origin_id = entry.owner_id,
             "Transaction origin must match CONFIRM owner")
    /\ Assert(entry.confirm_lsn >= dst_node.limbo_vclock[entry.owner_id],
             "Vclock LSN must not decrease")
    /\ TxnMarkCommit(txn_entry.data)
    /\ Nodes' = NodesUpdate(dst_nid,
                 SetLimboVclock(new_vclock,
                 SetLimbo(TxnEmpty,
                 SetData(ArrAppend(txn_entry.data, dst_node.data),
                 JournalAppend(entry, dst_node)))))

\* Apply a CONFIRM entry to destination node
ReplicateConfirm(entry, dst_nid) ==
    LET dst_node == Nodes[dst_nid]
        current_lsn == dst_node.limbo_vclock[entry.owner_id]
        promote == PromotionsFindPending(entry.origin_id, entry.confirm_lsn, dst_node.limbo_promotions)
    IN
    IF PromoteIsValid(promote)
    THEN ReplicateConfirmPromote(entry, dst_nid, promote)
    ELSE IF entry.confirm_lsn <= current_lsn
    THEN /\ Nodes' = NodesUpdate(dst_nid, JournalAppend(entry, dst_node))
         /\ UNCHANGED TransactionsDone
    ELSE IF entry.owner_id = dst_node.limbo_owner
    THEN ReplicateConfirmTransaction(entry, dst_nid)
    ELSE Assert(FALSE, "Invalid CONFIRM from non-owner")

\* Apply a transaction entry to destination node
ReplicateTransaction(entry, dst_nid) ==
    LET dst_node == Nodes[dst_nid]
        is_from_owner == entry.origin_id = dst_node.limbo_owner
        \* The entry carries no term. The origin's term is derived from the
        \* local term map - the term of the origin's last confirmed PROMOTE.
        \* The ordered replication makes this equal to attaching the creation
        \* term to the txn: the txn is always received after the origin's
        \* promote confirmation and before any newer rows of that origin.
        is_old_term == dst_node.limbo_term_map[entry.origin_id] < dst_node.limbo_term
    IN
    IF is_from_owner
    THEN
        \* Valid transaction from owner
        /\ Nodes' = NodesUpdate(dst_nid,
                     SetLimbo(entry,
                     JournalAppend(entry, dst_node)))
        /\ UNCHANGED TransactionsDone
    ELSE IF is_old_term
    THEN
        \* Rollback old term transaction
        /\ TxnMarkRollback(entry.data)
        /\ Nodes' = NodesUpdate(dst_nid, JournalAppend(entry, dst_node))
    ELSE
        \* Invalid: transaction from non-owner in current/future term
        Assert(FALSE, "Invalid transaction from non-owner")

\* Main replication action: replicate next entry from src to dst
ReplicateNextEntry(src_nid, dst_nid) ==
    LET src_node == Nodes[src_nid]
        dst_node == Nodes[dst_nid]
    IN
    /\ src_nid # dst_nid
    /\ dst_node.role # NodeRoleVoter
    /\ LET next_idx == NextEntryToReplicate(src_node, dst_node) IN
       /\ next_idx # 0
       /\ LET entry == src_node.journal[next_idx] IN
          /\ CASE entry.type = EntryTypePromote -> ReplicatePromote(entry, dst_nid)
               [] entry.type = EntryTypeConfirm -> ReplicateConfirm(entry, dst_nid)
               [] entry.type = EntryTypeTransaction -> ReplicateTransaction(entry, dst_nid)
    /\ UNCHANGED<<TransactionsToDo, LeaderTerm, TransactionTerms>>
--------------------------------------------------------------------------------
\*
\* Main specification
\*

Next ==
    \/ \E nid \in NodeIDs: NodeBumpTerm(nid)
    \/ \E nid \in NodeIDs: NodeBecomeLeader(nid)
    \/ \E nid \in NodeIDs: NodeStepDown(nid)
    \/ \E src \in NodeIDs, dst \in NodeIDs: NodeObserveHigherTerm(dst, src)
    \/ \E nid \in NodeIDs: LimboWritePromote(nid)
    \/ \E nid \in NodeIDs: LimboConfirmPromote(nid)
    \/ \E nid \in NodeIDs: LimboCreateTransaction(nid)
    \/ \E nid \in NodeIDs: LimboConfirmTransaction(nid)
    \/ \E src \in NodeIDs, dst \in NodeIDs: ReplicateNextEntry(src, dst)

--------------------------------------------------------------------------------
\*
\* Invariants
\*

\* Data consistency: for any two nodes, their data is either identical
\* or one is a prefix of the other
DataConsistencyInvariant ==
    \A nid1 \in NodeIDs, nid2 \in NodeIDs:
        LET data1 == Nodes[nid1].data
            data2 == Nodes[nid2].data
            len1 == Len(data1)
            len2 == Len(data2)
            minlen == IF len1 < len2 THEN len1 ELSE len2
        IN \A i \in 1..minlen:
            data1[i] = data2[i]

\* No duplicate PROMOTE entries with same term in promotions dictionary
PromotionQueueInvariant ==
    \A node_id \in NodeIDs:
        LET promotions == Nodes[node_id].limbo_promotions
        IN \A i \in DOMAIN(promotions), j \in DOMAIN(promotions):
            /\ i # j
            /\ PromoteIsValid(promotions[i])
            /\ PromoteIsValid(promotions[j])
            => promotions[i].raft_term # promotions[j].raft_term

\* Journal length must not exceed expected maximum
JournalLengthInvariant ==
    \A nid \in NodeIDs:
        Len(Nodes[nid].journal) <= MaxJournalLength

\* Limbo leader can only exist if Raft leader
LimboLeaderInvariant ==
    \A nid \in NodeIDs:
        Nodes[nid].limbo_state = LimboStateLeader =>
        Nodes[nid].raft_state = RaftStateLeader

\* If limbo has a transaction, its origin must match limbo owner
LimboOwnerInvariant ==
    \A nid \in NodeIDs:
        LET node == Nodes[nid]
        IN TxnIsValid(node.limbo) =>
            node.limbo.origin_id = node.limbo_owner

TotalInvariant ==
    /\ DataConsistencyInvariant
    /\ PromotionQueueInvariant
    /\ JournalLengthInvariant
    /\ LimboLeaderInvariant
    /\ LimboOwnerInvariant

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

================================================================================
