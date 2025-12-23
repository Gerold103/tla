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

\* Maximum number of transactions to create globally
CONSTANT MaxTransactions

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
CONSTANT RaftStateCandidate
CONSTANT RaftStateLeader

\* Limbo states
CONSTANT LimboStateReplica
CONSTANT LimboStateLeader

\* Symmetry - all nodes are equivalent
Perms == Permutations(NodeIDs)

\* Maximum expected journal length per node
MaxJournalLength == (MaxTerm * 2 + MaxTransactions * 2) * Cardinality(NodeIDs)

--------------------------------------------------------------------------------
\*
\* Variables
\*

\* Per-node state
VARIABLE Nodes

\* Global counter of created transactions
VARIABLE GlobalTxnCount

vars == <<Nodes, GlobalTxnCount>>

--------------------------------------------------------------------------------
\*
\* Helper functions for object field manipulation
\*

\* Single field setters
SetRaftTerm(v, s) == [s EXCEPT !.raft_term = v]
SetRaftVote(v, s) == [s EXCEPT !.raft_vote = v]
SetRaftState(v, s) == [s EXCEPT !.raft_state = v]
SetLimboState(v, s) == [s EXCEPT !.limbo_state = v]
SetLimboTerm(v, s) == [s EXCEPT !.limbo_term = v]
SetLimboOwner(v, s) == [s EXCEPT !.limbo_owner = v]
SetLimboVclock(v, s) == [s EXCEPT !.limbo_vclock = v]
SetLimboPromotions(v, s) == [s EXCEPT !.limbo_promotions = v]
SetLimboQueue(v, s) == [s EXCEPT !.limbo_queue = v]
SetData(v, s) == [s EXCEPT !.data = v]
SetNextLSN(v, s) == [s EXCEPT !.next_lsn = v]

\* Array operations
ArrLen(s) == Len(s)
ArrLast(s) == s[Len(s)]
ArrIsEmpty(s) == Len(s) = 0
ArrAppend(v, s) == Append(s, v)

\* Node setters
NodeJournalAppend(nid, entry) == [Nodes EXCEPT ![nid].journal = Append(Nodes[nid].journal, entry)]
NodeSetRaftTerm(nid, v, nodes) == [nodes EXCEPT ![nid] = SetRaftTerm(v, nodes[nid])]
NodeSetRaftVote(nid, v, nodes) == [nodes EXCEPT ![nid] = SetRaftVote(v, nodes[nid])]
NodeSetRaftState(nid, v, nodes) == [nodes EXCEPT ![nid] = SetRaftState(v, nodes[nid])]
NodeSetLimboState(nid, v, nodes) == [nodes EXCEPT ![nid] = SetLimboState(v, nodes[nid])]
NodeSetLimboTerm(nid, v, nodes) == [nodes EXCEPT ![nid] = SetLimboTerm(v, nodes[nid])]
NodeSetLimboOwner(nid, v, nodes) == [nodes EXCEPT ![nid] = SetLimboOwner(v, nodes[nid])]
NodeSetLimboVclock(nid, v, nodes) == [nodes EXCEPT ![nid] = SetLimboVclock(v, nodes[nid])]
NodeSetLimboPromotions(nid, v, nodes) == [nodes EXCEPT ![nid] = SetLimboPromotions(v, nodes[nid])]
NodeSetLimboQueue(nid, v, nodes) == [nodes EXCEPT ![nid] = SetLimboQueue(v, nodes[nid])]
NodeSetData(nid, v, nodes) == [nodes EXCEPT ![nid] = SetData(v, nodes[nid])]
NodeSetNextLSN(nid, v, nodes) == [nodes EXCEPT ![nid] = SetNextLSN(v, nodes[nid])]

\* Vclock operations
VclockSet(vclock, nid, val) == [vclock EXCEPT ![nid] = val]

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
    \/ GlobalTxnCount >= MaxTransactions

\* Create a new transaction entry
EntryNewTransaction(origin_id, lsn, limbo_term) == [
    type |-> EntryTypeTransaction,
    origin_id |-> origin_id,
    lsn |-> lsn,
    limbo_term |-> limbo_term
]

\* Create a new PROMOTE entry
EntryNewPromote(origin_id, lsn, raft_term, prev_owner, confirm_lsn, confirmed_vclock) == [
    type |-> EntryTypePromote,
    origin_id |-> origin_id,
    lsn |-> lsn,
    raft_term |-> raft_term,
    prev_owner |-> prev_owner,
    confirm_lsn |-> confirm_lsn,
    confirmed_vclock |-> confirmed_vclock
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

\* Check if node has an entry in its journal
HasEntry(node, entry) ==
    \E i \in DOMAIN(node.journal):
        EntriesEqual(node.journal[i], entry)

\* Find a pending PROMOTE by node ID and confirm_lsn
FindPendingPromote(promotions, nid, confirm_lsn) ==
    LET promote == promotions[nid]
    IN IF PromoteIsValid(promote) /\ promote.confirm_lsn = confirm_lsn
       THEN promote
       ELSE PromoteEmpty

\* Get the oldest (smallest term) valid promotion from the dictionary
GetOldestPromotion(promotions) ==
    IF \E nid \in DOMAIN(promotions): PromoteIsValid(promotions[nid])
    THEN LET oldestNid == CHOOSE nid \in DOMAIN(promotions):
                /\ PromoteIsValid(promotions[nid])
                /\ \A otherNid \in DOMAIN(promotions):
                    PromoteIsValid(promotions[otherNid]) =>
                    promotions[nid].raft_term <= promotions[otherNid].raft_term
         IN promotions[oldestNid]
    ELSE PromoteEmpty

\* Get the latest (largest term) valid promotion from the dictionary
GetLatestPromotion(promotions) ==
    IF \E nid \in DOMAIN(promotions): PromoteIsValid(promotions[nid])
    THEN LET latestNid == CHOOSE nid \in DOMAIN(promotions):
                /\ PromoteIsValid(promotions[nid])
                /\ \A otherNid \in DOMAIN(promotions):
                    PromoteIsValid(promotions[otherNid]) =>
                    promotions[nid].raft_term >= promotions[otherNid].raft_term
         IN promotions[latestNid]
    ELSE PromoteEmpty

\* Remove promotions with term <= given term
RemovePromotionsUpToTerm(promotions, term) ==
    [nid \in DOMAIN(promotions) |->
        IF PromoteIsValid(promotions[nid]) /\ promotions[nid].raft_term <= term
        THEN PromoteEmpty
        ELSE promotions[nid]]

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

\* Count nodes that have fully replicated this node's journal and have term <= given term
\* This ensures we only count replicas that haven't moved to a higher term
NodeCountFullReplicas(nid, max_term) ==
    LET node == Nodes[nid]
    IN Cardinality({other_nid \in NodeIDs:
        /\ JournalIsFullyReplicatedTo(node, Nodes[other_nid])
        /\ Nodes[other_nid].raft_term <= max_term})

\* Create new node state
NodeNew == [
    journal |-> <<>>,
    raft_term |-> 1,
    raft_vote |-> 0,
    raft_state |-> RaftStateFollower,
    limbo_state |-> LimboStateReplica,
    limbo_term |-> 1,
    limbo_owner |-> InitialLimboOwner,
    limbo_vclock |-> [i \in NodeIDs |-> -1],
    limbo_promotions |-> [i \in NodeIDs |-> PromoteEmpty],
    limbo_queue |-> <<>>,
    data |-> <<>>,
    next_lsn |-> 1
]

\* Initialize state
Init ==
    /\ Nodes = [nid \in NodeIDs |-> NodeNew]
    /\ GlobalTxnCount = 0

--------------------------------------------------------------------------------
\*
\* Raft election actions
\*

\* Node randomly bumps its term to start an election
NodeBumpTerm(nid) ==
    LET node == Nodes[nid]
    IN
    /\ ~ShouldStop
    /\ node.raft_state = RaftStateFollower \/ node.raft_state = RaftStateCandidate
    \* ---
    /\ Nodes' = NodeSetRaftTerm(nid, node.raft_term + 1,
                    NodeSetRaftVote(nid, nid,
                    NodeSetRaftState(nid, RaftStateCandidate,
                    NodeSetLimboState(nid, LimboStateReplica,
                    Nodes))))
    /\ UNCHANGED<<GlobalTxnCount>>

\* A node grants its vote to a candidate
NodeGrantVote(voter_nid, candidate_nid) ==
    LET voter == Nodes[voter_nid]
        candidate == Nodes[candidate_nid]
    IN
    /\ voter_nid # candidate_nid
    /\ candidate.raft_state = RaftStateCandidate
    /\ candidate.raft_term = voter.raft_term
    /\ voter.raft_vote = 0
    /\ JournalIsFullyReplicatedTo(voter, candidate)
    \* ---
    /\ Nodes' = NodeSetRaftVote(voter_nid, candidate_nid, Nodes)
    /\ UNCHANGED<<GlobalTxnCount>>

\* Node becomes Raft leader after winning election (receiving quorum of votes)
NodeBecomeLeader(nid) ==
    /\ Nodes[nid].raft_state = RaftStateCandidate
    /\ LET term == Nodes[nid].raft_term
       IN Cardinality({voter_nid \in NodeIDs:
              Nodes[voter_nid].raft_vote = nid /\ Nodes[voter_nid].raft_term = term}) >= Quorum
    \* ---
    /\ Nodes' = NodeSetRaftState(nid, RaftStateLeader, Nodes)
    /\ UNCHANGED<<GlobalTxnCount>>

\* Node randomly steps down from leader (simulating crash/restart)
NodeStepDown(nid) ==
    LET node == Nodes[nid]
    IN
    /\ node.raft_state = RaftStateLeader \/ node.limbo_state = LimboStateLeader
    \* ---
    /\ Nodes' = NodeSetRaftState(nid, RaftStateFollower,
                    NodeSetLimboState(nid, LimboStateReplica,
                    Nodes))
    /\ UNCHANGED<<GlobalTxnCount>>

\* Node observes higher term from another node and steps down
NodeObserveHigherTerm(dst_nid, src_nid) ==
    LET src_term == Nodes[src_nid].raft_term
    IN
    /\ src_term > Nodes[dst_nid].raft_term
    \* ---
    /\ Nodes' = NodeSetRaftTerm(dst_nid, src_term,
                    NodeSetRaftVote(dst_nid, 0,
                    NodeSetRaftState(dst_nid, RaftStateFollower,
                    NodeSetLimboState(dst_nid, LimboStateReplica,
                    Nodes))))
    /\ UNCHANGED<<GlobalTxnCount>>

--------------------------------------------------------------------------------
\*
\* Limbo PROMOTE actions
\*

\* Raft leader writes PROMOTE after quorum catches up
LimboWritePromote(nid) ==
    LET node == Nodes[nid]
    IN
    /\ node.raft_state = RaftStateLeader
    /\ node.raft_term > node.limbo_term
    /\ NodeCountFullReplicas(nid, node.raft_term) >= Quorum
    /\ Assert(ArrLen(node.limbo_queue) <= 1,
              "Too many transactions in limbo queue during PROMOTE")
    \* ---
    /\ LET oldest_promote == GetOldestPromotion(node.limbo_promotions)
           latest_promote == GetLatestPromotion(node.limbo_promotions)
           has_pending == PromoteIsValid(oldest_promote)
           \* confirm_lsn: use oldest promote's if exists, otherwise queue/vclock
           confirm_lsn == IF has_pending
                          THEN oldest_promote.confirm_lsn
                          ELSE IF ~ArrIsEmpty(node.limbo_queue)
                               THEN ArrLast(node.limbo_queue).lsn
                               ELSE node.limbo_vclock[node.limbo_owner]
           \* confirmed_vclock: use latest promote's if exists, otherwise limbo vclock
           base_vclock == IF has_pending
                          THEN latest_promote.confirmed_vclock
                          ELSE node.limbo_vclock
           \* Fill our component in the vclock
           confirmed_vclock == VclockSet(base_vclock, node.limbo_owner, confirm_lsn)
           entry == EntryNewPromote(
               nid,
               node.next_lsn,
               node.raft_term,
               node.limbo_owner,
               confirm_lsn,
               confirmed_vclock
           )
           old_promote == node.limbo_promotions[nid]
           new_promotions == [node.limbo_promotions EXCEPT ![nid] = entry]
       IN
       /\ Assert(~PromoteIsValid(old_promote) \/ old_promote.raft_term <= entry.raft_term,
                 "New PROMOTE must have term >= old PROMOTE term")
       /\ Assert(~PromoteIsValid(old_promote) \/ old_promote.lsn < entry.lsn,
                 "New PROMOTE must have LSN > old PROMOTE LSN")
       /\ Nodes' = NodeSetLimboPromotions(nid, new_promotions,
                    NodeSetNextLSN(nid, node.next_lsn + 1,
                    NodeJournalAppend(nid, entry)))
    /\ UNCHANGED<<GlobalTxnCount>>

\* Leader confirms PROMOTE after quorum receives it
LimboConfirmPromote(nid) ==
    LET node == Nodes[nid]
        promote_entry == node.limbo_promotions[nid]
    IN
    /\ node.raft_state = RaftStateLeader
    /\ PromoteIsValid(promote_entry)
    /\ promote_entry.raft_term = node.raft_term
    \* ---
    /\ CountNodesWithEntry(promote_entry, node.raft_term) >= Quorum
    /\ Assert(promote_entry.raft_term > node.limbo_term,
              "Local pending promote's term is always bigger than the last confirmed limbo term")
    /\ Assert(ArrLen(node.limbo_queue) <= 1,
              "Too many transactions in limbo queue during PROMOTE confirm")
    /\ Assert(\A i \in DOMAIN(node.limbo_promotions):
                  ~PromoteIsValid(node.limbo_promotions[i]) \/ node.limbo_promotions[i].raft_term <= node.raft_term,
              "No promotion can have bigger term than current node term")
    /\ LET has_txn == ~ArrIsEmpty(node.limbo_queue)
           txn_entry == IF has_txn THEN ArrLast(node.limbo_queue) ELSE NULL
           \* Commit/rollback transaction based on this PROMOTE's confirm_lsn
           owner_matches == has_txn /\ txn_entry.origin_id = promote_entry.prev_owner
           txn_covered == owner_matches /\ txn_entry.lsn <= promote_entry.confirm_lsn
           should_commit == txn_covered
           confirm_entry == EntryNewConfirm(
               nid,
               node.next_lsn,
               promote_entry.prev_owner,
               promote_entry.confirm_lsn
           )
           new_data == IF should_commit THEN ArrAppend(txn_entry, node.data) ELSE node.data
           \* Clear all promotions (local confirmation)
           new_promotions == [i \in NodeIDs |-> PromoteEmpty]
       IN
       /\ Assert(\A i \in NodeIDs:
                   promote_entry.confirmed_vclock[i] >= node.limbo_vclock[i],
                 "PROMOTE's confirmed_vclock must be >= limbo vclock")
       /\ Nodes' = NodeSetLimboTerm(nid, promote_entry.raft_term,
                    NodeSetLimboOwner(nid, nid,
                    NodeSetLimboVclock(nid, promote_entry.confirmed_vclock,
                    NodeSetLimboPromotions(nid, new_promotions,
                    NodeSetLimboQueue(nid, <<>>,
                    NodeSetData(nid, new_data,
                    NodeSetNextLSN(nid, node.next_lsn + 1,
                    NodeSetLimboState(nid, LimboStateLeader,
                    NodeJournalAppend(nid, confirm_entry)))))))))
    /\ UNCHANGED<<GlobalTxnCount>>

--------------------------------------------------------------------------------
\*
\* Limbo transaction actions
\*

\* Limbo leader creates a new transaction
LimboCreateTransaction(nid) ==
    LET node == Nodes[nid]
        entry == EntryNewTransaction(nid, node.next_lsn, node.limbo_term)
    IN
    /\ GlobalTxnCount < MaxTransactions
    /\ node.limbo_state = LimboStateLeader
    /\ ArrIsEmpty(node.limbo_queue)
    \* ---
    /\ GlobalTxnCount' = GlobalTxnCount + 1
    /\ Nodes' = NodeSetLimboQueue(nid, ArrAppend(entry, node.limbo_queue),
                    NodeSetNextLSN(nid, node.next_lsn + 1,
                    NodeJournalAppend(nid, entry)))

\* Limbo leader confirms transaction after quorum receives it
LimboConfirmTransaction(nid) ==
    LET node == Nodes[nid]
    IN
    /\ node.limbo_state = LimboStateLeader
    /\ ~ArrIsEmpty(node.limbo_queue)
    \* ---
    /\ LET txn_entry == ArrLast(node.limbo_queue)
       IN
       /\ CountNodesWithEntry(txn_entry, node.raft_term) >= Quorum
       /\ LET confirm_entry == EntryNewConfirm(
                  nid,
                  node.next_lsn,
                  nid,
                  txn_entry.lsn
              )
              old_vclock_lsn == node.limbo_vclock[nid]
              new_vclock == VclockSet(node.limbo_vclock, nid, txn_entry.lsn)
          IN
          /\ Assert(txn_entry.lsn >= old_vclock_lsn,
                    "Vclock LSN must not decrease")
          /\ Nodes' = NodeSetLimboQueue(nid, <<>>,
                       NodeSetLimboVclock(nid, new_vclock,
                       NodeSetData(nid, ArrAppend(txn_entry, node.data),
                       NodeSetNextLSN(nid, node.next_lsn + 1,
                       NodeJournalAppend(nid, confirm_entry)))))
    /\ UNCHANGED<<GlobalTxnCount>>

--------------------------------------------------------------------------------
\*
\* Replication actions
\*

\* Find the next journal entry to replicate (first one not present on destination)
\* Returns 0 if destination has all entries, otherwise returns the index
NextEntryToReplicate(src_node, dst_node) ==
    LET missing == {i \in DOMAIN(src_node.journal): ~HasEntry(dst_node, src_node.journal[i])}
    IN IF missing = {}
       THEN 0
       ELSE CHOOSE i \in missing: \A j \in missing: i <= j

\* Apply a PROMOTE entry to destination node
ReplicatePromote(entry, dst_nid) ==
    LET dst_node == Nodes[dst_nid]
    IN
    /\ IF entry.raft_term <= dst_node.limbo_term
       THEN
           \* Ignore old PROMOTE (already confirmed)
           Nodes' = NodeJournalAppend(dst_nid, entry)
       ELSE
           \* New term PROMOTE - store directly
           LET old_promote == dst_node.limbo_promotions[entry.origin_id]
               new_promotions == [dst_node.limbo_promotions EXCEPT ![entry.origin_id] = entry]
           IN
           /\ Assert(~PromoteIsValid(old_promote) \/ old_promote.raft_term <= entry.raft_term,
                     "New PROMOTE must have term >= old PROMOTE term")
           /\ Assert(~PromoteIsValid(old_promote) \/ old_promote.lsn < entry.lsn,
                     "New PROMOTE must have LSN > old PROMOTE LSN")
           /\ Nodes' = NodeSetLimboState(dst_nid, LimboStateReplica,
                        NodeSetLimboPromotions(dst_nid, new_promotions,
                        NodeJournalAppend(dst_nid, entry)))

\* Apply CONFIRM on PROMOTE entry to destination node
ReplicateConfirmPromote(entry, dst_nid, promote) ==
    LET dst_node == Nodes[dst_nid]
        has_txn == ~ArrIsEmpty(dst_node.limbo_queue)
        txn_entry == IF has_txn THEN ArrLast(dst_node.limbo_queue) ELSE NULL
        \* Commit/rollback transaction based on this PROMOTE's confirm_lsn
        owner_matches == has_txn /\ txn_entry.origin_id = promote.prev_owner
        txn_covered == owner_matches /\ txn_entry.lsn <= promote.confirm_lsn
        should_commit == txn_covered
        \* Always clear queue (commit if covered, rollback if not)
        new_data == IF should_commit THEN ArrAppend(txn_entry, dst_node.data) ELSE dst_node.data
        \* Remove promotions with term <= confirmed promote's term, keep higher ones
        new_promotions == RemovePromotionsUpToTerm(dst_node.limbo_promotions, promote.raft_term)
        \* Change owner to the confirmed PROMOTE's origin
        new_owner == promote.origin_id
    IN
    /\ Assert(ArrLen(dst_node.limbo_queue) <= 1,
             "Too many transactions in queue during PROMOTE confirm")
    /\ Assert(has_txn => txn_entry.origin_id = dst_node.limbo_owner,
             "Transaction origin must match current limbo owner")
    /\ Assert(entry.confirm_lsn = promote.confirm_lsn,
             "CONFIRM lsn must match pending PROMOTE confirm_lsn")
    /\ Assert(\A i \in NodeIDs:
                promote.confirmed_vclock[i] >= dst_node.limbo_vclock[i],
              "PROMOTE's confirmed_vclock must be >= limbo vclock")
    /\ Nodes' = NodeSetLimboTerm(dst_nid, promote.raft_term,
                    NodeSetLimboOwner(dst_nid, new_owner,
                    NodeSetLimboVclock(dst_nid, promote.confirmed_vclock,
                    NodeSetLimboPromotions(dst_nid, new_promotions,
                    NodeSetLimboQueue(dst_nid, <<>>,
                    NodeSetData(dst_nid, new_data,
                    NodeJournalAppend(dst_nid, entry)))))))

\* Apply CONFIRM on transaction entry to destination node
ReplicateConfirmTransaction(entry, dst_nid) ==
    LET dst_node == Nodes[dst_nid]
        new_vclock == VclockSet(dst_node.limbo_vclock, entry.owner_id, entry.confirm_lsn)
        txn_entry == ArrLast(dst_node.limbo_queue)
    IN
    /\ Assert(~ArrIsEmpty(dst_node.limbo_queue),
             "No transaction to confirm")
    /\ Assert(txn_entry.origin_id = entry.owner_id,
             "Transaction origin must match CONFIRM owner")
    /\ Assert(entry.confirm_lsn >= dst_node.limbo_vclock[entry.owner_id],
             "Vclock LSN must not decrease")
    /\ Nodes' = NodeSetLimboVclock(dst_nid, new_vclock,
                    NodeSetLimboQueue(dst_nid, <<>>,
                    NodeSetData(dst_nid, ArrAppend(txn_entry, dst_node.data),
                    NodeJournalAppend(dst_nid, entry))))

\* Apply a CONFIRM entry to destination node
ReplicateConfirm(entry, dst_nid) ==
    LET dst_node == Nodes[dst_nid]
        current_lsn == dst_node.limbo_vclock[entry.owner_id]
        promote == FindPendingPromote(dst_node.limbo_promotions, entry.origin_id, entry.confirm_lsn)
    IN
    IF PromoteIsValid(promote)
    THEN ReplicateConfirmPromote(entry, dst_nid, promote)
    ELSE IF entry.confirm_lsn <= current_lsn
    THEN Nodes' = NodeJournalAppend(dst_nid, entry)
    ELSE IF entry.owner_id = dst_node.limbo_owner
    THEN ReplicateConfirmTransaction(entry, dst_nid)
    ELSE Assert(FALSE, "Invalid CONFIRM from non-owner")

\* Apply a transaction entry to destination node
ReplicateTransaction(entry, dst_nid) ==
    LET dst_node == Nodes[dst_nid]
        is_from_owner == entry.origin_id = dst_node.limbo_owner
        is_old_term == entry.limbo_term < dst_node.limbo_term
    IN
    IF is_from_owner
    THEN
        \* Valid transaction from owner
        Nodes' = NodeSetLimboQueue(dst_nid, ArrAppend(entry, dst_node.limbo_queue),
                     NodeJournalAppend(dst_nid, entry))
    ELSE IF is_old_term
    THEN
        \* Ignore old term transaction
        Nodes' = NodeJournalAppend(dst_nid, entry)
    ELSE
        \* Invalid: transaction from non-owner in current/future term
        Assert(FALSE, "Invalid transaction from non-owner")

\* Main replication action: replicate next entry from src to dst
ReplicateNextEntry(src_nid, dst_nid) ==
    LET src_node == Nodes[src_nid]
        dst_node == Nodes[dst_nid]
        next_idx == NextEntryToReplicate(src_node, dst_node)
    IN
    /\ src_nid # dst_nid
    /\ next_idx # 0
    /\ LET entry == src_node.journal[next_idx]
       IN
       /\ CASE entry.type = EntryTypePromote -> ReplicatePromote(entry, dst_nid)
            [] entry.type = EntryTypeConfirm -> ReplicateConfirm(entry, dst_nid)
            [] entry.type = EntryTypeTransaction -> ReplicateTransaction(entry, dst_nid)
    /\ UNCHANGED<<GlobalTxnCount>>
--------------------------------------------------------------------------------
\*
\* Main specification
\*

Next ==
    \/ \E nid \in NodeIDs: NodeBumpTerm(nid)
    \/ \E voter \in NodeIDs, candidate \in NodeIDs: NodeGrantVote(voter, candidate)
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
            EntriesEqual(data1[i], data2[i])

\* Terminal state: either all transactions done OR max term reached
TerminalProperty == <>[](
    \/ GlobalTxnCount >= MaxTransactions
    \/ \E nid \in NodeIDs: Nodes[nid].raft_term >= MaxTerm
)

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

\* If limbo queue is not empty, transaction origin must match limbo owner
LimboQueueOwnerInvariant ==
    \A nid \in NodeIDs:
        LET node == Nodes[nid]
        IN ~ArrIsEmpty(node.limbo_queue) =>
            ArrLast(node.limbo_queue).origin_id = node.limbo_owner

\* No transaction loss: if a transaction is committed on one node (in data),
\* and exists in another node's journal, then it must be either committed
\* (in data) or pending (in limbo_queue) on that other node
NoTransactionLossInvariant ==
    \A nid1 \in NodeIDs, nid2 \in NodeIDs:
        nid1 # nid2 =>
        LET node1 == Nodes[nid1]
            node2 == Nodes[nid2]
        IN \A i \in DOMAIN(node1.data):
            LET txn == node1.data[i]
            IN HasEntry(node2, txn) =>
                \/ (\E j \in DOMAIN(node2.data): EntriesEqual(node2.data[j], txn))
                \/ (~ArrIsEmpty(node2.limbo_queue) /\ EntriesEqual(ArrLast(node2.limbo_queue), txn))

TotalInvariant ==
    /\ DataConsistencyInvariant
    /\ PromotionQueueInvariant
    /\ JournalLengthInvariant
    /\ LimboLeaderInvariant
    /\ LimboQueueOwnerInvariant
    /\ NoTransactionLossInvariant

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

================================================================================
