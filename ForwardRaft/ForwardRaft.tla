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
\* - Split-brain detection: a node refuses an entry contradicting its state
\*   and stops the replication link it came from. With a majority quorum no
\*   link ever breaks. With a smaller one the forks are inevitable, and the
\*   nodes must end up in consistent groups with all the links between the
\*   groups broken.
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

\* Election and ack quorum. A majority makes any two quorums intersect. A
\* smaller one lets two leaders get elected by disjoint supporters, even in
\* the same term - a fork the protocol can't prevent, and must detect.
CONSTANT Quorum

\* Null value
CONSTANT NULL

\* Entry types
CONSTANT EntryTypeTransaction
CONSTANT EntryTypePromote
CONSTANT EntryTypeConfirm

\* Raft states. A candidate is a node collecting the votes of the term it
\* started; only a candidate counts them. A leader leaving its leadership on
\* its own - fenced, demoted, restarted - is in Tarantool a follower of the
\* same term with its vote still cast, never elected again in that term: it
\* can only observe a higher term or start a new election. Both are available
\* to the leader here directly, so that follower is not a state of its own.
CONSTANT RaftStateFollower
CONSTANT RaftStateCandidate
CONSTANT RaftStateLeader

\* Limbo states
CONSTANT LimboStateReplica
CONSTANT LimboStateLeader

CONSTANT NodeRoleCandidate
CONSTANT NodeRoleVoter

\* Symmetry - all nodes and transactions are equivalent
Perms == Permutations(NodeIDs) \union Permutations(AllTransactions)

\* Maximum expected journal length per node
MaxJournalLength == (MaxTerm * 2 + Cardinality(AllTransactions) * 2) * Cardinality(NodeIDs)

\* The nodes receiving replication.
DataNodes == NodeIDs \ VoterIDs

\* Any two majorities intersect, so the elections and the acks make forks
\* impossible. The checks holding only then are asserted under this guard.
IsMajorityQuorum == 2 * Quorum > Cardinality(NodeIDs)

--------------------------------------------------------------------------------
\*
\* Variables
\*

\* Per-node state
VARIABLE Nodes

\* Remaining transactions to create (set)
VARIABLE TransactionsToDo

vars == <<Nodes, TransactionsToDo>>

--------------------------------------------------------------------------------
\*
\* Helper functions for object field manipulation
\*

\* Single field setters - operate on node objects directly
SetRaftTerm(v, s) == [s EXCEPT !.raft_term = v]
SetRaftState(v, s) == [s EXCEPT !.raft_state = v]
SetRaftVote(v, s) == [s EXCEPT !.raft_vote = v]
SetLimboState(v, s) == [s EXCEPT !.limbo_state = v]
SetLimboTerm(v, s) == [s EXCEPT !.limbo_term = v]
SetLimboOwner(v, s) == [s EXCEPT !.limbo_owner = v]
SetLimboVclock(v, s) == [s EXCEPT !.limbo_vclock = v]
SetLimboTermMap(v, s) == [s EXCEPT !.limbo_term_map = v]
SetLimboPromotions(v, s) == [s EXCEPT !.limbo_promotions = v]
SetLimbo(v, s) == [s EXCEPT !.limbo = v]
SetData(v, s) == [s EXCEPT !.data = v]
SetDataRejected(v, s) == [s EXCEPT !.data_rejected = v]
SetJournal(v, s) == [s EXCEPT !.journal = v]
SetJournalVclock(v, s) == [s EXCEPT !.journal_vclock = v]
SetValidAcks(v, s) == [s EXCEPT !.valid_acks = v]
SetMadeTxn(v, s) == [s EXCEPT !.made_txn = v]
SetAppliers(v, s) == [s EXCEPT !.appliers = v]

\* Array operations
ArrLen(s) == Len(s)
ArrLast(s) == s[Len(s)]
ArrIsEmpty(s) == Len(s) = 0
ArrAppend(v, s) == Append(s, v)
ArrContains(v, s) == \E i \in DOMAIN(s): s[i] = v

\* Update a node in the Nodes dictionary
NodesUpdate(nid, node) == [Nodes EXCEPT ![nid] = node]

\* Vclock operations
VclockSet(vclock, nid, val) == [vclock EXCEPT ![nid] = val]
VclockGE(a, b) == \A i \in NodeIDs: a[i] >= b[i]

\* Rows of one origin are strictly ordered on every delivery path, so the
\* journal rows of each origin are always a prefix of that origin's rows.
\* The journal vclock - the per-origin count of the rows - then says which
\* entries the node has without scanning the journal. The own component is
\* the LSN of the last own row.
\*
\* The append is also the ack: the applier sends the vclock to the origin
\* right after the write, with the Raft term of that moment. The origin
\* counts the ack only if that term is not above the one it wrote the row in
\* - the one it waits in. The verdict is remembered per origin for its latest
\* row, the only one it can be waiting on, so that the ack keeps its term
\* when the node moves on before the origin gets to count it. The origin's
\* term is on a PROMOTE; a txn is written in the term of the owner's applied
\* PROMOTE, which precedes the txn on every delivery path; a CONFIRM is never
\* waited on. The own rows go the same way: the own write is an ack too.
JournalAppend(entry, node) ==
    LET origin == entry.origin_id
        row_term == CASE entry.type = EntryTypePromote -> entry.raft_term
                      [] entry.type = EntryTypeTransaction -> node.limbo_term_map[origin]
                      [] entry.type = EntryTypeConfirm -> 0
        valid_acks == IF node.raft_term <= row_term
                      THEN node.valid_acks \union {origin}
                      ELSE node.valid_acks \ {origin}
    IN
    IF Assert(entry.lsn = node.journal_vclock[origin] + 1,
              "Rows of one origin arrive strictly in order")
    THEN SetJournal(ArrAppend(entry, node.journal),
         SetJournalVclock(VclockSet(node.journal_vclock, origin, entry.lsn),
         SetValidAcks(valid_acks,
         node)))
    ELSE node

\* The LSN for the next own row.
NextLSN(nid, node) == node.journal_vclock[nid] + 1

\* Transaction fate tracking. Each node decides for itself, exactly once per
\* transaction: a commit appends it to the data, a rollback puts it into the
\* rejected set. Two nodes can disagree only when the replication between
\* them is broken.
TxnIsDecided(txn_data, node) ==
    \/ ArrContains(txn_data, node.data)
    \/ txn_data \in node.data_rejected

SetTxnCommitted(txn_data, node) ==
    IF Assert(~TxnIsDecided(txn_data, node), "A transaction is decided once")
    THEN SetData(ArrAppend(txn_data, node.data), node)
    ELSE node

SetTxnRejected(txn_data, node) ==
    IF Assert(~TxnIsDecided(txn_data, node), "A transaction is decided once")
    THEN SetDataRejected(node.data_rejected \union {txn_data}, node)
    ELSE node

--------------------------------------------------------------------------------
\*
\* Constructors and helpers
\*

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

\* A term hosts at most one PROMOTE. The filters refuse a term taken by
\* another origin, so no two pending promotions ever share a term.
PromotionsSet(nid, promote, promotions) ==
    IF Assert(\A other \in NodeIDs \ {nid}:
                  ~PromoteIsValid(promotions[other]) \/
                  promotions[other].raft_term # promote.raft_term,
              "No two pending promotions share a term")
    THEN [promotions EXCEPT ![nid] = promote]
    ELSE promotions
PromotionsFindPending(nid, confirm_lsn, promotions) ==
    LET promote == promotions[nid]
    IN IF PromoteIsValid(promote) /\ promote.confirm_lsn = confirm_lsn
       THEN promote
       ELSE PromoteEmpty

\* Drop the pending promotions covered by the applied terms: their origin's
\* applied term reached them, meaning the applied promotion was chained from
\* them, or superseded them from the same origin. The others stay, even when
\* they can't get confirmed anymore - their CONFIRM has to be recognized.
PromotionsRemoveCovered(term_map, promotions) ==
    [nid \in DOMAIN(promotions) |->
        IF PromoteIsValid(promotions[nid]) /\ promotions[nid].raft_term <= term_map[nid]
        THEN PromoteEmpty
        ELSE promotions[nid]]

\* Check if node has an entry in its journal
HasEntry(node, entry) ==
    entry.lsn <= node.journal_vclock[entry.origin_id]

\* The acks for an entry which its origin can count: the nodes having the
\* entry, whose ack carried a term not above the origin's. An ack with a
\* higher term never counts - the relay processes the term first and the
\* origin steps down (relay.cc tx_status_update). The term is the one the
\* node had when it appended the entry, not its current one, see
\* JournalAppend: the ack can be in flight while the node moves to a higher
\* term, and the origin still counts it on arrival. The entry is the origin's
\* latest row - it writes nothing else while waiting - and the origin's own
\* write is always among the acks.
CountAcksForEntry(entry) ==
    LET origin == entry.origin_id
    IN
    IF Assert(origin \in Nodes[origin].valid_acks,
              "The origin's own write of the entry is an ack")
    THEN Cardinality({nid \in NodeIDs:
             /\ HasEntry(Nodes[nid], entry)
             /\ origin \in Nodes[nid].valid_acks})
    ELSE 0

\* Check if all journal entries from 'from' node are present in 'to' node
JournalIsFullyReplicatedTo(from, to) ==
    VclockGE(to.journal_vclock, from.journal_vclock)

\* Replication link operations. The link src -> dst is the applier of dst
\* receiving from src.
LinkIsOpenFromTo(src, dst) == src \in Nodes[dst].appliers

\* Create new node state
NodeNew(nid) == [
    role |-> IF nid \in VoterIDs THEN NodeRoleVoter ELSE NodeRoleCandidate,
    \* The nodes this one receives from. A voter receives no rows, but its
    \* links still carry the terms and the vote requests.
    appliers |-> NodeIDs \ {nid},
    journal |-> <<>>,
    raft_term |-> 1,
    raft_state |-> RaftStateFollower,
    \* The node voted for in the current term, NULL when didn't vote yet. The
    \* votes are not journal entries - they are Raft messages, observed by the
    \* peers over the replication links.
    raft_vote |-> NULL,
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
    \* The committed transactions, in the commit order.
    data |-> <<>>,
    \* The rolled back transactions. Their order is node-local: a transaction
    \* is rolled back either on receipt or when the queue is cleared, and
    \* nothing across nodes depends on which.
    data_rejected |-> {},
    \* The count of the journal rows of each origin.
    journal_vclock |-> [i \in NodeIDs |-> 0],
    \* The origins whose latest row this node acked with a term not above
    \* the row's own, see JournalAppend.
    valid_acks |-> {},
    \* Whether the node created a transaction since it was elected. A node
    \* creates at most one transaction per term - a state space reduction.
    made_txn |-> FALSE
]

\* Initialize state
Init ==
    /\ Nodes = [nid \in NodeIDs |-> NodeNew(nid)]
    /\ TransactionsToDo = AllTransactions

--------------------------------------------------------------------------------
\*
\* Raft election actions
\*

\* Node randomly bumps its term to start an election, voting for itself and
\* becoming a candidate. A candidate does it too - its round timed out
\* without a quorum. So does a leader - this is how it leaves its leadership
\* on its own, see the Raft states.
NodeBumpTerm(nid) ==
    LET node == Nodes[nid]
    IN
    /\ node.raft_term < MaxTerm
    /\ node.role = NodeRoleCandidate
    \* ---
    /\ Nodes' = NodesUpdate(nid,
                SetRaftTerm(node.raft_term + 1,
                SetRaftVote(nid,
                SetRaftState(RaftStateCandidate,
                SetLimboState(LimboStateReplica,
                node)))))
    /\ UNCHANGED TransactionsToDo

\* Node votes for a candidate of its term, once per term. The candidate's
\* journal must contain everything the voter has. The vote request is a
\* Raft message coming over the candidate's replication link.
\*
\* With quorum 1 the self-vote is the quorum: the other votes are never
\* counted, and the only thing a vote does to the voter is forbid its own
\* election in that term - which it may equally just not attempt. So the
\* votes are not even cast then, a state space reduction.
NodeVote(voter_nid, cand_nid) ==
    LET voter == Nodes[voter_nid]
        cand == Nodes[cand_nid]
    IN
    /\ Quorum > 1
    /\ voter_nid # cand_nid
    /\ voter.raft_term = cand.raft_term
    /\ voter.raft_vote = NULL
    /\ cand.raft_state = RaftStateCandidate
    /\ Assert(cand.raft_vote = cand_nid, "A candidate has voted for itself")
    /\ JournalIsFullyReplicatedTo(voter, cand)
    /\ LinkIsOpenFromTo(cand_nid, voter_nid)
    \* ---
    /\ Nodes' = NodesUpdate(voter_nid, SetRaftVote(cand_nid, voter))
    /\ UNCHANGED TransactionsToDo

\* Node becomes Raft leader after having a quorum of votes: its own one and
\* the Raft messages coming over the voters' replication links.
NodeBecomeLeader(nid) ==
    LET node == Nodes[nid]
        term == node.raft_term
    IN
    /\ node.raft_state = RaftStateCandidate
    /\ Assert(node.role = NodeRoleCandidate, "A voter is never a candidate")
    /\ Assert(node.raft_vote = nid, "A candidate has voted for itself")
    /\ Cardinality({other \in NodeIDs:
            /\ Nodes[other].raft_term = term
            /\ Nodes[other].raft_vote = nid
            /\ other = nid \/ LinkIsOpenFromTo(other, nid)}) >= Quorum
    \* ---
    /\ Nodes' = NodesUpdate(nid,
                SetRaftState(RaftStateLeader,
                SetMadeTxn(FALSE,
                node)))
    /\ UNCHANGED TransactionsToDo

\* Node observes higher term from another node and steps down. The vote is
\* reset - it is per term. The terms travel both with the entries and with
\* the acks, so one open link in any direction is enough.
NodeObserveHigherTerm(dst_nid, src_nid) ==
    LET dst_node == Nodes[dst_nid]
        src_term == Nodes[src_nid].raft_term
    IN
    /\ src_nid # dst_nid
    /\ src_term > dst_node.raft_term
    /\ LinkIsOpenFromTo(src_nid, dst_nid) \/ LinkIsOpenFromTo(dst_nid, src_nid)
    \* ---
    /\ Nodes' = NodesUpdate(dst_nid,
                SetRaftTerm(src_term,
                SetRaftVote(NULL,
                SetRaftState(RaftStateFollower,
                SetLimboState(LimboStateReplica,
                dst_node)))))
    /\ UNCHANGED TransactionsToDo

--------------------------------------------------------------------------------
\*
\* Limbo PROMOTE actions
\*

\* A pending PROMOTE is poisoned when no CONFIRM can apply it on this node:
\* the limbo moved past its term without it, or an applied PROMOTE carries a
\* term of some node which the entry's author didn't know. It appears in any
\* cluster, when a leader loses the leadership before its PROMOTE reaches
\* anybody. With a majority quorum it never gets confirmed - a confirmed
\* PROMOTE is known to every later leader. With a smaller quorum it can, by a
\* leader elected without intersecting the quorum which confirmed the older
\* PROMOTE. That is a fork, and its CONFIRM is refused.
PromoteIsPoisoned(node, promote) ==
    \/ promote.raft_term <= node.limbo_term
    \/ ~VclockGE(promote.term_map, node.limbo_term_map)

\* The filter of a CONFIRM applying a pending PROMOTE, own or received. A
\* poisoned one is a fork. So is one confirming less than what is already
\* confirmed here. With a majority quorum a pending PROMOTE of the leader
\* always passes - nothing gets confirmed behind the leader's back.
PromoteCanBeConfirmed(node, promote) ==
    /\ ~PromoteIsPoisoned(node, promote)
    /\ VclockGE(promote.confirmed_vclock, node.limbo_vclock)

\* The filter of a PROMOTE entering the journal, own or received. A term
\* hosts at most one PROMOTE - one re-using a term the node knows as taken by
\* another origin, applied or pending, is a second leader elected in the same
\* term.
PromoteCanBeWritten(node, term, origin) ==
    \A nid \in NodeIDs \ {origin}:
        /\ node.limbo_term_map[nid] # term
        /\ PromoteIsValid(node.limbo_promotions[nid]) =>
           node.limbo_promotions[nid].raft_term # term

\* The latest pending promotion which still can get confirmed here.
PromotionsGetLatestLive(node) ==
    LET promotions == node.limbo_promotions
        live == {nid \in DOMAIN(promotions):
                    /\ PromoteIsValid(promotions[nid])
                    /\ ~PromoteIsPoisoned(node, promotions[nid])}
    IN IF live = {}
       THEN PromoteEmpty
       ELSE promotions[CHOOSE nid \in live:
                \A other \in live:
                    promotions[nid].raft_term >= promotions[other].raft_term]

\* Whether the journal has a PROMOTE of the given term from another origin -
\* a second leader elected in the same term.
JournalHasForeignPromoteOfTerm(journal, term, origin) ==
    \E i \in DOMAIN(journal):
        /\ journal[i].type = EntryTypePromote
        /\ journal[i].raft_term = term
        /\ journal[i].origin_id # origin

\* Store a PROMOTE, own or received, as the pending promotion of its origin
\* and in the journal. Rows of one origin are strictly ordered on every
\* delivery path, so a PROMOTE never goes back in its origin's history.
LimboStorePromote(entry, node) ==
    LET origin == entry.origin_id
        old_promote == node.limbo_promotions[origin]
    IN
    IF /\ Assert(PromoteCanBeWritten(node, entry.raft_term, origin),
                 "Only a PROMOTE passing the filter is stored")
       /\ Assert(~PromoteIsValid(old_promote) \/ old_promote.raft_term < entry.raft_term,
                 "New PROMOTE must have term > old PROMOTE term")
       /\ Assert(~PromoteIsValid(old_promote) \/ old_promote.lsn < entry.lsn,
                 "New PROMOTE must have LSN > old PROMOTE LSN")
       /\ Assert(~IsMajorityQuorum \/
                 ~JournalHasForeignPromoteOfTerm(node.journal, entry.raft_term, origin),
                 "A majority quorum elects one leader per term")
    THEN SetLimboPromotions(PromotionsSet(origin, entry, node.limbo_promotions),
         JournalAppend(entry, node))
    ELSE node

\* Apply a pending PROMOTE by its CONFIRM, own or received: decide the
\* queued transaction by the PROMOTE's confirm boundary, move the limbo to
\* the PROMOTE's term, owner and vclocks, drop the covered pending
\* promotions, and journal the CONFIRM.
LimboApplyPromote(promote, confirm_entry, node) ==
    LET has_txn == TxnIsValid(node.limbo)
        txn_entry == node.limbo
        owner_matches == has_txn /\ txn_entry.origin_id = promote.prev_owner
        should_commit == owner_matches /\ txn_entry.lsn <= promote.confirm_lsn
        decided_node == IF ~has_txn THEN node
                        ELSE IF should_commit THEN SetTxnCommitted(txn_entry.data, node)
                        ELSE SetTxnRejected(txn_entry.data, node)
    IN
    IF /\ Assert(PromoteCanBeConfirmed(node, promote),
                 "Only a PROMOTE passing the filter is applied")
       /\ Assert(has_txn => txn_entry.origin_id = node.limbo_owner,
                 "Transaction origin must match current limbo owner")
       /\ Assert(\E i \in NodeIDs: promote.term_map[i] > node.limbo_term_map[i],
                 "PROMOTE's term map must advance at least one component")
    THEN SetLimboTerm(promote.raft_term,
         SetLimboOwner(promote.origin_id,
         SetLimboVclock(promote.confirmed_vclock,
         SetLimboTermMap(promote.term_map,
         SetLimboPromotions(PromotionsRemoveCovered(promote.term_map, node.limbo_promotions),
         SetLimbo(TxnEmpty,
         JournalAppend(confirm_entry, decided_node)))))))
    ELSE node

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
    \* A pending PROMOTE at or above the own term means the elections have
    \* moved on already - the term can overtake the PROMOTE on the way, so the
    \* leader might not know it yet. Chaining from such a PROMOTE would put a
    \* term above the own one into the term map. The promotion is not even
    \* attempted.
    /\ \A other \in NodeIDs:
        PromoteIsValid(node.limbo_promotions[other]) =>
        node.limbo_promotions[other].raft_term < node.raft_term
    \* The own PROMOTE goes through the same filter as the received ones. A
    \* leader elected in a term already taken by another one never claims
    \* the limbo.
    /\ PromoteCanBeWritten(node, node.raft_term, nid)
    \* ---
    \* Chained promotion. An older pending PROMOTE, even one from another
    \* node, can still get confirmed after this new PROMOTE is written. The
    \* new PROMOTE must then lead to the exact same state when its own
    \* CONFIRM is applied. A poisoned one can't get confirmed here, so there
    \* is nothing to stay consistent with - chaining from it would only
    \* inherit the poison.
    /\ LET latest_promote == PromotionsGetLatestLive(node)
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
               NextLSN(nid, node),
               node.raft_term,
               prev_owner,
               confirm_lsn,
               VclockSet(base_vclock, prev_owner, confirm_lsn),
               VclockSet(base_term_map, nid, node.raft_term)
           )
       IN Nodes' = NodesUpdate(nid, LimboStorePromote(entry, node))
    /\ UNCHANGED TransactionsToDo

\* Leader confirms PROMOTE after quorum receives it. The own CONFIRM goes
\* through the same filter as the received ones - it is never written when it
\* would be refused right here.
LimboConfirmPromote(nid) ==
    LET node == Nodes[nid]
        promote_entry == node.limbo_promotions[nid]
    IN
    /\ node.raft_state = RaftStateLeader
    /\ PromoteIsValid(promote_entry)
    /\ promote_entry.raft_term = node.raft_term
    \* The own PROMOTE poisoned by a newer applied promotion is the leader
    \* overtaken before observing the term. By an older one - a fork.
    /\ Assert(\/ ~IsMajorityQuorum
              \/ node.limbo_term > promote_entry.raft_term
              \/ PromoteCanBeConfirmed(node, promote_entry),
              "A majority quorum never confirms behind the leader's back")
    /\ PromoteCanBeConfirmed(node, promote_entry)
    /\ CountAcksForEntry(promote_entry) >= Quorum
    \* ---
    /\ Assert(promote_entry.raft_term > node.limbo_term,
              "Local pending promote's term is always bigger than the last confirmed limbo term")
    /\ LET confirm_entry == EntryNewConfirm(
               nid,
               NextLSN(nid, node),
               promote_entry.prev_owner,
               promote_entry.confirm_lsn
           )
       IN Nodes' = NodesUpdate(nid,
                   SetLimboState(LimboStateLeader,
                   LimboApplyPromote(promote_entry, confirm_entry, node)))
    /\ UNCHANGED TransactionsToDo

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
    /\ ~node.made_txn
    \* ---
    /\ \E txn_data \in TransactionsToDo:
        LET entry == EntryNewTransaction(nid, NextLSN(nid, node), txn_data)
        IN
        /\ TransactionsToDo' = TransactionsToDo \ {txn_data}
        /\ Nodes' = NodesUpdate(nid,
                    SetLimbo(entry,
                    SetMadeTxn(TRUE,
                    JournalAppend(entry, node))))

\* Limbo leader confirms transaction after quorum receives it
LimboConfirmTransaction(nid) ==
    LET node == Nodes[nid]
        txn_entry == node.limbo
    IN
    /\ node.limbo_state = LimboStateLeader
    /\ TxnIsValid(node.limbo)
    /\ CountAcksForEntry(txn_entry) >= Quorum
    \* ---
    /\ LET confirm_entry == EntryNewConfirm(
               nid,
               NextLSN(nid, node),
               nid,
               txn_entry.lsn
           )
       IN
       /\ Assert(txn_entry.lsn >= node.limbo_vclock[nid],
                 "Vclock LSN must not decrease")
       /\ Nodes' = NodesUpdate(nid,
                    SetLimbo(TxnEmpty,
                    SetLimboVclock(VclockSet(node.limbo_vclock, nid, txn_entry.lsn),
                    JournalAppend(confirm_entry,
                    SetTxnCommitted(txn_entry.data, node)))))
    /\ UNCHANGED TransactionsToDo

--------------------------------------------------------------------------------
\*
\* Replication actions
\*

\* Refuse an entry as a split brain. The applier stops and never delivers
\* anything from src again - neither entries nor terms.
LinkCloseFromTo(src, dst) ==
    LET node == Nodes[dst]
    IN
    /\ Assert(~IsMajorityQuorum, "A majority quorum never refuses anything")
    /\ Nodes' = NodesUpdate(dst, SetAppliers(node.appliers \ {src}, node))

\* Find the next journal entry to replicate (first one not present on destination)
\* Returns 0 if destination has all entries, otherwise returns the index
\* TODO: makes sense to make a binary search?
RECURSIVE FirstMissingEntryIdx(_, _, _)
FirstMissingEntryIdx(journal, dst_node, i) ==
    IF i > Len(journal) THEN 0
    ELSE IF ~HasEntry(dst_node, journal[i]) THEN i
    ELSE FirstMissingEntryIdx(journal, dst_node, i + 1)

NextEntryToReplicate(src_node, dst_node) ==
    IF JournalIsFullyReplicatedTo(src_node, dst_node)
    THEN 0
    ELSE FirstMissingEntryIdx(src_node.journal, dst_node, 1)

\* Apply a PROMOTE entry to destination node. It is stored as pending even
\* when poisoned already - an old PROMOTE, superseded before getting
\* confirmed, can show up late through another link, and its CONFIRM must
\* be recognized.
ReplicatePromote(entry, src_nid, dst_nid) ==
    LET dst_node == Nodes[dst_nid]
        origin == entry.origin_id
        \* A newer promotion demotes the limbo leader. An older one, poisoned
        \* on arrival, changes nothing about the leadership.
        new_limbo_state == IF entry.raft_term > dst_node.limbo_term
                           THEN LimboStateReplica
                           ELSE dst_node.limbo_state
    IN
    IF ~PromoteCanBeWritten(dst_node, entry.raft_term, origin)
    THEN LinkCloseFromTo(src_nid, dst_nid)
    ELSE
        \* A chain carrying this PROMOTE's term is always delivered after it,
        \* so it is never covered on arrival.
        /\ Assert(entry.raft_term > dst_node.limbo_term_map[origin],
                  "PROMOTE can't be covered on arrival")
        /\ Nodes' = NodesUpdate(dst_nid,
                     SetLimboState(new_limbo_state,
                     LimboStorePromote(entry, dst_node)))

\* Apply CONFIRM on PROMOTE entry to destination node. The CONFIRM of a
\* PROMOTE not passing the filter is a fork - its author confirmed it without
\* knowing something applied here.
ReplicateConfirmPromote(entry, src_nid, dst_nid, promote) ==
    LET dst_node == Nodes[dst_nid]
    IN
    /\ Assert(entry.confirm_lsn = promote.confirm_lsn,
             "CONFIRM lsn must match pending PROMOTE confirm_lsn")
    /\ IF ~PromoteCanBeConfirmed(dst_node, promote)
       THEN LinkCloseFromTo(src_nid, dst_nid)
       ELSE
           \* The ownership went to the PROMOTE's origin. A limbo leader
           \* which confirmed its own PROMOTE with this newer one pending
           \* is a replica again.
           LET new_node == SetLimboState(LimboStateReplica,
                           LimboApplyPromote(promote, entry, dst_node))
               own_promote == new_node.limbo_promotions[dst_nid]
           IN
           \* A leader's own pending PROMOTE stays confirmable through an
           \* older promotion applied beside it - a majority confirms
           \* nothing behind its back. A newer one is a different thing: the
           \* leader got overtaken, it just hasn't observed the term yet,
           \* the term can travel behind the PROMOTE.
           /\ Assert(\/ ~IsMajorityQuorum
                     \/ new_node.raft_state # RaftStateLeader
                     \/ ~PromoteIsValid(own_promote)
                     \/ promote.raft_term > own_promote.raft_term
                     \/ PromoteCanBeConfirmed(new_node, own_promote),
                     "A majority quorum never confirms behind the leader's back")
           /\ Nodes' = NodesUpdate(dst_nid, new_node)

\* Apply a CONFIRM entry to destination node
ReplicateConfirm(entry, src_nid, dst_nid) ==
    LET dst_node == Nodes[dst_nid]
        current_lsn == dst_node.limbo_vclock[entry.owner_id]
        promote == PromotionsFindPending(entry.origin_id, entry.confirm_lsn, dst_node.limbo_promotions)
        txn_entry == dst_node.limbo
        \* A CONFIRM of the current owner's queued transaction. Anything else
        \* confirming something new is a fork: an old owner still confirming,
        \* or a confirmation of what isn't queued here at all.
        is_txn_confirm ==
            /\ entry.owner_id = dst_node.limbo_owner
            /\ TxnIsValid(txn_entry)
            /\ txn_entry.lsn <= entry.confirm_lsn
    IN
    IF PromoteIsValid(promote)
    THEN ReplicateConfirmPromote(entry, src_nid, dst_nid, promote)
    ELSE IF entry.confirm_lsn <= current_lsn
    THEN Nodes' = NodesUpdate(dst_nid, JournalAppend(entry, dst_node))
    ELSE IF is_txn_confirm
    THEN /\ Assert(txn_entry.origin_id = entry.owner_id,
                   "Transaction origin must match CONFIRM owner")
         /\ Nodes' = NodesUpdate(dst_nid,
                      SetLimboVclock(VclockSet(dst_node.limbo_vclock, entry.owner_id, entry.confirm_lsn),
                      SetLimbo(TxnEmpty,
                      JournalAppend(entry,
                      SetTxnCommitted(txn_entry.data, dst_node)))))
    ELSE LinkCloseFromTo(src_nid, dst_nid)

\* Apply a transaction entry to destination node
ReplicateTransaction(entry, src_nid, dst_nid) ==
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
        \* The owner writes a new transaction only after the previous one is
        \* confirmed, and the CONFIRM precedes it on every delivery path.
        /\ Assert(~TxnIsValid(dst_node.limbo),
                  "The owner's transactions are queued one at a time")
        /\ Nodes' = NodesUpdate(dst_nid,
                     SetLimbo(entry,
                     JournalAppend(entry, dst_node)))
    ELSE IF is_old_term
    THEN
        \* Rollback old term transaction
        Nodes' = NodesUpdate(dst_nid,
                  JournalAppend(entry,
                  SetTxnRejected(entry.data, dst_node)))
    ELSE
        \* A transaction from a non-owner in a current term - its author
        \* thinks it owns the limbo. A fork.
        LinkCloseFromTo(src_nid, dst_nid)

\* Main replication action: the applier of dst applies the next entry from
\* src.
ReplicateNextEntry(src_nid, dst_nid) ==
    LET src_node == Nodes[src_nid]
        dst_node == Nodes[dst_nid]
    IN
    /\ dst_node.role # NodeRoleVoter
    /\ LET next_idx == NextEntryToReplicate(src_node, dst_node) IN
       /\ next_idx # 0
       /\ LET entry == src_node.journal[next_idx] IN
          /\ CASE entry.type = EntryTypePromote -> ReplicatePromote(entry, src_nid, dst_nid)
               [] entry.type = EntryTypeConfirm -> ReplicateConfirm(entry, src_nid, dst_nid)
               [] entry.type = EntryTypeTransaction -> ReplicateTransaction(entry, src_nid, dst_nid)
    /\ UNCHANGED TransactionsToDo
--------------------------------------------------------------------------------
\*
\* Main specification
\*

Next ==
    \/ \E nid \in NodeIDs: NodeBumpTerm(nid)
    \/ \E nid \in NodeIDs, cand \in NodeIDs: NodeVote(nid, cand)
    \/ \E nid \in NodeIDs: NodeBecomeLeader(nid)
    \/ \E src \in NodeIDs, dst \in NodeIDs: NodeObserveHigherTerm(dst, src)
    \/ \E nid \in NodeIDs: LimboWritePromote(nid)
    \/ \E nid \in NodeIDs: LimboConfirmPromote(nid)
    \/ \E nid \in NodeIDs: LimboCreateTransaction(nid)
    \/ \E nid \in NodeIDs: LimboConfirmTransaction(nid)
    \/ \E dst \in NodeIDs: \E src \in Nodes[dst].appliers:
        ReplicateNextEntry(src, dst)

--------------------------------------------------------------------------------
\*
\* Invariants
\*

\* Whether dst has every row src has, whatever the path was.
IsCaughtUp(src, dst) ==
    JournalIsFullyReplicatedTo(Nodes[src], Nodes[dst])

\* Everything a has decided, b has decided the same way: a's commits are a
\* prefix of b's commits, a's rejections are among b's rejections.
TxnDecisionsAreCoveredBy(a, b) ==
    LET na == Nodes[a]
        nb == Nodes[b]
    IN
    /\ Len(na.data) <= Len(nb.data)
    /\ \A i \in DOMAIN(na.data): na.data[i] = nb.data[i]
    /\ na.data_rejected \subseteq nb.data_rejected

\* Every leadership a has confirmed, b has confirmed too, or moved past: each
\* origin's applied term, and the limbo term.
LeadershipIsCoveredBy(a, b) ==
    LET na == Nodes[a]
        nb == Nodes[b]
    IN
    /\ na.limbo_term <= nb.limbo_term
    /\ VclockGE(nb.limbo_term_map, na.limbo_term_map)

\* Consistency over a live link: a divergence can exist only while the row
\* revealing it is in flight. Every decision is made by a journal row, and a
\* refused row is never journaled. So once dst has every row src has, it made
\* every decision src made, the same way, and confirmed every leadership src
\* confirmed. A conflict - a transaction decided differently, a term
\* confirmed for two origins - is always on a row the receiver refuses. With
\* a majority quorum nothing is refused, so this is every pair, always.
CaughtUpConsistencyInvariant ==
    \A a \in DataNodes, b \in DataNodes:
        a # b /\ IsCaughtUp(a, b) =>
            /\ TxnDecisionsAreCoveredBy(a, b)
            /\ LeadershipIsCoveredBy(a, b)

\* Nothing is left to deliver over the open links.
Quiescent ==
    \A src \in DataNodes, dst \in DataNodes:
        src # dst => ~LinkIsOpenFromTo(src, dst) \/ IsCaughtUp(src, dst)

JournalsEqual(a, b) ==
    /\ JournalIsFullyReplicatedTo(Nodes[a], Nodes[b])
    /\ JournalIsFullyReplicatedTo(Nodes[b], Nodes[a])

\* The state derived from the journal, excluding the Raft-dependent parts.
StatesEqual(a, b) ==
    LET na == Nodes[a]
        nb == Nodes[b]
    IN
    /\ na.limbo_term = nb.limbo_term
    /\ na.limbo_owner = nb.limbo_owner
    /\ na.limbo_vclock = nb.limbo_vclock
    /\ na.limbo_term_map = nb.limbo_term_map
    /\ na.limbo_promotions = nb.limbo_promotions
    /\ na.limbo = nb.limbo
    /\ na.data = nb.data
    /\ na.data_rejected = nb.data_rejected

\* When the replication is finished, the nodes still accepting each other's
\* rows have identical journals and states, whatever the delivery order was
\* between them. A majority quorum makes the whole cluster one such group.
\*
\* The detection is not always two-sided. Two leaders of one term (a quorum
\* at or below half) refuse each other's PROMOTE only while their own one for
\* that term is pending. A leader re-elected before its PROMOTE got confirmed
\* chains the new one over it and forgets the old term, so it stores the
\* other leader's PROMOTE as live, and learns of the fork only from that
\* leader's CONFIRM, which poisons its own pending by regression - or never,
\* if that CONFIRM doesn't come, and then it just follows. It confirmed
\* nothing of its own in between, so a one-way link is covered by
\* CaughtUpConsistencyInvariant: the receiver has everything the sender has.
QuiescentInvariant ==
    Quiescent =>
        \A a \in DataNodes, b \in DataNodes:
            a # b /\ LinkIsOpenFromTo(a, b) /\ LinkIsOpenFromTo(b, a) =>
                JournalsEqual(a, b) /\ StatesEqual(a, b)

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

\* A term hosts at most one confirmed PROMOTE: no node holds one applied term
\* for two origins. The filters keep it so - a PROMOTE of a term taken in the
\* map is refused, and a pending PROMOTE at or below the applied limbo term is
\* poisoned, its CONFIRM refused.
LimboTermMapInvariant ==
    \A nid \in NodeIDs:
        LET map == Nodes[nid].limbo_term_map
        IN \A a \in NodeIDs, b \in NodeIDs:
            a # b /\ map[a] > 0 => map[a] # map[b]

TotalInvariant ==
    /\ CaughtUpConsistencyInvariant
    /\ QuiescentInvariant
    /\ JournalLengthInvariant
    /\ LimboLeaderInvariant
    /\ LimboOwnerInvariant
    /\ LimboTermMapInvariant

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

================================================================================
