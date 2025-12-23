We are going to write a TLA+ specification.

# TLA+ Specification for Tarantool Raft protocol

The spec's goal is to describe and verify a potential implementation of Raft in Tarantool DBMS (https://github.com/tarantool/tarantool/).

The original Raft in Tarantool isn't applicable because of at least these reasons:
- Raft requires to be able to remove non-committed entries from the end of an instance's log.
- Raft allows to retry the previously removed entries. I.e. deliver them again to an instance which previously discarded them.
- Raft has a linear log indexation. Tarantool has a vector clock (vclock). I.e. each instance writes its own sequence of logs.

An implementation-motivated difference also is that in Raft a newly elected leader just becomes a leader as soon as it receives a final vote. But in Tarantool there is an extra step to bring this leader into power of being able to write transactions - a special journal entry PROMOTE.

Another implementation-motivated difference is that in Tarantool's Raft a newly elected leader will wait for a quorum (N/2 + 1) of replicas to catch up with itself before it will write PROMOTE. This way we try to guarantee that if any txns in older terms did have a quorum, then the new leader will see them. Which in turn should help us to prevent the situation when same txns might be delivered, removed, and then delivered again on some replicas from different leaders in different terms.

The existing implementation of Raft in Tarantool suffers from a bug that a newly elected Raft leader is committing pending transactions from the previous terms right after winning elections and writing that PROMOTE entry. Which in turn means the new leader didn't actually collect a new quorum after becoming the leader. Which in turn is necessary in Raft, or otherwise there will be conflicting situations when the same txn might get confirmed and rolled back on different instances, leading to a split-brain. This rule is explicitly required by the original Raft.

The algorithm in this spec below is a new version of what is to be implemented in Tarantool. It still extends Raft, but adds more extra steps. The main one - Tarantool after writing PROMOTE won't anymore immediately commit the transactions from the previous terms. Instead, it will collect a quorum on its current journal, then write PROMOTE, then collect a quorum on that PROMOTE, and then write CONFIRM for that PROMOTE and commit or rollback the txns from the previous terms. Thus doing what the original Raft requires - making a new leader commit older term txns only after confirming something (the PROMOTE entry) in a newer term. PROMOTE here, in a way, plays the role of a "first transaction" in a new term on a new leader.

This last paragraph about a new addition to the protocol is the main thing that we want to validate to be correct. In addition to validation of the entire algorithm, of course.

## Implementation rules

For reference one can access the original Raft spec - https://github.com/ongardie/raft.tla/blob/master/raft.tla.
For looking how to make TLA+ code look more like real code it is required to adopt the style from https://github.com/Gerold103/tla/blob/master/TaskScheduler.tla.

On the point of code style. In TLA+ specs (including the original Raft spec) it is often done that attributes of objects are stored as "arrays" or "lists" and each object is represented by an index. To find all attributes of that object one has to lookup attributes in multiple arrays by that index. For example, if there is an object "log entry" and it has an LSN, a type, and a term, then usual TLA+ spec would store logs in 3 arrays like `logLSN == {...}`, `logTerms == {...}`, `logType = {...}`. And to create a new log entry one has to put a record into each of these 3 arrays. Which is very inconvenient and unnatural. It MUST NOT BE DONE LIKE THIS.

Instead, it is required to represent the objects in the system (the instances, the log entries, etc) as actual objects or "functions" (in TLA terms). Returning to the example of log entries - we could much easier represent them like:
```
LogEntryNew == [
	type |-> ...,
	lsn |-> ...,
	term |-> ...,
]
```
And then have a list of `logEntries = {...}` where we would put the results of `LogEntryNew` invocations.

Same with other non-trivial objects like instances and their states. On the other hand, a list of ids or alike might be possible when unavoidable too.

It is also important to group all the rules of one object together in the spec code. And each rule must consist of 2 parts: conditions to satisfy and actions to do.

For a reference on all these rules and coding style you must use this spec - https://github.com/Gerold103/tla/blob/master/TaskScheduler.tla. Its algorithm is unrelated to our case, but its coding style is exactly what we need.

## Spec

We describe a replicaset. Its size must be configurable in a .cfg file.

The instances are connected over network. Messages can get stuck and get delivered slow.
Each instance is connected to each other instance. So they can send messages to each other in any way.

Each instance has the following states:
- journal log (list);
- raft term (number);
- raft vote (number, can be 0 when not specified and is ignored then);
- raft state (enum);
- limbo state (enum);
- limbo term (number);
- limbo owner (number);
- limbo vclock (dictionary of confirmed log ordinal numbers, contains one entry for every instance);
- limbo promotions (dictionary of pending promotions);
- limbo queue (list of pending transactions);
- data (list of committed transactions);

Lets consider these states of the instance.

### Journal

It contains transactions and persisted updates of some of the states. Instance writes there the following:
- Limbo PROMOTE and CONFIRM entries.
- Transactions.

The journal log is linear. Entries are only added to the end of it. And can be replicated only one by one in the same sequence as they were written.

Each entry in the journal has the following:
- Type: transaction, PROMOTE, CONFIRM.
- The ID of the instance which has created this log entry.
- Ordinal number (LSN) of that entry in the log of the original instance who made it.

Once an entry is created, it will never change. It gets replicated exactly as is. And is appended to the journal logs of the other instances. Log entries are considered equal when their origin ID and LSN pairs match.

Depending on entry type, each entry might contain more data. See on that below.

### Raft

The Raft term, vote, and state. They have the same purpose as in vanilla Raft. We can assume these states are automatically "persistent" and we don't need to write them into the journal log. Since we are not trying to validate the correctness of Raft elections here. Tarantool uses the vanilla algorithm for this anyway.

The term can only grow. The vote gets reset to null when term is bumped. The state we consider "not persistent" according to Raft. But since we can't formally make an instance restart, we could express the state volatility as it being able to randomly get dropped into the follower state even if it was the leader or candidate right now.

When any update happens to the Raft state, this instance will send this state to all the other instances over the network. Bypassing the journal order.

The other instances will do what the original Raft says. Like same voting rules, term bumps, etc.

### Limbo

In Tarantool the leader elections and transaction processing are done by 2 systems, not one. The leader election is pretty much vanilla Raft. The transaction processing is done by a module called Limbo. When a leader gets elected, the limbo of the leader will notice that and will do the following steps. Checking if the term didn't change and this instance is still the Raft leader:
- Wait until at least a quorum of replicas (including this one) has all the same journal entries as this instance.
- Write PROMOTE to the journal and save it in the pending promotions dictionary.
- Wait until at least a quorum of replicas (including this one) has this PROMOTE received into their journals.
- Write CONFIRM to the journal. The transaction in the limbo queue, if there is one, is committed (appears in `data`) and removed from the limbo queue. The limbo owner is changed to the ID of this instance. There can't be more than one transaction in the queue at this moment. Otherwise this is an error.

The PROMOTE entry contains (in addition to what all the journal entries contain):
- The Raft term.
- The previous limbo owner.
- Confirmation LSN. It is set as follows:
- - If there are any older pending promotions, it is set to confirmation LSN of the oldest one.
- - Otherwise if the limbo queue isn't empty, it is set to the LSN of the transaction in the queue.
- - Otherwise it is set to limbo_vclock[limbo_owner].
- Confirmed vclock. It is set as follows:
- - If there are any older pending promotions, it is set to confirmed vclock of the first one.
- - Otherwise it is set as the limbo vclock.
- - In both cases the confirmed_vclock[limbo_owner] is set to confirmation LSN explained above.

The CONFIRM on PROMOTE entry contains (in addition to what all the journal entries contain):
- The latest confirmed limbo owner ID.
- Same LSN as the PROMOTE.

Writing to the journal can be considered to happen instantly. Commit of transactions also.

The limbo state is either 'leader' or 'replica'. It becomes 'leader' when Raft state is 'leader', Raft term = limbo term, limbo owner = instance ID. Otherwise the limbo's state is 'replica'. Only when the limbo's state is leader, this instance can create new transactions.

The limbo state is as volatile as the Raft state. So when an instance "restarts", the limbo state is also dropped to 'replica'. Which means that an instance can technically be the limbo owner and have its limbo term = Raft term, but still have its limbo state 'replica'.

Newly created transactions instantly get written into the journal, are added to the limbo queue, and then will be eventually replicated to all the instances. The replication rules see in one of the following sections.

The transaction log entries contain (in addition to what all the journal entries contain):
- The limbo term known when the transaction was created by the limbo owner-leader.

Once the limbo leader instance sees that it has a transaction in the limbo queue, which also got replicated on a quorum of instances (including this one), it writes CONFIRM into the journal and marks the limbo transaction as committed (appends it to the `data` and removes from the limbo queue).

The CONFIRM on transaction contains (in addition to what all the journal entries contain):
- The latest confirmed limbo owner ID.
- LSN of the confirmed transaction.

Every CONFIRM has, as explained above, the limbo owner ID which was known when that entry was created, and an LSN. When CONFIRM is applied, it will increase the limbo's vclock[confirm-owner-ID] counter to the given LSN.

The limbo promotions is a dictionary. It contains for every instance ID either its latest known pending PROMOTE entry, or an invalid entry. All valid pending promotions in this dictionary have unique terms. This must be validated with an assertion.

When an instance creates a new PROMOTE entry, it is not only written to the journal, but is also inserted into the promotion queue.

The logic of PROMOTE application is based on the idea of treating the promotions as transactions. When a PROMOTE is confirmed, it is like this and all the previous promotions known to this instance in the promotions dictionary get 'committed' with all their effects applied.

To avoid having to carry inside each promotion all the history of the previously known pending promotions each promotion actually is packed with all that information in a compressed format. The logic is that commit of a promote is a simple thing: bump confirmed vclock, bump last known term, commit/rollback the transactions in the limbo queue, bump the owner. It can be compressed into a package whose size only depends on the cluster size and not on how many promotions were actually pending:
- The final owner is always from the last confirmed promotion, so we store just one origin_id in each promote. No need to keep the previous ones.
- The transactions in the limbo queue get all committed and rolled back by the first pending promote and its confirm_lsn. So we store just the first confirm_lsn for a whole "chain" of promotions.
- The confirmation LSNs of the non-first confirmed promotions are packed into the confirmed_vclock field.
- The Raft term is enough to take from the last promote. The previous ones are all smaller anyway.

This is going to be O(InstanceCount) size. Even if there were 1000 more pending promotions done one after another until finally one is confirmed.

If a PROMOTE got confirmed and the limbo queue had a transaction (there can be max 1 in this spec) which is covered by this PROMOTE's confirm-lsn, then it is committed. Otherwise this transaction is rolled back.

### Data

Data contains a sequence of committed transactions. Each transaction is basically its log entry. In real world they contain data also, but here we don't care about that. The sequence's order matters. Once a transaction is committed, it is added to the end of the data list and remains there forever. We will use that to compare in the end that all instances have exactly the same sequence of transactions in their data. Note, that the journal logs might still be a bit mixed and this is ok. Most important is that the committed transaction list will be the same.

### Replication

Each instance is connected to each instance. A full mesh of pairs. An instance A sends to instance B messages via a single channel. Never in parallel. So the order can't get mixed between each specific pair of instances. But it might easily happen that A replicates something to B, and then B replicates it to C, for example.

The connection is used for sending:
- Raft messages.
- Journal entries.

An instance A will send its log entries to instance B as long as it sees that A has any log entries not yet present on B. They will be sent one by one in the same order as A has them in its journal.

For simplicity, we can assume that if B already got A's journal entry via some third node, then A knows about that instantly and won't send that row to B second time.

When an instance receives a journal entry, it is guaranteed to be a new one. We never send duplicates, for simplicity. Then the following happens depending on the entry type.

#### For received PROMOTE entry.
If the entry's term < limbo's term, then the entry is written to the journal, but nothing happens. It is basically ignored.
If the entry's term == limbo's term, then we instantly must fail the validation with an error. It is not supposed to happen. Use assertion for that.
If the entry's term > limbo's term, save it into the pending promotions dictionary by the origin ID and make the limbo state set to "replica".

#### For received CONFIRM entry.
CONFIRM is checked if it tries to confirm anything new by looking at its limbo owner ID, its LSN, and the vclock of the local limbo. If it is not confirming anything new, then it is written to the journal and nothing happens. It is basically ignored.

If CONFIRM tries to bump some component in the limbo vclock, then we must do more checks.

First, if there is a pending PROMOTE from the instance which made this CONFIRM. If yes, then we consider this PROMOTE applied and remove this and all the older pending promotes from the pending promotions dictionary (by looking at their raft terms). The confirmed promote gets applied same as it was applied on the instance that created this CONFIRM. The only difference is that there might be still some pending promotions left with an even bigger term than the confirmed one. Those will stay in the promotions dictionary. The CONFIRM gets written into the journal.

If the CONFIRM isn't for a pending PROMOTE, then we check if its limbo owner ID matches the current limbo owner ID. If yes, then we apply it (bump limbo vclock, commit the pending transaction (there must be one transaction, if we got a confirm for it)).

Otherwise the CONFIRM is trying to confirm some new data while actually not owning the limbo. We treat this as an error and abort everything.

#### For received transaction entry.
If its origin matches the limbo owner ID, then we add it to the journal and to the limbo queue.
If its origin is not the limbo owner, and its term < limbo term, then we write it to the journal and do nothing else. Essentially ignoring it.
Otherwise it means that there is some instance trying to create new transactions while having no right to do that. We treat this as an error and abort everything.

### Goal, restrictions, relaxations

We want our spec to have a configurable number nodes and number of transactions to do. The spec must create the given number of instances and make them try to execute these transactions. So they must elect a leader, which will try to execute these transactions until another leader steps in for some reason, and so on.

For simplicity and reduction of the number of states we should make each leader create at most one (1 or 0) transaction per term. The transaction can be created at any random moment as long as this instance remains a leader. Not necessarily right after confirmed promotion (which means in some terms we might have no transactions at all). And then another term somehow starts by any instance in the cluster.

Once no new transactions can be created, we must stop random term bumps and leader stepdowns. This can be checked by having a global transaction counter which is incremented on each transaction start globally in the cluster, and stopping when it reached the configured transaction count. And then wait until all pending transactions are over and all terms on all instances match. This is the terminal condition.

To simulate instances being down we must do the following: an instance might suddenly become a replica without anything changing (limbo and raft states become 'replica').

To simulate leader health issues ("lost connectivity" to the replicas, for example) we must allow any replica to suddenly bump its Raft term + 1 to start new elections.

The network model can be kept simple. We assume that the instances are able to detect duplicate entries. Sending of a message might be delayed indefinitely. But once it is sent, it is also instantly delivered.

The initial state of the system:
- Every node is a replica.
- All terms are 1.
- Limbo owner ID is a constant from the config.
- The journal log, data, limbo queue, limbo promotions are empty.
- The limbo vclock contains -1 for all components.
- All instances are already in the cluster, we are not testing topology changes.
- The journal's ordinal numbers start with 1 on each instance.

In this state the system can't do transactions though, so naturally we expect, if all rules are correct, the system will elect a new leader and will start doing transactions. This also means that the first PROMOTE will contain zero LSN.

While the system is running, we must keep an invariant true, that for every 2 nodes in the cluster their `data` are either identical or one is prefix of another.

To protect the system from never being able to start new transactions due to constant term bumps we must add a limitation somehow that eventually the system will elect a leader and a leader will eventually start a new transaction. Weak fairness is probably be enough, if it helps to prevent infinite term bumps with no other progress.

## End

The spec might be incomplete or can be missing things. Be critical. Do not blindly rush to execution and don't assume things that aren't 100% known. Prior to implementation explain the task back to me and ask questions in case something needs clarification. Do not be agreeable with everything. Be attentive and critical.

Only start implementation once everything is clear.

It is again important to refer to these sources:
- A perfect example of a spec regarding code style: https://github.com/Gerold103/tla/blob/master/TaskScheduler.tla.
- Spec of the original Raft: https://github.com/ongardie/raft.tla/blob/master/raft.tla
- Tarantool's current implementation where you can find `txn_limbo.c` and `txn_limbo.h` and `raft.h` and `raft.c` to see what states we have.
