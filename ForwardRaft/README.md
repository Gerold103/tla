# ForwardRaft - Tarantool synchronous replication with a quorum PROMOTE

A TLA+ model of Tarantool's synchronous replication ("limbo") on top of Raft
elections, written for the redesign in which a new leader's PROMOTE has to
be confirmed by a quorum before it takes effect (the "synchronous promote"
work, Tarantool issue gh-8095). The model is checked with TLC for safety
only. It is meant to be read next to the Tarantool sources: `src/box/txn_limbo.c`
(the limbo), `src/lib/raft/raft.c` and `src/box/raft.c` (elections),
`src/box/relay.cc` and `src/box/applier.cc` (replication). Where the model
makes a choice because of how the code behaves, the comment in the spec says
so and names the function.

## Files

| file | what |
|------|------|
| `ForwardRaft.tla` | the specification, ~1000 lines, heavily commented |
| `ForwardRaftWitness.tla` | reachability witnesses, extends `ForwardRaft` |
| `test.yaml` | the test matrix: configs which must pass, in run order |
| `test_witness.yaml` | the witness matrix: configs which must each reach a scenario |
| `template.cfg` | the TLC config template `gen.py` fills from a matrix entry |
| `gen.py <matrix.yaml> <out dir>` | writes `<out dir>/<name>.cfg` per entry; no defaults |
| `ForwardRaft.cfg` | a hand-written 3-node majority config for a single quick run |
| `../tools/run.py` | runs TLC on a list of configs, see "Running" |
| `../tools/tlatrace.py` | turns a TLC trace into per-step diffs or an action list |

Generated configs and run outputs are runtime files; they go to a dir you
choose (`var/...` here), never into this directory.

## The system

A cluster of nodes replicates a journal. The **data nodes** hold the journal
and the data; the **voters** only take part in elections (Tarantool's
`election_mode = 'voter'`; in the model they receive no rows at all, a
reduction explained below). Every node has an **applier** from every other
node - the replication link `src -> dst` over which `dst` receives `src`'s
journal rows in `src`'s order, and over which `dst`'s acknowledgements
(its vclock) travel back to `src`.

Rows are of three kinds:

- **PROMOTE** - "term T, I am the limbo owner now, the previous owner's
  last confirmed LSN is N". Written by a Raft leader right after the
  election. It carries the owner's confirmed vclock and a **term map**: the
  latest term the author knew for every node when it wrote the row.
- **CONFIRM** - "my rows up to LSN X are confirmed", written by the node
  whose rows they are. The row at X is either the author's transaction or
  the author's own PROMOTE, so a PROMOTE's CONFIRM names the exact row it
  confirms, with one CONFIRM meaning for both kinds. Any decision - a
  transaction committed, a PROMOTE applied - is made by a CONFIRM row;
  nothing is decided without one.
- **transaction** - written only by the limbo owner, one at a time (the next
  one only after the previous one's CONFIRM), one per leadership here.

The **limbo** of a node is what it derives from the rows: the owner, the
owner's term (`limbo_term`), the confirmed vclock, the applied term map, the
**pending** PROMOTEs (one slot per origin: received or own, not yet
confirmed), the queued transaction, the data (committed txns in order) and
the rejected txns. A node is the **limbo leader** when it owns the limbo, is
the Raft leader and its Raft term equals the limbo term - only then it
writes transactions.

A pending PROMOTE is **poisoned** when it can never be confirmed on this
node: its term is at or below the applied limbo term, or its term map is
behind the applied one (its author did not know a confirmed promotion). A
poisoned PROMOTE stays stored: its CONFIRM may still arrive and must be
recognized - and refused. **Chaining**: a new leader with a live pending
PROMOTE writes its own on top of it, inheriting its confirm LSN, vclock and
term map, so both lead to the same state whichever CONFIRM applies.

A node that receives a row contradicting its state **refuses** it: a PROMOTE
of a term it knows as taken by another node, the CONFIRM of a poisoned
PROMOTE, a CONFIRM of something not queued. A refusal closes the link the row
came over (the applier stops with `ER_SPLIT_BRAIN` in Tarantool), for good;
nothing from that source is received again.

The **quorum** is one constant for both elections and confirmations, as
Tarantool's `replication_synchro_quorum`. When it is a majority of the nodes
(`IsMajorityQuorum`), any two quorums intersect and forks are impossible;
the model then asserts that nothing is ever refused and that every
promotion the leader confirms is legitimate. Operators may configure a
smaller quorum; the model then expects forks, and what it checks is that
they are detected: a node that accepted all of another's rows agrees with
it, and two nodes holding the same rows have the same state.

## How the spec is built

`Nodes` is a function from node id to a record; `TransactionsToDo` the
transactions not yet created; `PromotesWritten` a counter. The record's
fields, grouped:

- Raft: `role` (candidate/voter, fixed), `raft_term`, `raft_state`
  (follower/candidate/leader), `raft_vote` (the vote in the current term or
  `NULL`), `appliers` (the sources still accepted).
- Journal: `journal` (the rows in receipt order - the WAL), `journal_vclock`
  (the count of rows per origin; rows of one origin always arrive in order,
  so this says which rows the node has in O(1)), `valid_acks` (per origin,
  whether the ack of its latest row carried a term the origin can count).
- Limbo: `limbo_state`, `limbo_term`, `limbo_owner`, `limbo_vclock`,
  `limbo_term_map`, `limbo_promotions` (the pending slots), `limbo` (the
  queued transaction), `data`, `data_rejected`, `made_txn`.

Actions, in the order of the file:

- **Raft**: `NodeBumpTerm` (start an election: new term, vote for self,
  candidate - from a follower on timeout, from a candidate whose round
  failed, or from a leader leaving its leadership), `NodeVote`,
  `NodeBecomeLeader` (own vote plus the votes received over open links),
  `NodeObserveHigherTerm` (any node, any time a higher term is visible over
  an open link in either direction; the terms travel with the rows and with
  the acks).
- **Limbo PROMOTE**: `LimboWritePromote` (chained over the latest live
  pending if there is one), `LimboConfirmPromote` (own, on a quorum of acks).
- **Limbo transaction**: `LimboCreateTransaction`, `LimboConfirmTransaction`.
- **Replication**: `ReplicateNextEntry(dst)` applies the first row `dst`
  lacks from one of its sources - `ReplicatePromote`, `ReplicateConfirm`
  (which dispatches to `ReplicateConfirmPromote`), `ReplicateTransaction` -
  or refuses it and closes the link (`LinkCloseFromTo`).

`Init` has every node a follower at term 1 with `n1` the limbo owner and no
rows. `Next` is the disjunction of the actions over all nodes. Depth is
bounded by `MaxTerm` (no term above it is started) and breadth optionally
by `MaxPromotes`.

### Modeling decisions worth knowing

Each is in a comment at the place in the spec; this is the map.

- **Rows and terms travel separately.** A PROMOTE can reach a node before
  the Raft term it belongs to (the term goes in a separate Raft message when
  forwarded), and this happens in production. The spec has no assertion
  that a pending PROMOTE's term is at most the node's Raft term; instead
  `LimboWritePromote` refuses to promote while a pending PROMOTE at or above
  the own term exists - the elections have moved on.
- **Acks carry the term of their sending.** `JournalAppend` is also the ack;
  the node remembers per origin whether the ack of the origin's latest row
  carried a term not above the row's (`valid_acks`). An ack may be delivered
  after its sender moved to a higher term and still count, as in reality
  (`relay.cc`, `tx_status_update`: the term in the message is processed
  first, then the ack). Acks travel over the node's applier from the origin,
  so a closed one carries none (`CountAcksForEntry`).
- **`limbo_state` is a stored field**, as in the code where it is kept for
  a fast check, and `LimboStateInvariant` verifies it always equals what
  `txn_limbo_update_state()` derives: owner is self, Raft leader, Raft term
  equals the limbo term. A newer PROMOTE arriving as pending demotes
  nothing; only the observed Raft term or the applied CONFIRM does.
- **Raft is small on purpose.** Three states; a candidate counts its own
  vote; a leader stops being one by observing a higher term or by starting
  a new election - in Tarantool a resigned leader is a follower of the same
  term who can never be elected again in it (votes count only for a
  candidate, `raft_process_msg`), so that follower is not a state of its
  own. Votes are counted while the voter is still at the term; a vote
  delivered later commutes with the voter's later moves. At quorum 1 no
  votes are cast at all: the self-vote is the quorum.
- **Journal order is WAL order and is relayed in that order.** The relay
  offers a destination the first row of its journal the destination lacks.
  This is the replication contract everything rests on ("a conflict is
  always on a row the receiver refuses") and must not be relaxed, however
  many states it costs.
- **Links close only on refusals and never heal**, the operator's rebootstrap
  is out of scope. A majority quorum never refuses (asserted), so in those
  configs no link ever closes. Voters never receive rows: their links carry
  only terms and votes, which makes a PROMOTE quorum above the data node
  count unsatisfiable - such configs are not generated.
- **Detection is not always two-sided.** With two leaders of one term
  (quorum at or below half), a leader re-elected before its PROMOTE was
  confirmed chains over it and forgets the old term; it stores the other
  leader's PROMOTE as live and learns of the fork only from that leader's
  CONFIRM (which poisons its own pending by regression), or never, and then
  it follows. The invariants are written for that: see
  `JournalDeterminesStateInvariant`'s comment.
- **State space reductions**, all argued in the comments: `journal_vclock`
  for O(1) `HasEntry`; one transaction per leadership (`made_txn`); the
  transaction to create chosen deterministically (`CHOOSE`) under the
  transaction symmetry; symmetry over data nodes and over voters separately
  (sound only because `role` is in the state); term observation per term
  rather than per source; replication per distinct row rather than per
  source, a refused row branching over its sources; `MaxPromotes`.
- **Out of scope**: several queued transactions per owner, ROLLBACK rows,
  DEMOTE rows, link recovery.

## What is checked

`TotalInvariant`, on every state of every config:

- `CaughtUpConsistencyInvariant` - once `b` has every row `a` has, `b` made
  every decision `a` made the same way (`a`'s commits are a prefix of `b`'s,
  `a`'s rejections among `b`'s) and confirmed every leadership `a` confirmed
  (term map and limbo term covered). A conflict can exist only on a row the
  receiver refuses. Under a majority quorum this is every pair, always.
- `JournalDeterminesStateInvariant` - two nodes holding the same rows have
  the same derived state, whatever order the rows came in.
- `LimboStateInvariant` - the stored limbo state equals the code's
  derivation, both directions.
- `LimboTermMapInvariant` - no applied term above the limbo term, the
  owner's applied term is the limbo term, no term applied for two origins.
- `JournalLengthInvariant`, `LimboOwnerInvariant` - sanity bounds.

The majority-only claims are `Assert`s inside the actions, gated on
`IsMajorityQuorum`, so they are active in the `majority_*` configs and
inactive in the `bad_*` ones automatically: a majority quorum never refuses
anything (`LinkCloseFromTo`), elects one leader per term
(`LimboStorePromote`), never confirms behind the leader's back
(`LimboConfirmPromote`, `ReplicateConfirmPromote`). Other asserts state
facts the model relies on - a PROMOTE is never covered on arrival, a
non-owner's transaction is always from an old term, the origin's own write
is among the acks - so that TLC proves them rather than the reader.

## Witnesses

An invariant passing says nothing about whether its interesting case was
ever reached, and a model that is too strict passes everything. The
witnesses close that gap: each operator in `ForwardRaftWitness.tla` is the
negation of a scenario the model must be able to reach. TLC violating it is
the goal; the trace is the proof the state space covers the scenario, and a
script for a test. `run.py --witness` expects every config to end with
exactly its own operator violated - the matrix entry's name is the
operator's name - and treats a pass (unreachable), another invariant, a
failed assert or a TLC error as the failure it is.

A scenario visible in one state is an `invariant:` entry. One visible only
in a step - the state after it is reachable another way too, e.g. a chained
PROMOTE's confirmed map is also what a sequence of plain promotions produces
- is a `property:` entry of the form `[][~step]_vars`, checked on every
transition of the same search.

All ten run in about 20 seconds on a laptop. Eight run on three data nodes
with quorum 1 (every node elects itself and confirms alone, every refusal is
possible, the shortest traces), two on a majority quorum, to show the
scenario is not a fork artifact.

| witness                           | kind      | quorum | the scenario reached                                              |
|-----------------------------------|-----------|--------|-------------------------------------------------------------------|
| WitnessTwoLeadersOneTerm          | invariant | 1 of 3 | two leaders of one term, each with its own PROMOTE                |
| WitnessPromoteAheadOfTerm         | invariant | 1 of 3 | a PROMOTE pending on a node whose Raft term is still below it     |
| WitnessDataFork                   | invariant | 1 of 3 | a transaction committed on one node, rolled back on another       |
| WitnessPoisonedConfirmRefused     | property  | 1 of 3 | the CONFIRM of a poisoned pending PROMOTE arrives and is refused  |
| WitnessChainConfirmed             | property  | 1 of 3 | a CONFIRM advances the applied term map in two components at once |
| WitnessOlderPromoteConfirmedLater | property  | 1 of 3 | an own PROMOTE confirmed with a newer live one pending beside it  |
| WitnessConfirmOnDelayedAck        | property  | 2 of 3 | a CONFIRM whose quorum holds only with an ack from a node that moved to a higher term since |
| WitnessLeaderWithNewerPending     | invariant | 2 of 3 | a limbo leader with a newer PROMOTE pending beside it             |
| WitnessQuiescentSplit             | invariant | 1 of 3 | replication finished, the cluster in two groups: refused both ways across, open both ways inside |
| WitnessAllLinksBroken             | invariant | 1 of 3 | every data node refuses every other one; `MaxTerm = 2` suffices  |

The witnesses are also the reachability check for `MaxPromotes`: all ten
need at most four PROMOTEs.

## The test matrix

Naming: `<position>_<majority|bad>_d<data nodes>v<voters>_q<quorum>_t<MaxTerm>`.
The limbo owner at start is always `n1`; voters are the highest node ids.
The position prefix makes a shell glob list the configs in matrix order,
which is ascending by measured duration, so a run gets through as many as
it can before the long ones.

| config                   | nodes | quorum | what it exercises                               | duration (16 cores) |
|--------------------------|-------|--------|-------------------------------------------------|---------------------|
| 01_majority_d2v0_q2_t4   | 2     | 2 of 2 | every ack required, no fork possible            | 3 s                 |
| 02_majority_d2v1_q2_t4   | 2+1   | 2 of 3 | a voter decides elections, data nodes ack alone | 7 s                 |
| 03_majority_d3v0_q2_t3   | 3     | 2 of 3 | smoke test, majority                            | 9 s                 |
| 04_bad_d2v0_q1_t4        | 2     | 1 of 2 | every node elects itself                        | 26 s                |
| 05_majority_d3v0_q2_t4   | 3     | 2 of 3 | the full majority run                           | 14 min              |
| 06_bad_d3v0_q1_t3        | 3     | 1 of 3 | smoke test, two-sided forks                     | 27 min              |
| 07_majority_d3v2_q3_t4   | 3+2   | 3 of 5 | two voters, every data node must ack            | hours               |
| 08_bad_d3v0_q1_t4        | 3     | 1 of 3 | three sides, all links can break; `MaxPromotes 6` of 9 | days        |

Depth: `MaxTerm = 4` allows three promotions, which the deepest known
patterns need - a chain through a chain, a poisoned entry covered by a later
promotion of its origin, three fork sides. `MaxPromotes` caps the PROMOTEs
the whole cluster writes; the natural maximum is `data nodes * (MaxTerm - 1)`
and the default 999 never binds. A cap cuts breadth (not every node promotes
in every term) and keeps depth; it does not limit elections, a node still
reaches every term promoted or not.

Dropped as redundant, with the argument: a config with one node never
acting is a subset of the same config with that node present, and the
invariants range over data nodes only, so an idle voter changes nothing.
`majority_d3v1_q3_t4` is `majority_d3v2_q3_t4` with a voter idle. Every
`bad_*` config with voters is inside `bad_d3v0_q1_t4`: `Quorum` appears in
the spec only as a lower bound (votes to win, acks to confirm), so a smaller
quorum only enables more, acks come from data nodes alone, and a voter's
vote and relayed terms are subsumed at quorum 1 by self-election and term
bumps. The two-node configs are subsets of the three-node ones with a node
idle but run in seconds and stay; the `t3` configs are depth-limited
prefixes of their `t4` runs, kept to fail fast.

## Running

```
python3 ForwardRaft/gen.py ForwardRaft/test.yaml var/test
python3 ForwardRaft/gen.py ForwardRaft/test_witness.yaml var/witness

python3 tools/run.py --tlc /path/to/tla2tools.jar --witness \
    --metadir var/witness/states --spec ForwardRaft/ForwardRaftWitness.tla var/witness/*.cfg

python3 tools/run.py --tlc /path/to/tla2tools.jar --java "java -XX:+UseParallelGC" \
    --java-heap 48g --fpmem 0.5 --checkpoint 30 --workers auto --interval 60 \
    --metadir var/test/states --spec ForwardRaft/ForwardRaft.tla var/test/*.cfg
```

`run.py` runs the configs one by one, stops at the first unexpected
outcome, prints the last TLC progress line when it changes, and writes each
run's complete TLC output next to its config as `<name>_out.txt` with a
footer giving the command and the wall time. `--java` is the JVM with its
options as one string (aliases are not visible to a subprocess),
`--java-heap` its `-Xmx`, `--fpmem` the fingerprint set's share of the heap,
`--checkpoint` the minutes between TLC checkpoints, `--metadir` (required)
where TLC keeps its run files: `<metadir>/<config name>`, deleted after an
expected outcome, kept with its path printed after an unexpected one - the
checkpoint to `-recover` from is there. `run.py --help` explains each. On a
failure the runner prints TLC's error lines and the trace's action list;
`tools/tlatrace.py <out.txt> diff` shows what changed at every step.

Big runs: always set `--java-heap` and `--fpmem` - without them the JVM
takes a quarter of the machine's RAM and TLC a quarter of that for the
fingerprints, and the workers and the disk queue's writer starve; a starved
writer thread dying leaves TLC deadlocked with zero CPU and the progress
line frozen. `--checkpoint 30` makes such a run recoverable. One fingerprint
is 8 bytes per distinct state; when the set is full TLC spills it to disk
and the rate collapses, so size it for the expected count.

## For a reviewer: working cheaply

Everything below finishes in seconds to a few minutes on a laptop.

- Parse check after an edit (from this directory, SANY resolves `EXTENDS`
  relative to the cwd): `java -cp tla2tools.jar tla2sany.SANY ForwardRaftWitness.tla`.
- The witnesses: 20 seconds, and the first thing to run after any change -
  a model that became too strict shows up here as `NOT REACHED`.
- The small test configs: 01-04 in under a minute together. Do not start
  05-08 casually; 07 and 08 are server runs of hours to days.
- Custom small configs: a yaml with `data_nodes`, `voters`, `quorum`,
  `max_term`, `transactions`, optional `max_promotes`, `invariant`,
  `property`, through `gen.py`. Two nodes at `MaxTerm 3` with one
  transaction is ~15k states; three nodes `MaxTerm 3` majority with one
  transaction ~57k; three nodes plus a voter, quorum 2, `MaxTerm 3`, one
  transaction (a bad config with refusals) ~2M and 1-2 minutes.
- Measuring a change: compare "distinct states found" and "states
  generated" in the TLC output before and after on the same small configs.
  A CPU-only change must leave the distinct count identical; a change that
  removes behaviors must say which and why they are artifacts. To size the
  share of states differing only in some field, TLC's `VIEW` directive
  (fingerprint by an expression) counts equivalence classes without
  changing the model.
- A TLC rule that bit us: an `\E` used as a conjunct *inside an action* is
  not a boolean guard - TLC splits the action into one successor per witness,
  duplicates included. A pure guard must be a `~\A`, a `Cardinality` or a
  set comparison; `\E` inside an action is only for a branch that is meant
  (the row to deliver, the source to refuse). In invariants, properties and
  `Assert` arguments `\E` is evaluated as a boolean and is fine.
- Trace reading: `tlatrace.py <out.txt> actions` for the step list,
  `diff` for the per-step field changes (a whole record replaced is one
  line), `show N` for a full state.

Things that look like bugs and are not: `NodeObserveHigherTerm(n3)` in a
trace names no source (the step is per term); replication steps show as
`ReplicateNextEntry(n2)` without the source for the same reason; a node
holding two PROMOTEs of one term in its journal is possible when it forgot
its own superseded term (the one-sided detection above); a limbo leader
with a newer PROMOTE pending beside it is a real state (`txn_limbo_update_state`
ignores pending PROMOTEs), reachable in a majority cluster through a delayed
ack - both are witnessed.

A review of the model with the findings and the decisions taken is kept in
the Tarantool repository under `reviews/tla-spec-review.md`.
