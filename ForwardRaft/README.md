# ForwardRaft test and witness matrices

- `test.yaml` - the test matrix: configs which must pass. The order is the
  run order.
- `test_witness.yaml` - the witness matrix: configs which must reach a
  scenario, see below.
- `template.cfg` - the config template, `gen.py` fills it.
- `gen.py <matrix.yaml> <out dir>` - writes `<out dir>/<name>.cfg` for every
  entry of the matrix. No defaults. Give the two matrices different dirs:
  they run against different modules.
- `ForwardRaftWitness.tla` - the witness operators, extends `ForwardRaft`.
- `ForwardRaft.cfg` - a hand-written majority config (3 nodes, 2 of 3,
  `MaxTerm 3`) for a single quick run outside the matrices.

The out dirs hold runtime files only: the generated configs and the run
outputs. Delete them when done.

## Running

The runner is the generic `tools/run.py`: it takes the TLC command, the
module, the worker count and the configs to run, runs them one by one in
the given order, stops at the first unexpected outcome, prints progress
every N seconds, and writes the complete TLC output of each run next to its
config as `<name>_out.txt` with a footer giving the command and the wall
time. `--fpmem` and `--checkpoint` are forwarded to TLC when given.

    python3 ForwardRaft/gen.py ForwardRaft/test.yaml var/test
    python3 ForwardRaft/gen.py ForwardRaft/test_witness.yaml var/witness

    python3 tools/run.py --tlc /path/to/tla2tools.jar --java "java -XX:+UseParallelGC" \
        --java-heap 48g --fpmem 0.5 --checkpoint 30 --workers auto --interval 60 \
        --spec ForwardRaft/ForwardRaft.tla var/test/*.cfg

    python3 tools/run.py --tlc /path/to/tla2tools.jar --witness \
        --spec ForwardRaft/ForwardRaftWitness.tla var/witness/*.cfg

`--java` is the JVM with its options as one string (aliases are not visible
to a subprocess); `--java-heap` is its `-Xmx`, `--fpmem` the fingerprint
set's share of it, `--checkpoint` the minutes between TLC checkpoints - see
`run.py --help` for what each means and why a big run wants all three. The
test config names carry their position in the matrix, so the shell glob runs
them in the matrix order; for a subset, list them explicitly.

## The test matrix

Every config checks `TotalInvariant`. The majority-only properties are
asserts inside the spec, gated on `IsMajorityQuorum`, so they are active in
the `majority_*` configs and inactive in the `bad_*` ones automatically.
Success is every config passing.

Naming: `<position>_<majority|bad>_d<data nodes>v<voters>_q<quorum>_t<MaxTerm>`.
The limbo owner at start is always `n1`; voters are the highest node ids.

Depth: `MaxTerm = 4` allows three promotions, which is what the deepest
known pattern needs - a chain through a chain, a poisoned entry covered by
a later promotion of its origin, three fork sides. The two `t3` configs are
the fast smoke tests.

Voters in the spec vote and observe terms but receive no rows (a state space
reduction), so a PROMOTE quorum above the data node count can never be met.
Such combinations are left out.

The matrix is ordered by the estimated size, smallest first, so that a run
gets through as many configs as it can before the ones taking a day.

| config                   | nodes | quorum | what it exercises                               |
|--------------------------|-------|--------|-------------------------------------------------|
| 01_majority_d2v0_q2_t4   | 2     | 2 of 2 | every ack required, no fork possible            |
| 02_majority_d2v1_q2_t4   | 2+1   | 2 of 3 | a voter decides elections, data nodes ack alone |
| 03_majority_d3v0_q2_t3   | 3     | 2 of 3 | smoke test, majority                            |
| 04_bad_d2v0_q1_t4        | 2     | 1 of 2 | every node elects itself                        |
| 05_bad_d3v0_q1_t3        | 3     | 1 of 3 | smoke test, two-sided forks                     |
| 06_majority_d3v0_q2_t4   | 3     | 2 of 3 | the full majority run                           |
| 07_majority_d3v2_q3_t4   | 3+2   | 3 of 5 | two voters, every data node must ack            |
| 08_bad_d3v0_q1_t4        | 3     | 1 of 3 | three sides, all links can break                |

Redundancy: a config with one node never acting is a subset of the same
config with that node present, and `Quiescent`, `StatesEqual` range over the
data nodes only, so an idle voter changes nothing in the invariants either.
Hence:

- `majority_d3v1_q3_t4` is `majority_d3v2_q3_t4` with one voter idle (same
  elections, same acks, same `IsMajorityQuorum`) - dropped.
- Voters add nothing to a `bad_*` config beyond `bad_d3v0_q1_t4`. `Quorum`
  appears in the spec only as a lower bound - on the votes to become leader,
  on the acks to confirm a PROMOTE or a transaction - so a smaller quorum
  only enables more. Acks come from data nodes alone, and a voter's remaining
  contribution, its vote and the terms it relays, is subsumed at quorum 1 by
  self-election and term bumps. `bad_d3v1_q2_t4` ("exactly half") and
  `bad_d3v2_q2_t4` ("below half") were dropped; the latter had run three
  days without finishing, two voters multiplying the states by their terms
  and votes.
- The two-node configs are subsets of the three-node ones with `n3` idle,
  except that their `Quiescent` premise holds where an idle `n3` never
  catches up. They run in minutes and stay.
- The `t3` smokes are depth-limited prefixes of their `t4` runs, kept to
  fail fast.

Voters matter in the `majority_*` configs, where they shift what a majority
means relative to the data nodes.

## The witness matrix

An invariant passing says nothing about whether its interesting case was
ever reached. The witnesses close that gap: each is the negation of a
scenario the model must be able to reach, checked as an invariant or a
property. TLC violating it is the goal - the trace is the proof the state
space covers the scenario, and a script for a test. `run.py --witness`
expects every config to end with exactly its own operator violated: a pass
means the scenario is unreachable, anything else failing is a bug like
anywhere else. Hence the matrix entry's name is the operator's name.

A scenario visible in a single state is an `invariant:` entry. One visible
only in a step - when the state after it is reachable another way too, like
a chained PROMOTE whose confirmed map a sequence of plain promotions can
produce as well - is a `property:` entry of the form `[][~step]_vars`,
which TLC checks on every transition of the same search.

The witnesses run on three data nodes with quorum 1: every node elects
itself and confirms alone, every refusal is possible, and every scenario
takes the fewest steps. `MaxTerm = 3` suffices; `AllLinksBroken` needs only
2, three leaders of one term refusing each other's PROMOTE on arrival. Two
witnesses run on a majority quorum instead, to show their scenario is not a
fork artifact: the delayed ack (the own ack is never stale, so it needs a
quorum of two) and the leader with a newer pending PROMOTE.

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
| WitnessAllLinksBroken             | invariant | 1 of 3 | every data node refuses every other one; `MaxTerm = 2`            |
