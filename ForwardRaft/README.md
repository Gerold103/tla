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

    python3 tools/run.py --interval 60 --workers auto \
        --tlc "java -XX:+UseParallelGC -cp /path/to/tla2tools.jar tlc2.TLC" \
        --spec ForwardRaft/ForwardRaft.tla var/test/*.cfg

    python3 tools/run.py --witness --interval 60 --workers auto \
        --tlc "..." --spec ForwardRaft/ForwardRaftWitness.tla var/witness/*.cfg

Aliases are not visible to a subprocess, so the TLC command has to be the
expanded one. The shell glob gives the configs in name order; to run them in
the matrix order, or a subset, list them explicitly.

## The test matrix

Every config checks `TotalInvariant`. The majority-only properties are
asserts inside the spec, gated on `IsMajorityQuorum`, so they are active in
the `majority_*` configs and inactive in the `bad_*` ones automatically.
Success is every config passing.

Naming: `d<data nodes>v<voters>_q<quorum>_t<MaxTerm>`. The limbo owner at
start is always `n1`; voters are the highest node ids.

Depth: `MaxTerm = 4` allows three promotions, which is what the deepest
known pattern needs - a chain through a chain, a poisoned entry covered by
a later promotion of its origin, three fork sides. The two `t3` configs are
the fast smoke tests.

Voters in the spec vote and observe terms but receive no rows (a state space
reduction), so a PROMOTE quorum above the data node count can never be met.
Such combinations are left out.

| config                | nodes | quorum | what it exercises                               |
|-----------------------|-------|--------|-------------------------------------------------|
| majority_d3v0_q2_t3   | 3     | 2 of 3 | smoke test, majority                            |
| bad_d3v0_q1_t3        | 3     | 1 of 3 | smoke test, two-sided forks                     |
| majority_d3v0_q2_t4   | 3     | 2 of 3 | the full majority run                           |
| majority_d2v0_q2_t4   | 2     | 2 of 2 | every ack required, no fork possible            |
| majority_d2v1_q2_t4   | 2+1   | 2 of 3 | a voter decides elections, data nodes ack alone |
| majority_d3v1_q3_t4   | 3+1   | 3 of 4 | even node count                                 |
| majority_d3v2_q3_t4   | 3+2   | 3 of 5 | the former large config                         |
| bad_d2v0_q1_t4        | 2     | 1 of 2 | every node elects itself                        |
| bad_d3v0_q1_t4        | 3     | 1 of 3 | three sides, all links can break                |
| bad_d3v1_q2_t4        | 3+1   | 2 of 4 | exactly half: disjoint pairs, a voter in one    |

Voters add nothing to a `bad_*` config beyond `bad_d3v0_q1_t4`. `Quorum`
appears in the spec only as a lower bound - on the votes to become leader,
on the acks to confirm a PROMOTE or a transaction - so a smaller quorum only
enables more. Acks come from data nodes alone, and a voter's remaining
contribution, its vote and the terms it relays, is subsumed at quorum 1 by
self-election and term bumps. `bad_d3v1_q2_t4` is kept as the "exactly
half" shape operators do configure; `bad_d3v2_q2_t4` was dropped after
three days of running without finishing - two voters multiply the states
(terms and votes of each) and add no scenario. Voters matter in the
`majority_*` configs, where they shift what a majority means relative to the
data nodes.

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

All witnesses run on three data nodes with quorum 1: every node elects
itself and confirms alone, every refusal is possible, and every scenario
takes the fewest steps. `MaxTerm = 3` suffices for all but one.

| witness                           | kind      | the scenario reached                                              |
|-----------------------------------|-----------|-------------------------------------------------------------------|
| WitnessTwoLeadersOneTerm          | invariant | two leaders of one term, each with its own PROMOTE                |
| WitnessPromoteAheadOfTerm         | invariant | a PROMOTE pending on a node whose Raft term is still below it     |
| WitnessDataFork                   | invariant | a transaction committed on one node, rolled back on another       |
| WitnessPoisonedConfirmRefused     | property  | the CONFIRM of a poisoned pending PROMOTE arrives and is refused  |
| WitnessChainConfirmed             | property  | a CONFIRM advances the applied term map in two components at once |
| WitnessOlderPromoteConfirmedLater | property  | an own PROMOTE confirmed with a newer live one pending beside it  |
| WitnessQuiescentSplit             | invariant | replication finished, cluster split, one pair still connected     |
| WitnessAllLinksBroken             | invariant | every data node refuses every other one; `MaxTerm = 4`            |
