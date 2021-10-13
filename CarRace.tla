-------------------------------- MODULE CarRace --------------------------------
\* Cars are racing to a finish line. They move one at a time. Hence only one car
\* should win before all the others. After one wins, all the others must stop.

EXTENDS TLC, Integers, Sequences

--------------------------------------------------------------------------------
\*
\* Constant values.
\*

\* Set of cars. For example, some model values.
CONSTANT Cars
\* Distance to pass.
CONSTANT Distance

--------------------------------------------------------------------------------
\*
\* Initialization.
\*

\* Position of each car.
VARIABLE Positions

vars == <<Positions>>

Init == Positions = [c \in Cars |-> 0]

Perms == Permutations(Cars)

--------------------------------------------------------------------------------
\*
\* Actions.
\*

MoveOne(c) == LET pos == Positions[c] IN
  /\ pos < Distance
  /\ Positions' = [Positions EXCEPT ![c] = pos + 1]

Next ==
  \* Continue only if no one has won yet.
  /\ \A c \in Cars: Positions[c] < Distance
  /\ \E c \in Cars: MoveOne(c)

--------------------------------------------------------------------------------
\*
\* Invariants.
\*

\* Either no winners yet, or just one.
RaceInvariant ==
  \/ \A c \in Cars: Positions[c] < Distance
  \/ \E c \in Cars:
    /\ Positions[c] = Distance
    /\ \A c2 \in Cars \ {c}: Positions[c2] < Distance

\* Eventually a winner is found and it never goes back.
TerminalPropetry == <>[](\E c \in Cars: Positions[c] = Distance)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

================================================================================
