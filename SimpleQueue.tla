------------------------------ MODULE SimpleQueue ------------------------------
\* A queue of numbers which are delivered in one direction via a pipe of a
\* limited size.

EXTENDS TLC, Integers, Sequences

--------------------------------------------------------------------------------
\*
\* Constant values.
\*

\* How many messages to pass through the pipe in total.
CONSTANT Count
\* How many messages can be in the pipe at once.
CONSTANT Lim

--------------------------------------------------------------------------------
\*
\* Initialization.
\*

\* Sequence of messages. Example: <<1, 2, 3, 4, 5>>.
VARIABLES Pipe, LastReceived, LastSent

vars == <<Pipe, LastReceived, LastSent>>

Init ==
  /\ Pipe = << >>
  /\ LastReceived = 0
  /\ LastSent = 0

--------------------------------------------------------------------------------
\*
\* Actions.
\*

Send ==
  /\ Len(Pipe) < Lim
  /\ LastSent < Count
  /\ Pipe' = Append(Pipe, LastSent + 1)
  /\ LastSent' = LastSent + 1
  /\ UNCHANGED<<LastReceived>>

Recv ==
  /\ Len(Pipe) > 0
  /\ LastReceived' = Head(Pipe)
  /\ Pipe' = Tail(Pipe)
  /\ UNCHANGED<<LastSent>>

Next == Send \/ Recv

--------------------------------------------------------------------------------
\*
\* Invariants.
\*

\* Numbers are ordered, the limit is never exceeded.
PipeInvariant ==
  /\ \A i \in 1..Len(Pipe) - 1: Pipe[i] + 1 = Pipe[i + 1]
  /\ Len(Pipe) =< Lim
  /\ \/ Len(Pipe) = 0
     \/ Pipe[1] = LastReceived + 1

TerminalPropetry == <>[](LastSent = Count /\ LastReceived = Count)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Send)
  /\ WF_vars(Recv)

================================================================================
