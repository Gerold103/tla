------------------------------- MODULE RemoveSeq -------------------------------
EXTENDS TLC, Integers, Sequences

Remove(i, seq) == 
  [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] 
                                      ELSE seq[j+1]]

\* An example how to print expressions for debug.
Expr == (1..3) \X {"a", "b"} \X {"c", "d"}
ASSUME PrintT(Expr)
=============================================================================
