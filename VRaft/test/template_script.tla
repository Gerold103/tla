---- MODULE {name} ----
\* Generated from {source} by gen.py - do not edit, edit the script.
EXTENDS VRaftScript

CONSTANTS {constants}

ScriptLength == {length}

\* The steps, with their lines in the script.
Step(i) ==
    CASE {cases}

\* The Expect lines of the script, each at the step it follows.
Checkpoints ==
{checkpoints}

{run}{bound}
ScriptSpec ==
    /\ ScriptInit
    /\ [][ScriptRun]_svars

====
