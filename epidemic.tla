---- MODULE epidemic ----
EXTENDS Naturals

CONSTANTS N, Values

Roles == 1..N

undef == CHOOSE undef: undef \notin Values

(*--algorithm epidemic

variables 
    current = [r \in Roles |-> undef];
    written = [r \in Roles |-> [number|->0, pid|->r]];

begin
    skip;
end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-82108082f0ce45a2ad05bae43beadd5e
VARIABLES current, written, pc

vars == << current, written, pc >>

Init == (* Global variables *)
        /\ current = [r \in Roles |-> undef]
        /\ written = [r \in Roles |-> [number|->0, pid|->r]]
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ pc' = "Done"
         /\ UNCHANGED << current, written >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-09aa14808c124d7bf1780094d9a1fbd5


====
