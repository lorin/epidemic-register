---- MODULE epidemic ----
EXTENDS Naturals, Sequences

CONSTANTS N, Values, Steps

Roles == 1..N

Methods == {"read", "write"}

undef == CHOOSE undef: undef \notin (Values \cup Methods)

(*--algorithm epidemic

variables 
    steps = Steps

procedure Read() begin
read:
    method := "read";
    rval := current;
end procedure;

procedure Write(val) begin
write:
    method := "write";
    current := val;
    written := [written EXCEPT !.number = @+1];
    rval := "ok";
end procedure;


fair process Role \in Roles
variables
    method = undef; 
    current = undef;
    written = [number|->0, pid|->self]];
    rval = undef;

begin
\* Each time it's going to randomly choose whether to read, write, send, receive, or do nothing

loop: while steps > 0 do 
body: steps := steps - 1;
      either 
        call Read();
      or
        skip; \* write
      or
        skip; \* send
      or 
        skip; \* receive
      or 
        skip; \* do nothing
      end either;
    end while;
end process

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-e3d6a3d2e2da04fcf8b8797e21b1b82d
VARIABLES method, current, written, rval, steps, pc, stack

vars == << method, current, written, rval, steps, pc, stack >>

ProcSet == (Roles)

Init == (* Global variables *)
        /\ method = [r \in Roles |-> undef]
        /\ current = [r \in Roles |-> undef]
        /\ written = [r \in Roles |-> [number|->0, pid|->r]]
        /\ rval = [r \in Roles |-> undef]
        /\ steps = Steps
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "loop"]

read(self) == /\ pc[self] = "read"
              /\ method' = [method EXCEPT ![self] = "read"]
              /\ rval' = [rval EXCEPT ![self] = current[self]]
              /\ pc' = [pc EXCEPT ![self] = "Error"]
              /\ UNCHANGED << current, written, steps, stack >>

Read(self) == read(self)

loop(self) == /\ pc[self] = "loop"
              /\ IF steps > 0
                    THEN /\ pc' = [pc EXCEPT ![self] = "body"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << method, current, written, rval, steps, stack >>

body(self) == /\ pc[self] = "body"
              /\ steps' = steps - 1
              /\ \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Read",
                                                             pc        |->  "loop" ] >>
                                                         \o stack[self]]
                    /\ pc' = [pc EXCEPT ![self] = "read"]
                 \/ /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "loop"]
                    /\ stack' = stack
                 \/ /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "loop"]
                    /\ stack' = stack
                 \/ /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "loop"]
                    /\ stack' = stack
                 \/ /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "loop"]
                    /\ stack' = stack
              /\ UNCHANGED << method, current, written, rval >>

Role(self) == loop(self) \/ body(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: Read(self))
           \/ (\E self \in Roles: Role(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Roles : WF_vars(Role(self)) /\ WF_vars(Read(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c97f78097b37048b366ec0ebf234e72e


====
