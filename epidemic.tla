---- MODULE epidemic ----
EXTENDS TLC

CONSTANTS N, Values

Roles == 1..N

undef == CHOOSE undef: undef \notin Values

(*--algorithm epidemic-register

variables 
    current = [r \in Roles |-> undef];
    written = [r \in Roles |-> [number|->0, pid|->r]];

begin
    skip;
end algorithm; *)


====