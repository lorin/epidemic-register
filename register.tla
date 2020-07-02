---- MODULE register ----
CONSTANTS Values, NIL

VARIABLES method, value, rval

Methods == {"read", "write"}


ASSUME NIL \notin (Values \cup Methods)


Init == /\ method = NIL
        /\ value = NIL
        /\ rval = NIL

Read == /\ method' = "read"
        /\ rval' = value
        /\ UNCHANGED value

Write(x) == /\ method' = "write"
            /\ value' = x
            /\ rval' = "ok"
            
\* No operation
Nop ==  /\ method' = NIL
        /\ rval' = NIL
        /\ UNCHANGED value

Next == \/ Read
        \/ \E v \in Values : Write(v)
        \/ Nop

TypeOK == /\ method \in Methods \cup { NIL }
          /\ value \in Values \cup { NIL }
          /\ rval \in Values \cup { "ok", NIL }


vars == <<method, value, rval>>

Spec == Init /\ [][Next]_vars

====