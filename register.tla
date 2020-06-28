---- MODULE register ----
EXTENDS TLC

CONSTANT Values

VARIABLES method, value, return

Methods == {"read", "write"}


NIL == CHOOSE NIL: NIL \notin (Values \union Methods)


Init == /\ method = NIL
        /\ value = NUL
        /\ return = NIL

Read == /\ method' = "read"
        /\ return' = value
        /\ UNCHANGED value

Write(x) == /\ method' = "write"
            /\ value' = x
            /\ return' = "ok"

Next == \/ Read
        \/ \E v \in Values : Write(v)

TypeOk == /\ method \in Methods \union { NIL }
          /\ value \in Values \union { NIL }
          /\ return \in Values \union { NIL }

====