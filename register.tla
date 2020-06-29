---- MODULE register ----
CONSTANT Values

VARIABLES method, value, return

Methods == {"read", "write"}


NIL == CHOOSE NIL: NIL \notin (Values \cup Methods)


Init == /\ method = NIL
        /\ value = NIL
        /\ return = NIL

Read == /\ method' = "read"
        /\ return' = value
        /\ UNCHANGED value

Write(x) == /\ method' = "write"
            /\ value' = x
            /\ return' = "ok"

Next == \/ Read
        \/ \E v \in Values : Write(v)

TypeOK == /\ method \in Methods \cup { NIL }
          /\ value \in Values \cup { NIL }
          /\ return \in Values \cup { "ok", NIL }

====