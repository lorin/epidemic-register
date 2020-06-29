---- MODULE register ----
CONSTANT Values

VARIABLES method, value, rval

Methods == {"read", "write"}


NIL == CHOOSE NIL: NIL \notin (Values \cup Methods)


Init == /\ method = NIL
        /\ value = NIL
        /\ rval = NIL

Read == /\ method' = "read"
        /\ rval' = value
        /\ UNCHANGED value

Write(x) == /\ method' = "write"
            /\ value' = x
            /\ rval' = "ok"

Next == \/ Read
        \/ \E v \in Values : Write(v)

TypeOK == /\ method \in Methods \cup { NIL }
          /\ value \in Values \cup { NIL }
          /\ rval \in Values \cup { "ok", NIL }

====