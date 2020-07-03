open concrete

sig Timestamp {
    , number : Int
    , pid: Role
}

pred lessthan(t1, t2 : Timestamp) {
    t1.number < t2.number or {
        t1.number = t2.number
        lt[t1.pid, t2.pid]
    }
}

sig ERMessage  extends Message {
    , val: Value
    , t: Timestamp
}


run {} for 3