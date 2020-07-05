open concrete

sig Timestamp {
    , number : Int
    , pid: this/Role
}


pred lessthan(t1, t2 : Timestamp) {
    t1.number < t2.number or {
        t1.number = t2.number
        lt[t1.pid, t2.pid]
    }
}

sig Latest extends Message {
    , val : this/Value
    , t : Timestamp
}

sig State extends concrete/State {
    , current: lone Value
    , written: Timestamp
} 


fact "Don't forge messages" {
    dontforge[Latest]
}

sig init extends concrete/init {} {
    no sigma'.current
    sigma'.written.number = 0
    sigma'.written.pid = role
    no M
}
