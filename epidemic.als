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

sig ERState extends State {
    , current: Value
    , written: Timestamp
}

// Protocols, p102
sig Read,Write extends Operation {}

sig read extends callret {} {
    o = Read
    sigmaP = sigma
    no M
    v = sigma.current
}

fun lookupRole[t : Transition] : Role {
    let c = ConcreteExecution, e = (c.tr_).t | (c.role)[e]
}

one sig ok extends Value {}

sig write extends callret {
    arg : Value
} {
    o = Write
    sigmaP.current = arg
    sigmaP.written.number = sigma.written.number+1
    sigmaP.written.pid = lookupRole[this]
    no M
    v = ok
}


run {} for 3