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


sig Latest extends Message {
    , val : Value
    , t : Timestamp
}

sig ERState extends State {
    , current: Value+undef
    , written: Timestamp
}

// Protocols, p102
sig Read,Write extends Operation {}

sig init extends concrete/init {} {
    sigmaP.current = undef
    sigmaP.written.number = 0
    sigmaP.written.pid = lookupRole[this]
}

sig read extends callret {} {
    o = Read
    sigmaP = sigma
    no M
    v = sigma.current
}

// Helper function to get role from transition
fun lookupRole[t : Transition] : Role {
    let ex = Execution, e = (ex.tr_).t | (ex.role)[e]
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

sig Periodically extends Process {}

sig periodically extends step {} {
    p = Periodically
    sigmaP = sigma
    M.val = sigma.current
    M.t = sigma.written
}

sig rcv extends concrete/rcv {
    , val: Value
    , ts: Timestamp
} {
    lessthan[sigma.written, ts] => {
        sigmaP.current = val
        sigmaP.written = ts
    }
}

fact {
    // Only messages in this spec
    concrete/Transition in this/init+read+write+periodically+this/rcv
}
run {} for 2 but 1 Role
