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
    , current: Value
    , written: Timestamp
}

// Protocols, p102
sig Read,Write extends Operation {}

sig read extends callret {} {
    o = Read
    concrete/callret.sigmaP = sigma
    no concrete/callret.M
    concrete/callret.v = sigma.current
}

// Helper function to get role from transition
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
    no concrete/callret.M
    v = ok
}

sig Periodically extends Process {}

sig periodically extends step {} {
    p = Periodically
    concrete/step.sigmaP = sigma
    concrete/step.M.val = sigma.current
    (Latest & concrete/step.M).t = sigma.written
}

sig receive extends rcv {
    , val: Value
    , ts: Timestamp
} {
    lessthan[sigma.written, ts] => {
        sigmaP.current = val
        sigmaP.written = ts
    }
}

run {} for 3