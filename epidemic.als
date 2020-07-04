open concrete as c

sig Event extends c/Event {}

sig Role extends c/Role {}

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

fact "Don't forge messages" {
    c/dontforge[Latest]
}

sig State extends c/State {
    , current: this/Value+undef
    , written: Timestamp
}

// Protocols, p102
sig Read,Write extends Operation {}


sig init extends c/init {} {
    sigma'.current = undef
    sigma'.written.number = 0
    sigma'.written.pid = lookupRole[this]
    no M
}

sig read extends callret {} {
    o = Read
    sigma' = sigma
    no M
    v = sigma.current
}

// Helper function to get role from transition
fun lookupRole[t : Transition] : this/Role {
    let ex = Execution, e = (ex.tr_).t | (ex.role)[e]
}

sig Value extends c/Value {}
one sig ok extends c/Value {}


sig write extends callret {
    arg : this/Value
} {
    o = Write
    sigma'.current = arg

    // TODO: Figure out why this is giving me trouble
    sigma'.written.number = sigma.written.number.add[1]

    sigma'.written.pid = lookupRole[this]
    no M
    v = ok

}

sig Periodically extends Process {}

sig periodically extends step {} {
    p = Periodically
    sigma' = sigma
    M.val = sigma.current
    M.t = sigma.written
}

sig rcv extends c/rcv {
    , val: this/Value
    , ts: Timestamp
} {
    no M
    lessthan[sigma.written, ts] => {
        sigma'.current = val
        sigma'.written = ts
    } else {
        sigma'=sigma
    }
}


fact {
    // Only model transitions defined in this spec
    c/Transition in this/init+read+write+periodically+this/rcv
}


run {some write } for 1 but 2 Transition, 2 this/Event, 2 this/State, 3 Timestamp, 2 this/Value

//run { } for 4 but 1 Execution, 2 Trajectory
