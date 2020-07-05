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
one sig Read,Write extends Operation {}


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
    let ex = Execution, e = (ex.tr).t | (ex.role)[e]
}

sig Value extends c/Value {}
one sig ok extends c/Value {}


sig write extends callret {
    arg : this/Value
} {
    o = Write
    sigma'.current = arg

    sigma'.written.number = sigma.written.number.add[1]

    sigma'.written.pid = lookupRole[this]
    no M
    v = ok

}

one sig Periodically extends Process {}

sig gossip extends step {} {
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
    // Only allow model transitions defined in this spec
    c/Transition in this/init+read+write+gossip+this/rcv
}

/*

Cardinalities for model checking:

Event: N
Role: R<N (let's say R=2)
Value: don't care (let's say 2)
State: Max N-R (init is redundant)+1
Process: 1 (process doesn't really do anything)
Message: Same as State: max N-R
Execution: 1
Trajectory: R
*/ 

// 1 Role
run { 
    
//    some this/read 
//     some this/write
    } for 4 but 1 Execution, 1 Process, 2 this/Value, 2 this/Role

// run { } for 2 but 3 this/State, 4 Timestamp, 3 this/Value


//  run {some read } for 1 but 2 Transition, 2 this/Event, 2 this/State, 3 Timestamp, 2 this/Value, 2 Operation
// run {some write } for 1 but 2 Transition, 2 this/Event, 2 this/State, 3 Timestamp, 2 this/Value

/*

run { 
    some write
//    some read
//    some gossip 
//    some this/rcv 
    } for 4 but 1 Execution, 2 Trajectory

*/
