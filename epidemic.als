open concrete

sig Latest extends Message {
    , val : this/Value
    , t : Timestamp
}

sig Timestamp {
    , number : Int
    , pid: Role
}

sig R extends Role {} // Remove namespace from visualization

sig V extends Value {}
one sig ok extends Value {}


pred lessthan(t1, t2 : Timestamp) {
    t1.number < t2.number or {
        t1.number = t2.number
        lt[t1.pid, t2.pid]
    }
}

sig State extends concrete/State {
    , current: lone V
    , written: Timestamp
} 


fact "Don't forge messages" {
    dontforge[Latest]
}

sig init extends concrete/init {} {
    no post.current
    post.written.number = 0
    post.written.pid = role
    no M
}

sig read extends callret {} {
    post = pre
    no M
    v = pre.current
}

sig write extends callret {
    arg : V
} {
    post.current = arg
    post.written.number = pre.written.number.add[1]
    post.written.pid = role
    no M
    v = ok
}

sig send extends step {} {
    post = pre
    M.val = pre.current
    M.t = pre.written
}

sig recv extends concrete/recv {
    // m : Message <- defined in in concrete/recv
} {
    no M
    lessthan[pre.written, m.t] => {
        post.current = m.val
        post.written = m.t
    } else {
        post=pre
    }
}


fact {
    // Only allow model transitions defined in this spec
    E in this/init+read+write+send+this/recv

    // All roles must have associated events
    all r : Role | some role.r

    // All timestamps must be associated with a state
    Timestamp in this/State.written

    // Don't allow any undefined reads
    all e : read | some e.v

    // works above here

   // Some messages
   some del

   // All roles have reads
   all r : Role | some read & role.r
}

run {
} for 8 but 2 Role
