open concrete

sig Latest extends Message {
    , val : this/Value
    , t : Timestamp
}

sig Timestamp {
    , number : Int
    , pid: this/Role
}

sig R extends concrete/Role {} // Remove namespace from visualization

sig Value extends concrete/Value {}
one sig ok extends concrete/Value {}


pred lessthan(t1, t2 : Timestamp) {
    t1.number < t2.number or {
        t1.number = t2.number
        lt[t1.pid, t2.pid]
    }
}

sig State extends concrete/State {
    , current: lone this/Value
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
    arg : this/Value
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

    // Don't allow any undefined reads
    all e : read | some e.v

   // Some messages
   some del

   // Some reads
   some read

   // All roles have reads
   //all r : Role | read in role.r
}

run {
} for 6 but 2 Role
