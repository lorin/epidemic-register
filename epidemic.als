open concrete

sig Timestamp {
    , number : Int
    , pid: this/Role
}

sig Value extends concrete/Value {}
one sig ok extends concrete/Value {}


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

sig gossip extends step {} {
    post = pre
    M.val = pre.current
    M.t = pre.written
}

sig recv extends concrete/recv {
    , val: this/Value
    , ts: Timestamp
} {
    no M
    lessthan[pre.written, ts] => {
        post.current = val
        post.written = ts
    } else {
        post=pre
    }
}

fact {
    // Only allow model transitions defined in this spec
    E in this/init+read+write+gossip+this/recv

    // All roles must have associated events
    all r : Role | some role.r

    // Don't allow any undefined reads
    all e : read | some e.v

   some read
   some del
}

run {
} for 6 but 2 Role
