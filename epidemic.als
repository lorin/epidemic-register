sig Value {}

sig Event {}

sig undef {}

sig Role {}

sig Message {}

sig State {}

sig Process {}

abstract sig Transition {
    , _op: Operation
    , _rcv: Message
    , _proc: Process
    , _pre: State+undef
    , _post: State
    , _snd: set Message
    , _rval: Value
} {

}

sig Operation {}

sig init, call, rcv, step, callret, rcvret, stepret extends Transition {}

sig Trajectory {
  , E : set Event
  , eo: Event -> Event
  , _tr: Event -> Transition
} {

    // t1: eo is an enumeration (total order) of E
   
    no iden & eo // irreflexive 
    no eo & ~eo // anti-symmetric
    all e1, e2 : E | e1!=e2 => e1->e2 in eo or e2->e1 in eo // all elements


    some e : E | {
        e.tr._pre = undef
        pred_[E, eo, e] = undef

    } or pre[e] = post[pred_[E, eo, e]] 

    all c1, c2 : calls[E] | 
        (c1 -> c2) in eo => some r : returns[E] | {
            (c1 -> r) in eo or c1=r
            (r -> c2) in eo
        }

}

fun tr[e: Event] : Transition {
    let traj = E.e | traj._tr[e]
}

fun op[e :Event] : Operation {
    tr[e]._op
}

fun rval[e: Event]: Value {
    tr[e]._rval
}

fun pre[e : Event] : State+undef {
    tr[e]._pre
}

fun post[e : Event] : State {
    tr[e]._post
}

fun calls[E : set Event] : set Event {
    {e: E | no op[e] & undef}
}

fun returns[E : set Event] : set Event {
    {e: E | no rval[e] & undef }

}


// Use pred_ to distinguish from pred keyword
fun pred_[E: set Event, eo: Event->Event, e: Event] : Event+undef {
    eo.e & E
}


run {} for 3