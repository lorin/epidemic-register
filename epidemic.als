sig Value {}

sig Event {}

sig undef {}

sig Role {}

sig Message {}

sig State {}

sig Process {}

/**
 * Concrete executions are defined on p86
 */
one sig ConcreteExecution {
    , E: set Event
    , tr_: Transition
    , role: Event -> Role
    , del: Event -> Event
} {
  // c6: 
  all e : E | lone del.e // injective
  all s,r : E | s->r in del => s->r in eo and rcv[r] in snd[s]

}

abstract sig Transition {
    , _op: Operation
    , _rcv: Message
    , _proc: Process
    , _pre: State+undef
    , _post: State
    , _snd: set Message
    , _rval: Value
} {}

sig Operation {}

sig init, call, rcv, step, callret, rcvret, stepret extends Transition {}

/**
 * Trajectories are defined on p86
 */
sig Trajectory {
  , E : set Event
  , eo: Event -> Event
  , _tr: Event -> Transition // t2
} {

    // t1: eo is an enumeration (total order) of E
   
    no iden & eo // irreflexive 
    no eo & ~eo // anti-symmetric
    all e1, e2 : E | e1!=e2 => e1->e2 in eo or e2->e1 in eo // all elements


    // t3: The first (and only the first) transition is an initialization transition, 
    // and the pre-state of each transition matches the post-state of the previous transition
    some e : E | {
        e.tr._pre = undef
        pred_[E, eo, e] = undef

    } or pre[e] = post[pred_[E, eo, e]] 

    // t4: A call transition may not follow another call transition unless there is a return transition in between them:
    all c1, c2 : calls[E] | 
        (c1 -> c2) in eo => some r : returns[E] | {
            (c1 -> r) in eo or c1=r
            (r -> c2) in eo
        }


    // Definition 7.4:
    // A trajectory is well-formed if each event is preceded by no more returns than calls
    // We enforce well-formedness here
    all e : E | #{r : returns[E] | r->e in eo or r=e} <= #{c : calls[E] | c->e in eo or c=e}



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


fun rcv[e : Event] : Message {
    tr[e]._rcv
}

fun snd[e : Event] : set Message {
    tr[e]._snd
}

fun calls[E : set Event] : set Event {
    {e: E | no op[e] & undef}
}

fun returns[E : set Event] : set Event {
    {e: E | no rval[e] & undef }

}

// pred(E, eo, e) is the partial function that returns the predecessor of e in E with respect to the enumeration eo
// , or is undefined (⊥) if there is no predecessor
// We call it pred_ here because `pred` is a reserved word
fun pred_[E: set Event, eo: Event->Event, e: Event] : Event+undef {
    eo.e & E
}

run {} for 3