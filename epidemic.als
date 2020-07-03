open util/ordering[Role]

sig Value {}

sig Event {}

sig undef {}

sig Role {}

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

sig Message {
    , val: Value
    , t: Timestamp
}

sig State {}

sig Process {}

abstract sig Transition {
    , _op: Operation+undef
    , _rcv: Message
    , _proc: Process
    , _pre: State+undef
    , _post: State
    , _snd: set Message
    , _rval: Value+undef
} {}

sig Operation {}

sig init, call, rcv, step, callret, rcvret, stepret extends Transition {}

/**
 * Trajectories are defined on p86
 */
sig Trajectory {
  , _E : set Event
  , _eo: Event -> Event
  , _tr: Event -> Transition // t2
} {

    // t1: eo is an enumeration (total order) of E
   
    no iden & _eo // irreflexive 
    no _eo & ~_eo // anti-symmetric
    all e1, e2 : _E | e1!=e2 => e1->e2 in _eo or e2->e1 in _eo // all elements


    // t3: The first (and only the first) transition is an initialization transition, 
    // and the pre-state of each transition matches the post-state of the previous transition
    some e : _E | {
        e.tr._pre = undef
        pred_[_E, _eo, e] = undef

    } or pre[e] = post[pred_[_E, _eo, e]] 

    // t4: A call transition may not follow another call transition unless there is a return transition in between them:
    all c1, c2 : calls[_E] | 
        (c1 -> c2) in _eo => some r : returns[_E] | {
            (c1 -> r) in _eo or c1=r
            (r -> c2) in _eo
        }


    // Definition 7.4:
    // A trajectory is well-formed if each event is preceded by no more returns than calls
    // We enforce well-formedness here
    all e : _E | #{r : returns[_E] | r->e in _eo or r=e} <= #{c : calls[_E] | c->e in _eo or c=e}

}

fun tr[e: Event] : Transition {
    ConcreteExecution.tr_[e]
}

fun op[e :Event] : Operation+undef{
    tr[e]._op
}

fun rval[e: Event]: Value+undef {
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

// pred(E, eo, e) is the partial function that returns the predecessor of e in E with respect to the enumeration eo
// , or is undefined (⊥) if there is no predecessor
// We call it pred_ here because `pred` is a reserved word
fun pred_[E: set Event, eo: Event->Event, e: Event] : Event+undef {
    eo.e & E
}

fun rcv[e : Event] : Message {
    tr[e]._rcv
}

fun snd[e : Event] : set Message {
    tr[e]._snd
}


/**
 * Concrete executions are defined on p87
 */
one sig ConcreteExecution {
    , E: set Event
    , eo: Event -> Event
    , tr_: Event -> Transition
    , role: Event -> Role
    , del: Event -> Event
} {
  // c4: events for each role are a trajectory
  all r : Role | some t : Trajectory | {
      t._E = role.r
      t._eo in eo
      t._tr in tr_

  }

  // c6: 
  all e : E | lone del.e // injective
  all s,r : E | (s->r in del) => (s->r in eo) and (rcv[r] in snd[s])
}



run {} for 3