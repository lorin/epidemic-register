/*

Concrete executions

From Principles of Eventual Conistency by Sebastian Burckhardt

*/
open util/ordering[Role]

sig Value {}

sig Event {}

one sig undef {}

sig Role {}

abstract sig State {}

abstract sig Process {}

abstract sig Message {}

abstract sig Transition {
    , _op: Operation+undef
    , _rcv: Message+undef
    , _proc: Process+undef
    , _pre: State+undef
    , _post: State
    , _snd: set Message
    , _rval: Value+undef

    , sigmaP : State
    , M : set Message
} {}

abstract sig NonInitialTransition extends Transition {
    , sigma : State
}

abstract sig Operation {}

//
// See definition 7.2, p85
//

abstract sig init extends Transition {
} {
    _op = undef
    _rcv = undef
    _proc = undef
    _pre = undef
    _post = sigmaP
    _snd = M
    _rval = undef
}

abstract sig call extends NonInitialTransition {
    , o: Operation
} {
    _op = o
    _rcv = undef
    _proc = undef
    _pre = sigma
    _post = sigmaP
    _snd = Message
    _rval = undef
}

abstract sig rcv extends NonInitialTransition {
    , m : Message
} {
    _op = undef
    _rcv = m
    _proc = undef
    _pre = sigma
    _post = sigmaP
    _snd = Message
    _rval = undef
}

abstract sig step extends NonInitialTransition {
    , p : Process
}{
    _op = undef
    _rcv = undef
    _proc = p
    _pre = sigma
    _post = sigmaP
    _snd = Message
    _rval = undef
}

abstract sig callret extends NonInitialTransition {
    , o: Operation
    , v : Value
} {
    _op = o
    _rcv = undef
    _proc = undef
    _pre = sigma
    _post = sigmaP
    _snd = Message
    _rval = v
}

abstract sig rcvret extends NonInitialTransition {
    , m : Message
    , v : Value
} {
    _op = undef
    _rcv = m
    _proc = undef
    _pre = sigma
    _post = sigmaP
    _snd = Message
    _rval = v
}

abstract sig stepret extends NonInitialTransition {
    , p : Process
    , v : Value
} {
    _op = undef
    _rcv = undef
    _proc = p
    _pre = sigma
    _post = sigmaP
    _snd = Message
    _rval = v
}


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
    Execution.tr_[e]
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
one sig Execution {
    , E: set Event
    , eo: Event -> Event
    , tr_: Event one -> one Transition
    , role: Event -> one Role
    , del: Event -> Event
} {

  // c4: events for each role are a trajectory
  all r : Role | some t : Trajectory | {
      t._E = role.r
      t._eo in eo
      t._tr in tr_

  }

  // c5: 
  all e : E | lone del.e // injective
  all s,r : E | (s->r in del) => (s->r in eo) and (rcv[r] in snd[s])


// There is at least one initialization transition in each role
  all r : Role | some init & tr[role.r]
}
