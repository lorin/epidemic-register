/*

Concrete executions

From Principles of Eventual Conistency by Sebastian Burckhardt

*/

open util/ordering[Role]
open util/relation as r

abstract sig Value {}

abstract sig Event {
    // Not part of the original, added for convenience
    , role: one Role
} {
    role = (Execution.@role)[this]
}

one sig undef {}

abstract sig Role {
    // TODO: Remove, this is a temporary thing
    , traj: one Trajectory
} 

fact "Role to trajectory is one-to-one" {
    r/injective[traj, Trajectory]
}

abstract sig State {}

abstract sig Process {}

abstract sig Message {}

fun lookupEvent[t : Transition[]] : Event {
    Execution.del.(Execution.tr.t)
}


abstract sig Transition {
    , op: Operation+undef
    , rcv: Message+undef
    , proc: Process+undef
    , pre: State+undef
    , post: State
    , snd: set Message
    , rval: Value+undef

    , sigma' : State
    , M : set Message

    // These are not part of the original doc, but added here for convenience
    , e : one Event
    , role: one Role
    , next : lone Transition
} {
    e = Execution.tr.this  
    role = Execution.@role[e]

    next = { n : Event | { 
        e->n in Execution.eo 
        no m : Event | ((e->m)+(m->n)) in Execution.eo 
        }
    }.(Execution.tr)
}

abstract sig NonInitialTransition extends Transition {
    , sigma : State
}

abstract sig Operation {}

//
// See definition 7.2, p85
//

abstract sig init extends Transition {
} {
    op = undef
    rcv = undef
    proc = undef
    pre = undef
    post = sigma'
    snd = M
    rval = undef
}

abstract sig call extends NonInitialTransition {
    , o: Operation
} {
    op = o
    rcv = undef
    proc = undef
    pre = sigma
    post = sigma'
    snd = M
    rval = undef
}

abstract sig rcv extends NonInitialTransition {
    , m : Message
} {
    op = undef
    rcv = m
    proc = undef
    pre = sigma
    post = sigma'
    snd = M
    rval = undef
}

abstract sig step extends NonInitialTransition {
    , p : Process
}{
    op = undef
    rcv = undef
    proc = p
    pre = sigma
    post = sigma'
    snd = M
    rval = undef
}

abstract sig callret extends NonInitialTransition {
    , o: Operation
    , v : Value+undef
} {
    op = o
    rcv = undef
    proc = undef
    pre = sigma
    post = sigma'
    snd = M
    rval = v
}

abstract sig rcvret extends NonInitialTransition {
    , m : Message
    , v : Value
} {
    op = undef
    rcv = m
    proc = undef
    pre = sigma
    post = sigma'
    snd = M
    rval = v
}

abstract sig stepret extends NonInitialTransition {
    , p : Process
    , v : Value
} {
    op = undef
    rcv = undef
    proc = p
    pre = sigma
    post = sigma'
    snd = M
    rval = v
}


/**
 * Trajectories are defined on p86
 */
abstract sig Trajectory {
  , E : set Event
  , eo: Event -> Event
  , tr: Event -> one Transition // t2
} {
    //  domain of tr must be E
    tr.Transition in E

    // t1: eo is an enumeration (total order) of E
    totalOrder[eo, E]



    // t3: The first (and only the first) transition is an initialization transition, 
    // and the pre-state of each transition matches the post-state of the previous transition

    // TODO: Figure out why this is problematic
    /*
    all e : E | {
        // Initial state
        pre[e] = undef // no pre-state
        pred_[E, eo, e] = undef // no predecessor

    } or pre[e] = post[pred_[E, eo, e]]  // prestate is poststate of predecessor
    */

    // t4: A call transition may not follow another call transition unless there is a return transition in between them:
    all c1, c2 : calls[E] | 
        (c1 -> c2) in eo => some r : returns[E] | {
            (c1 -> r) in eo or c1=r
            (r -> c2) in eo
        }


    // Definition 7.4:
    // A trajectory is well-formed if each event is preceded by no more returns than calls
    // We enforce well-formedness here
    all e : this.@E | #{r : returns[E] | r->e in eo or r=e} <= #{c : calls[E] | c->e in eo or c=e}
}

fun tr[e: Event] : Transition {
    Execution.tr[e]
}

fun op[e :Event] : Operation+undef{
    tr[e].op
}

fun rval[e: Event]: Value+undef {
    tr[e].rval
}

fun pre[e : Event] : State+undef {
    tr[e].pre
}

fun post[e : Event] : State {
    tr[e].post
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
    let result = { p : E | {
        p->e in eo 
        no q : E | ((p->q) + (q->e)) in eo
        }
    } | some result => result else undef
}



// Message received
fun rcvd[e : Event] : Message {
    tr[e].rcv
}

// Messages sent
fun snt[e : Event] : set Message {
    tr[e].snd
}


/**
 * Concrete executions are defined on p87
 */
one sig Execution {
    , E: set Event
    , eo: Event -> Event
    , tr: Event one -> one Transition
    , role: Event -> one Role
    , del: Event -> Event
} {

    // All events are in the concrete execution
    Event in E

/*
    // All events are associated with a role
    E in role.Role


    // Each role's events are associated with a trajectory
    all r : Role | some t : Trajectory | {
        t.@E = role.r
    }
    
    // c4: events for each role form a trajectory
    all t : Trajectory | some r: Role {
        t.@E = role.r
        t.@eo in eo
        t.@tr in tr
    }
    */

    // Execution order constraints
    totalOrder[eo, E]

    // c5: 
    injective[del, E]
    all s,r : E | (s->r in del) => (s->r in eo) and (rcvd[r] in snt[s])
  

    // There is at least one initialization transition in each role
    // Need to do this this.@ trick to disambiguate Execution.tr from the tr function
    all r : Role | init in (role.r).(this.@tr)
}


// 8.3 p109
pred dontforge[M : set Message] {
    all e : Event | ( tr[e] in rcv && rcvd[e] in M) => some del.e
}
