
/*

Concrete executions

From Principles of Eventual Conistency by Sebastian Burckhardt

*/

open util/ordering[Role]

open util/relation

abstract sig Value {}

abstract sig Event {
    , role: Role
    , eo: set Event
} {
    totalOrder[@eo, @Event]
}

abstract sig Role {

}

abstract sig State {}

abstract sig Message {}

abstract sig Transition extends Event {
    , rcv: lone Message
    , pre: lone State
    , post: State
    , snd: set Message
    , rval: lone Value

    , sigma' : State
    , M : set Message
}

abstract sig NonInitialTransition extends Transition {
    , sigma : State
}

//
// See definition 7.2, p85
//

abstract sig init extends Transition {
} {
    no this.@rcv
    no pre
    post = sigma'
    snd = M
    no rval
}

abstract sig call extends NonInitialTransition {
} {
    no this.@rcv 
    pre = sigma
    post = sigma'
    snd = M
    no rval
}

abstract sig rcv extends NonInitialTransition {
    , m : Message
} {
    rcv = m
    pre = sigma
    post = sigma'
    snd = M
    no rval
}

abstract sig step extends NonInitialTransition {
}{
    no this.@rcv
    pre = sigma
    post = sigma'
    snd = M
    no rval
}

abstract sig callret extends NonInitialTransition {
    , v : lone Value
} {
    no this.@rcv
    pre = sigma
    post = sigma'
    snd = M
    rval = v
}

abstract sig rcvret extends NonInitialTransition {
    , m : Message
    , v : Value
} {
    rcv = m
    pre = sigma
    post = sigma'
    snd = M
    rval = v
}

abstract sig stepret extends NonInitialTransition {
    , v : Value
} {
    no this.@rcv
    pre = sigma
    post = sigma'
    snd = M
    rval = v
}

/**
 * Trajectories are defined on p86
 */
pred isTrajectory[E: set Event, eo: Event->Event] {
    // t3: The first (and only the first) transition is an initialization transition, 
    // and the pre-state of each transition matches the post-state of the previous transition
    all e : E | {
        no pre[e]
        no Pred[E, eo, e]
    } or pre[e] = post[Pred[E, eo, e]]

}

// Predecessor based on event ordering.
// We use `Pred` instead of `pred` because `pred` is a reserved keyword
fun Pred[E: set Event, eo: Event->Event, e: Event] : lone Event {
    // Restrict to subset of events we care about
    let eo' = eo & (E->E) | { p : E | (p->e in eo') and no q : E | (p->q) + (q->e) in eo'}
}


run {}