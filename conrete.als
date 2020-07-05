
/*

Concrete executions

From Principles of Eventual Conistency by Sebastian Burckhardt

*/

open util/ordering[Role]

open util/relation

abstract sig Value {}

abstract sig E {
    , role: Role
    , eo: set E
    , del: set E
} {
}

fact {
    totalOrder[eo, E]

    // c5: 
    injective[del, E]
    all s,r : E | (s->r in del) => (s->r in eo) and rcv[r] in snd[s]
}

abstract sig Role {

}

abstract sig State {}

abstract sig Message {}

abstract sig Transition extends E {
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

abstract sig recv extends NonInitialTransition {
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
pred isTrajectory[E': set E, eo: E->E] {

    // t1: eo is an enumeration (total order) of E'
    totalOrder[eo, E']

    // t2: every event is associated with a transition
    E' in Transition

    // t3: The first (and only the first) transition is an initialization transition, 
    // and the pre-state of each transition matches the post-state of the previous transition
    all e : E' | {
        no pre[e]
        no Pred[E', eo, e]
    } or pre[e] = post[Pred[E', eo, e]]


    // t4: A call transition may not follow another call transition unless there is a return transition in between them
    // Not modeling this for now because epidemic register calls all return immediately

    // 7.4: Well-formed trajectories
    // A trajectory (E,eo,tr) is well-formed if each event is preceded by no more returns than calls
    // Not modeling this for now because epidemic register calls all return immediately
}


// 8.3 p109
pred dontforge[M : set Message] {
    all e : E | ((e in recv) && (rcv[e] in M)) => some del.e
}



// Predecessor based on event ordering.
// We use `Pred` instead of `pred` because `pred` is a reserved keyword
fun Pred[E': set E, eo: E->E, e: E] : lone E {
     { p : E' | (p->e in eo) and no q : E' | (p->q) + (q->e) in eo}
}


run {}