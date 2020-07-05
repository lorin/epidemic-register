
/*

Concrete executions

From Principles of Eventual Conistency by Sebastian Burckhardt

*/

open util/ordering[Role]

open util/relation as r

abstract sig Value {}

abstract sig Event {
    , role: Role
    , eo: set Event
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


run {}