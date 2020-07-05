
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


run {}