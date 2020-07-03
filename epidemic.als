sig Value {}

sig Event {}

sig undef {}

sig Role {}

sig Message {}

sig State {}

sig Process {}

abstract sig Transition {
    , op: Operation
    , rcv: Message
    , proc: Process
    , pre: State+undef
    , post: State
    , snd: set Message
    , rval: Value
} {

}

sig Operation {}

sig init extends Transition {}

sig Trajectory {
  , E : set Event
  , eo: Event -> Event
  , tr: Event -> Transition
} {
    some e : E | {
        e.tr.pre = undef
        pred_[E, eo, e] = undef

    } or @pre[e] = @post[pred_[E, eo, e]] // TODO: rewrite this!!!

}

// E : Trajectory -> set Event
// tr: Trajectory -> Event -> Transition

fun pre[e : Event] : State+undef {
    (E.e).tr[e].pre
}

fun post[e : Event] : State {
    (E.e).tr[e].post
}


// Use pred_ to distinguish from pred keyword
fun pred_[E: set Event, eo: Event->Event, e: Event] : Event+undef {
    eo.e & E
}


run {} for 3