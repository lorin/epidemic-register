---- MODULE epidemic ----
EXTENDS Naturals, Sequences

CONSTANTS N, Values, Steps

Roles == 1..N

Methods == {"read", "write"}

undef == CHOOSE undef: undef \notin (Values \cup Methods)

(*--algorithm epidemic

variables 
    steps = Steps;
    messages = {};
    history = {};

define
    Timestamp(number, pid) == [number|->number, pid|->pid]
    Latest(val, t) == [val|->val, t|->t]
    lessthan(t1, t2) == LET n1 == t1.number
                            n2 == t2.number
                            pid1 == t1.pid
                            pid2 == t2.pid
                        IN (n1 < n2) \/ (n1=n2 /\ pid1<pid2)
end define;

macro Read() begin
    seq := seq + 1;
    retval := current;
    history := history \union {[op|->"read", val|->retval,t|->written.number, pid|->written.pid, seq|->seq]};
end macro;

macro Write(val) begin
    current := val;
    written := Timestamp(written.number+1,self);
    retval := "ok";
    seq := 0;
    history := history \union {[op|->"write", val|->val,t|->written.number, pid|->self, seq|->seq]};
end macro;

macro Send() begin
    messages := messages \union {Latest(current, written)};
end macro;

macro Receive(val, ts) begin
    if lessthan(written, ts) then 
        current := val;
        written := ts;
        seq := 0;
    end if;
end macro;


fair process Role \in Roles
variables
    current = undef;
    written = Timestamp(0, self);
    retval = undef;
    seq = 0;

begin
\* On each iteration: read, write, send a message, or receive a message

loop: while steps > 0 do 
      steps := steps - 1;
      either 
        Read();
      or
        with v \in Values do Write(v); end with;
      or
        Send();
      or 
        with m \in messages do Receive(m.val, m.t); end with
      or 
        skip; \* do nothing
      end either;
    end while;
end process

fair process Serialize = 0
variables
    evt = undef;
    method = undef;
    value = undef;
    rval = undef;

begin
guard: await steps = 0;
wh:    while history /= {} do
next:  evt := CHOOSE h \in history : 
            \A x \in history \ {h}:  
                \/ h.t < x.t 
                \/ /\ h.t = x.t
                   /\ h.pid < x.pid
                \/ /\ h.t = x.t 
                   /\ h.pid = x.pid 
                   /\ h.seq < x.seq;
       method := evt.op;
       value := evt.val;
       rval := IF method = "read" THEN evt.val ELSE "ok";
       history := history \ {evt};
end while;
end process

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-420ed5f15996682d5f12d353a75ab5db
VARIABLES steps, messages, history, pc

(* define statement *)
Timestamp(number, pid) == [number|->number, pid|->pid]
Latest(val, t) == [val|->val, t|->t]
lessthan(t1, t2) == LET n1 == t1.number
                        n2 == t2.number
                        pid1 == t1.pid
                        pid2 == t2.pid
                    IN (n1 < n2) \/ (n1=n2 /\ pid1<pid2)

VARIABLES current, written, retval, seq, evt, method, value, rval

vars == << steps, messages, history, pc, current, written, retval, seq, evt, 
           method, value, rval >>

ProcSet == (Roles) \cup {0}

Init == (* Global variables *)
        /\ steps = Steps
        /\ messages = {}
        /\ history = {}
        (* Process Role *)
        /\ current = [self \in Roles |-> undef]
        /\ written = [self \in Roles |-> Timestamp(0, self)]
        /\ retval = [self \in Roles |-> undef]
        /\ seq = [self \in Roles |-> 0]
        (* Process Serialize *)
        /\ evt = undef
        /\ method = undef
        /\ value = undef
        /\ rval = undef
        /\ pc = [self \in ProcSet |-> CASE self \in Roles -> "loop"
                                        [] self = 0 -> "guard"]

loop(self) == /\ pc[self] = "loop"
              /\ IF steps > 0
                    THEN /\ steps' = steps - 1
                         /\ \/ /\ seq' = [seq EXCEPT ![self] = seq[self] + 1]
                               /\ retval' = [retval EXCEPT ![self] = current[self]]
                               /\ history' = (history \union {[op|->"read", val|->retval'[self],t|->written[self].number, pid|->written[self].pid, seq|->seq'[self]]})
                               /\ UNCHANGED <<messages, current, written>>
                            \/ /\ \E v \in Values:
                                    /\ current' = [current EXCEPT ![self] = v]
                                    /\ written' = [written EXCEPT ![self] = Timestamp(written[self].number+1,self)]
                                    /\ retval' = [retval EXCEPT ![self] = "ok"]
                                    /\ seq' = [seq EXCEPT ![self] = 0]
                                    /\ history' = (history \union {[op|->"write", val|->v,t|->written'[self].number, pid|->self, seq|->seq'[self]]})
                               /\ UNCHANGED messages
                            \/ /\ messages' = (messages \union {Latest(current[self], written[self])})
                               /\ UNCHANGED <<history, current, written, retval, seq>>
                            \/ /\ \E m \in messages:
                                    IF lessthan(written[self], (m.t))
                                       THEN /\ current' = [current EXCEPT ![self] = m.val]
                                            /\ written' = [written EXCEPT ![self] = m.t]
                                            /\ seq' = [seq EXCEPT ![self] = 0]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED << current, written, 
                                                            seq >>
                               /\ UNCHANGED <<messages, history, retval>>
                            \/ /\ TRUE
                               /\ UNCHANGED <<messages, history, current, written, retval, seq>>
                         /\ pc' = [pc EXCEPT ![self] = "loop"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << steps, messages, history, current, 
                                         written, retval, seq >>
              /\ UNCHANGED << evt, method, value, rval >>

Role(self) == loop(self)

guard == /\ pc[0] = "guard"
         /\ steps = 0
         /\ pc' = [pc EXCEPT ![0] = "wh"]
         /\ UNCHANGED << steps, messages, history, current, written, retval, 
                         seq, evt, method, value, rval >>

wh == /\ pc[0] = "wh"
      /\ IF history /= {}
            THEN /\ pc' = [pc EXCEPT ![0] = "next"]
            ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED << steps, messages, history, current, written, retval, seq, 
                      evt, method, value, rval >>

next == /\ pc[0] = "next"
        /\ evt' = (  CHOOSE h \in history :
                   \A x \in history \ {h}:
                       \/ h.t < x.t
                       \/ /\ h.t = x.t
                          /\ h.pid < x.pid
                       \/ /\ h.t = x.t
                          /\ h.pid = x.pid
                          /\ h.seq < x.seq)
        /\ method' = evt'.op
        /\ value' = evt'.val
        /\ rval' = (IF method' = "read" THEN evt'.val ELSE "ok")
        /\ history' = history \ {evt'}
        /\ pc' = [pc EXCEPT ![0] = "wh"]
        /\ UNCHANGED << steps, messages, current, written, retval, seq >>

Serialize == guard \/ wh \/ next

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Serialize
           \/ (\E self \in Roles: Role(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Roles : WF_vars(Role(self))
        /\ WF_vars(Serialize)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-2369b331153387902ffff5fe6a475d5f

R == INSTANCE register

====
