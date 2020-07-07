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
    
    
    methodLin = undef;
    valueLin = undef;
    rvalLin = undef;

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
    if current /= undef then 
        retval := current;
        
        \* linearization refinement mapping
        methodLin := "read";
        valueLin := current;
        rvalLin := retval;
        
        \* needed for sequential consistency refinement mapping
        seq := seq + 1;
        history := history \union {[op|->"read", val|->retval,t|->written.number, pid|->written.pid, seq|->seq]};
    end if;
end macro;

macro Write(val) begin
    current := val;
    written := Timestamp(written.number+1,self);
    retval := "ok";
    
    \* linearization refinement mapping
    methodLin := "write";
    valueLin := current;
    rvalLin := "ok";
    
    
    \* needed for sequential consistency refinement mapping
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
    methodSeq = undef;
    valueSeq = undef;
    rvalSeq = undef;

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
       methodSeq := evt.op;
       valueSeq := evt.val;
       rvalSeq := IF methodSeq = "read" THEN evt.val ELSE "ok";
       history := history \ {evt};
end while;
end process

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-91c040f3d12206094e7d6aafb298fc2d
VARIABLES steps, messages, history, methodLin, valueLin, rvalLin, pc

(* define statement *)
Timestamp(number, pid) == [number|->number, pid|->pid]
Latest(val, t) == [val|->val, t|->t]
lessthan(t1, t2) == LET n1 == t1.number
                        n2 == t2.number
                        pid1 == t1.pid
                        pid2 == t2.pid
                    IN (n1 < n2) \/ (n1=n2 /\ pid1<pid2)

VARIABLES current, written, retval, seq, evt, methodSeq, valueSeq, rvalSeq

vars == << steps, messages, history, methodLin, valueLin, rvalLin, pc, 
           current, written, retval, seq, evt, methodSeq, valueSeq, rvalSeq
        >>

ProcSet == (Roles) \cup {0}

Init == (* Global variables *)
        /\ steps = Steps
        /\ messages = {}
        /\ history = {}
        /\ methodLin = undef
        /\ valueLin = undef
        /\ rvalLin = undef
        (* Process Role *)
        /\ current = [self \in Roles |-> undef]
        /\ written = [self \in Roles |-> Timestamp(0, self)]
        /\ retval = [self \in Roles |-> undef]
        /\ seq = [self \in Roles |-> 0]
        (* Process Serialize *)
        /\ evt = undef
        /\ methodSeq = undef
        /\ valueSeq = undef
        /\ rvalSeq = undef
        /\ pc = [self \in ProcSet |-> CASE self \in Roles -> "loop"
                                        [] self = 0 -> "guard"]

loop(self) == /\ pc[self] = "loop"
              /\ IF steps > 0
                    THEN /\ steps' = steps - 1
                         /\ \/ /\ IF current[self] /= undef
                                     THEN /\ seq' = [seq EXCEPT ![self] = seq[self] + 1]
                                          /\ retval' = [retval EXCEPT ![self] = current[self]]
                                          /\ methodLin' = "read"
                                          /\ valueLin' = current[self]
                                          /\ rvalLin' = retval'[self]
                                          /\ history' = (history \union {[op|->"read", val|->retval'[self],t|->written[self].number, pid|->written[self].pid, seq|->seq'[self]]})
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << history, methodLin, 
                                                          valueLin, rvalLin, 
                                                          retval, seq >>
                               /\ UNCHANGED <<messages, current, written>>
                            \/ /\ \E v \in Values:
                                    /\ current' = [current EXCEPT ![self] = v]
                                    /\ written' = [written EXCEPT ![self] = Timestamp(written[self].number+1,self)]
                                    /\ retval' = [retval EXCEPT ![self] = "ok"]
                                    /\ methodLin' = "write"
                                    /\ valueLin' = current'[self]
                                    /\ rvalLin' = "ok"
                                    /\ seq' = [seq EXCEPT ![self] = 0]
                                    /\ history' = (history \union {[op|->"write", val|->v,t|->written'[self].number, pid|->self, seq|->seq'[self]]})
                               /\ UNCHANGED messages
                            \/ /\ messages' = (messages \union {Latest(current[self], written[self])})
                               /\ UNCHANGED <<history, methodLin, valueLin, rvalLin, current, written, retval, seq>>
                            \/ /\ \E m \in messages:
                                    IF lessthan(written[self], (m.t))
                                       THEN /\ current' = [current EXCEPT ![self] = m.val]
                                            /\ written' = [written EXCEPT ![self] = m.t]
                                            /\ seq' = [seq EXCEPT ![self] = 0]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED << current, written, 
                                                            seq >>
                               /\ UNCHANGED <<messages, history, methodLin, valueLin, rvalLin, retval>>
                            \/ /\ TRUE
                               /\ UNCHANGED <<messages, history, methodLin, valueLin, rvalLin, current, written, retval, seq>>
                         /\ pc' = [pc EXCEPT ![self] = "loop"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << steps, messages, history, methodLin, 
                                         valueLin, rvalLin, current, written, 
                                         retval, seq >>
              /\ UNCHANGED << evt, methodSeq, valueSeq, rvalSeq >>

Role(self) == loop(self)

guard == /\ pc[0] = "guard"
         /\ steps = 0
         /\ pc' = [pc EXCEPT ![0] = "wh"]
         /\ UNCHANGED << steps, messages, history, methodLin, valueLin, 
                         rvalLin, current, written, retval, seq, evt, 
                         methodSeq, valueSeq, rvalSeq >>

wh == /\ pc[0] = "wh"
      /\ IF history /= {}
            THEN /\ pc' = [pc EXCEPT ![0] = "next"]
            ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED << steps, messages, history, methodLin, valueLin, rvalLin, 
                      current, written, retval, seq, evt, methodSeq, valueSeq, 
                      rvalSeq >>

next == /\ pc[0] = "next"
        /\ evt' = (  CHOOSE h \in history :
                   \A x \in history \ {h}:
                       \/ h.t < x.t
                       \/ /\ h.t = x.t
                          /\ h.pid < x.pid
                       \/ /\ h.t = x.t
                          /\ h.pid = x.pid
                          /\ h.seq < x.seq)
        /\ methodSeq' = evt'.op
        /\ valueSeq' = evt'.val
        /\ rvalSeq' = (IF methodSeq' = "read" THEN evt'.val ELSE "ok")
        /\ history' = history \ {evt'}
        /\ pc' = [pc EXCEPT ![0] = "wh"]
        /\ UNCHANGED << steps, messages, methodLin, valueLin, rvalLin, current, 
                        written, retval, seq >>

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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-7fbc8d9469f76e907c21d58dd2928382

\*
\* Refinement mappings
\* 

RegLin == INSTANCE register WITH method<-methodLin, value<-valueLin, rval<-rvalLin
RegSeq == INSTANCE register WITH method<-methodSeq, value<-valueSeq, rval<-rvalSeq

====
