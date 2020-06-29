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
    method := "read";
    rval := current;
    seq := seq + 1;
    history := history \union {[op|->method, val|->rval,t|->written.number, pid|->self, seq|->seq]};
end macro;

macro Write(val) begin
    method := "write";
    current := val;
    written := [written EXCEPT !.number = @+1];
    rval := "ok";
    history := history \union {[op|->method, val|->val,t|->written.number, pid|->self, seq|->seq]};
end macro;

macro Send() begin
    method := "send";
    messages := messages \union {Latest(current, written)};
end macro;

macro Receive(val, ts) begin
    method := "receive";
    if lessthan(written, ts) then 
        current := val;
        written := ts;
    end if;
end macro;


fair process Role \in Roles
variables
    method = undef; 
    current = undef;
    written = Timestamp(0, self);
    rval = undef;
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
    op = undef;
    value = undef;
    evt = undef;

begin
guard: await steps = 0;
sloop: while history /= {} do
next:  evt := CHOOSE h \in history : 
            \A x \in history \ {h}:  
                \/ h.t < x.t 
                \/ /\ h.t = x.t
                   /\ h.pid < x.pid
                \/ /\ h.t = x.t 
                   /\ h.pid = x.pid 
                   /\ h.seq < x.seq;
       op := evt.op;
       value := evt.val;
       history := history \ {evt};
end while;
end process

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-183d7fca93b3623e821a6333e042517b
VARIABLES steps, messages, history, pc

(* define statement *)
Timestamp(number, pid) == [number|->number, pid|->pid]
Latest(val, t) == [val|->val, t|->t]
lessthan(t1, t2) == LET n1 == t1.number
                        n2 == t2.number
                        pid1 == t1.pid
                        pid2 == t2.pid
                    IN (n1 < n2) \/ (n1=n2 /\ pid1<pid2)

VARIABLES method, current, written, rval, seq, op, value, evt

vars == << steps, messages, history, pc, method, current, written, rval, seq, 
           op, value, evt >>

ProcSet == (Roles) \cup {0}

Init == (* Global variables *)
        /\ steps = Steps
        /\ messages = {}
        /\ history = {}
        (* Process Role *)
        /\ method = [self \in Roles |-> undef]
        /\ current = [self \in Roles |-> undef]
        /\ written = [self \in Roles |-> Timestamp(0, self)]
        /\ rval = [self \in Roles |-> undef]
        /\ seq = [self \in Roles |-> 0]
        (* Process Serialize *)
        /\ op = undef
        /\ value = undef
        /\ evt = undef
        /\ pc = [self \in ProcSet |-> CASE self \in Roles -> "loop"
                                        [] self = 0 -> "guard"]

loop(self) == /\ pc[self] = "loop"
              /\ IF steps > 0
                    THEN /\ steps' = steps - 1
                         /\ \/ /\ method' = [method EXCEPT ![self] = "read"]
                               /\ rval' = [rval EXCEPT ![self] = current[self]]
                               /\ seq' = [seq EXCEPT ![self] = seq[self] + 1]
                               /\ history' = (history \union {[op|->method'[self], val|->rval'[self],t|->written[self].number, pid|->self, seq|->seq'[self]]})
                               /\ UNCHANGED <<messages, current, written>>
                            \/ /\ \E v \in Values:
                                    /\ method' = [method EXCEPT ![self] = "write"]
                                    /\ current' = [current EXCEPT ![self] = v]
                                    /\ written' = [written EXCEPT ![self] = [written[self] EXCEPT !.number = @+1]]
                                    /\ rval' = [rval EXCEPT ![self] = "ok"]
                                    /\ history' = (history \union {[op|->method'[self], val|->v,t|->written'[self].number, pid|->self, seq|->seq[self]]})
                               /\ UNCHANGED <<messages, seq>>
                            \/ /\ method' = [method EXCEPT ![self] = "send"]
                               /\ messages' = (messages \union {Latest(current[self], written[self])})
                               /\ UNCHANGED <<history, current, written, rval, seq>>
                            \/ /\ \E m \in messages:
                                    /\ method' = [method EXCEPT ![self] = "receive"]
                                    /\ IF lessthan(written[self], (m.t))
                                          THEN /\ current' = [current EXCEPT ![self] = m.val]
                                               /\ written' = [written EXCEPT ![self] = m.t]
                                          ELSE /\ TRUE
                                               /\ UNCHANGED << current, 
                                                               written >>
                               /\ UNCHANGED <<messages, history, rval, seq>>
                            \/ /\ TRUE
                               /\ UNCHANGED <<messages, history, method, current, written, rval, seq>>
                         /\ pc' = [pc EXCEPT ![self] = "loop"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << steps, messages, history, method, 
                                         current, written, rval, seq >>
              /\ UNCHANGED << op, value, evt >>

Role(self) == loop(self)

guard == /\ pc[0] = "guard"
         /\ steps = 0
         /\ pc' = [pc EXCEPT ![0] = "sloop"]
         /\ UNCHANGED << steps, messages, history, method, current, written, 
                         rval, seq, op, value, evt >>

sloop == /\ pc[0] = "sloop"
         /\ IF history /= {}
               THEN /\ pc' = [pc EXCEPT ![0] = "next"]
               ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
         /\ UNCHANGED << steps, messages, history, method, current, written, 
                         rval, seq, op, value, evt >>

next == /\ pc[0] = "next"
        /\ evt' = (  CHOOSE h \in history :
                   \A x \in history \ {h}:
                       \/ h.t < x.t
                       \/ /\ h.t = x.t
                          /\ h.pid < x.pid
                       \/ /\ h.t = x.t
                          /\ h.pid = x.pid
                          /\ h.seq < x.seq)
        /\ op' = evt'.op
        /\ value' = evt'.val
        /\ history' = history \ {evt'}
        /\ pc' = [pc EXCEPT ![0] = "sloop"]
        /\ UNCHANGED << steps, messages, method, current, written, rval, seq >>

Serialize == guard \/ sloop \/ next

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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-255a372d98ce3ac2e2200346cfc93efc


====
