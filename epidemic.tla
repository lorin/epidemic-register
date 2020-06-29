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
    history := history \union [op|->method, val|->rval,t|->written.number, pid|->self, seq|->seq];
end macro;

macro Write(val) begin
    method := "write";
    current := val;
    written := [written EXCEPT !.number = @+1];
    rval := "ok";
    history := history \union [op|->method, val|->val,t|->written.number, pid|->self, seq|->seq];
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
\* Each time it's going to randomly choose whether to read, write, send, receive, or do nothing

loop: while steps > 0 do 
body: steps := steps - 1;
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
    method = undef;
    value = undef;
    e = undef;

begin
guard: await steps = 0;
sloop: while history /= {} do
next:  e := CHOOSE h \in history : 
            \A x \in history \ {h}:  
                \/ h.t < x.t 
                \/ /\ h.t = x.t
                   /\ h.pid < x.pid
                \/ /\ h.t = x.t 
                   /\ h.pid = x.pid 
                   /\ h.seq < x.seq;
       method := e.op;
       value := e.val;
       history := history \ {e};
end while;
end process

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-a44d882e7ef2d77474a0e26ac1d0a8d4
\* Process variable method of process Role at line 60 col 5 changed to method_
VARIABLES steps, messages, history, pc

(* define statement *)
Timestamp(number, pid) == [number|->number, pid|->pid]
Latest(val, t) == [val|->val, t|->t]
lessthan(t1, t2) == LET n1 == t1.number
                        n2 == t2.number
                        pid1 == t1.pid
                        pid2 == t2.pid
                    IN (n1 < n2) \/ (n1=n2 /\ pid1<pid2)

VARIABLES method_, current, written, rval, seq, method, value, e

vars == << steps, messages, history, pc, method_, current, written, rval, seq, 
           method, value, e >>

ProcSet == (Roles) \cup {0}

Init == (* Global variables *)
        /\ steps = Steps
        /\ messages = {}
        /\ history = {}
        (* Process Role *)
        /\ method_ = [self \in Roles |-> undef]
        /\ current = [self \in Roles |-> undef]
        /\ written = [self \in Roles |-> Timestamp(0, self)]
        /\ rval = [self \in Roles |-> undef]
        /\ seq = [self \in Roles |-> 0]
        (* Process Serialize *)
        /\ method = undef
        /\ value = undef
        /\ e = undef
        /\ pc = [self \in ProcSet |-> CASE self \in Roles -> "loop"
                                        [] self = 0 -> "guard"]

loop(self) == /\ pc[self] = "loop"
              /\ IF steps > 0
                    THEN /\ pc' = [pc EXCEPT ![self] = "body"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << steps, messages, history, method_, current, 
                              written, rval, seq, method, value, e >>

body(self) == /\ pc[self] = "body"
              /\ steps' = steps - 1
              /\ \/ /\ method_' = [method_ EXCEPT ![self] = "read"]
                    /\ rval' = [rval EXCEPT ![self] = current[self]]
                    /\ seq' = [seq EXCEPT ![self] = seq[self] + 1]
                    /\ history' = (history \union [op|->method_'[self], val|->rval'[self],t|->written[self].number, pid|->self, seq|->seq'[self]])
                    /\ UNCHANGED <<messages, current, written>>
                 \/ /\ \E v \in Values:
                         /\ method_' = [method_ EXCEPT ![self] = "write"]
                         /\ current' = [current EXCEPT ![self] = v]
                         /\ written' = [written EXCEPT ![self] = [written[self] EXCEPT !.number = @+1]]
                         /\ rval' = [rval EXCEPT ![self] = "ok"]
                         /\ history' = (history \union [op|->method_'[self], val|->v,t|->written'[self].number, pid|->self, seq|->seq[self]])
                    /\ UNCHANGED <<messages, seq>>
                 \/ /\ method_' = [method_ EXCEPT ![self] = "send"]
                    /\ messages' = (messages \union {Latest(current[self], written[self])})
                    /\ UNCHANGED <<history, current, written, rval, seq>>
                 \/ /\ \E m \in messages:
                         /\ method_' = [method_ EXCEPT ![self] = "receive"]
                         /\ IF lessthan(written[self], (m.t))
                               THEN /\ current' = [current EXCEPT ![self] = m.val]
                                    /\ written' = [written EXCEPT ![self] = m.t]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << current, written >>
                    /\ UNCHANGED <<messages, history, rval, seq>>
                 \/ /\ TRUE
                    /\ UNCHANGED <<messages, history, method_, current, written, rval, seq>>
              /\ pc' = [pc EXCEPT ![self] = "loop"]
              /\ UNCHANGED << method, value, e >>

Role(self) == loop(self) \/ body(self)

guard == /\ pc[0] = "guard"
         /\ steps = 0
         /\ pc' = [pc EXCEPT ![0] = "sloop"]
         /\ UNCHANGED << steps, messages, history, method_, current, written, 
                         rval, seq, method, value, e >>

sloop == /\ pc[0] = "sloop"
         /\ IF history /= {}
               THEN /\ pc' = [pc EXCEPT ![0] = "next"]
               ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
         /\ UNCHANGED << steps, messages, history, method_, current, written, 
                         rval, seq, method, value, e >>

next == /\ pc[0] = "next"
        /\ e' = (CHOOSE h \in history :
                 \A x \in history \ {h}:
                     \/ h.t < x.t
                     \/ /\ h.t = x.t
                        /\ h.pid < x.pid
                     \/ /\ h.t = x.t
                        /\ h.pid = x.pid
                        /\ h.seq < x.seq)
        /\ method' = e'.op
        /\ value' = e'.val
        /\ history' = history \ {e'}
        /\ pc' = [pc EXCEPT ![0] = "sloop"]
        /\ UNCHANGED << steps, messages, method_, current, written, rval, seq >>

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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-73ff11a56710b0f7fecb9a3454cce904


====
