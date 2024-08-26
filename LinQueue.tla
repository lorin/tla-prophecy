---------- MODULE LinQueue ----------
(************************************)
(* Model for a linearizable queue   *)
(************************************)
EXTENDS Sequences

CONSTANTS item, producer, consumer

null == CHOOSE null: null \notin item \union {"ok"}

(*
--algorithm LinQueue {

variable q = <<>>;

process (prod \in producer) 
variables x=null, rval=null; {
E1: with (arg \in item) { \* invocation starts
        x := arg
    };
E2: q := Append(q, x); \* takes effect
E3: rval := "ok"; \* invocation completes
}

process (con \in consumer) 
variable tmp=null, rval=null; {
D1: skip; \* Invocation starts, nothing to do
D2: await q # <<>>;
    tmp := Head(q); \* takes effect
    q := Tail(q);
D3: rval := tmp; \* invocation completes
}


}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "137f5198" /\ chksum(tla) = "e53fa929")
\* Process variable rval of process prod at line 17 col 19 changed to rval_
VARIABLES pc, q, x, rval_, tmp, rval

vars == << pc, q, x, rval_, tmp, rval >>

ProcSet == (producer) \cup (consumer)

Init == (* Global variables *)
        /\ q = <<>>
        (* Process prod *)
        /\ x = [self \in producer |-> null]
        /\ rval_ = [self \in producer |-> null]
        (* Process con *)
        /\ tmp = [self \in consumer |-> null]
        /\ rval = [self \in consumer |-> null]
        /\ pc = [self \in ProcSet |-> CASE self \in producer -> "E1"
                                        [] self \in consumer -> "D1"]

E1(self) == /\ pc[self] = "E1"
            /\ \E arg \in item:
                 x' = [x EXCEPT ![self] = arg]
            /\ pc' = [pc EXCEPT ![self] = "E2"]
            /\ UNCHANGED << q, rval_, tmp, rval >>

E2(self) == /\ pc[self] = "E2"
            /\ q' = Append(q, x[self])
            /\ pc' = [pc EXCEPT ![self] = "E3"]
            /\ UNCHANGED << x, rval_, tmp, rval >>

E3(self) == /\ pc[self] = "E3"
            /\ rval_' = [rval_ EXCEPT ![self] = "ok"]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << q, x, tmp, rval >>

prod(self) == E1(self) \/ E2(self) \/ E3(self)

D1(self) == /\ pc[self] = "D1"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "D2"]
            /\ UNCHANGED << q, x, rval_, tmp, rval >>

D2(self) == /\ pc[self] = "D2"
            /\ q # <<>>
            /\ tmp' = [tmp EXCEPT ![self] = Head(q)]
            /\ q' = Tail(q)
            /\ pc' = [pc EXCEPT ![self] = "D3"]
            /\ UNCHANGED << x, rval_, rval >>

D3(self) == /\ pc[self] = "D3"
            /\ rval' = [rval EXCEPT ![self] = tmp[self]]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << q, x, rval_, tmp >>

con(self) == D1(self) \/ D2(self) \/ D3(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in producer: prod(self))
           \/ (\E self \in consumer: con(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
