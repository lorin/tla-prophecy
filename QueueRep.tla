(***************************************************************************)
(*                                                                         *)
(* Queue representation type (REP) from Herlihy & Wing 1990                *)
(*                                                                         *)
(***************************************************************************)
------------------------------ MODULE QueueRep ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT Values
CONSTANT Producers
CONSTANT Consumers
CONSTANT Nmax

null == CHOOSE x : x \notin Values

(*
--algorithm Rep {

variables rep = [back|->1, items|->[n \in 1..Nmax|->null]];

macro INC(x) { x := x+1 || rInd := x }
macro STORE(loc, val) { loc := val }
macro READ(ind) { rInd := ind }
macro SWAP(loc, val) { loc := val || rVal := loc }

procedure Enq(x)
variables i, rInd {
E1:  INC(rep.back);
     i := rInd;
E2:  STORE(rep.items[i], x);
E3:  return
}

procedure Deq()
variables i, x, range, rInd, rVal {
D1: while(TRUE) {
D2:   READ(rep.back);
D3:   range := rInd-1;
D4:   i := 1;
D5:   while(i<=range) {
D6:     SWAP(rep.items[i], null);
D7:     x := rVal;
        if(x /= null) {
D8:       rVal := x;
D9:       return
        };
D10:    i:= i+1
      }
    }
}

fair process (producer \in Producers) {
P1: with (item \in Values) {
    call Enq(item)
    }
}

fair process (consumer \in Consumers) {
C1: call Deq()
}
}
*)
\* BEGIN TRANSLATION
\* Procedure variable i of procedure Enq at line 27 col 11 changed to i_
\* Procedure variable rInd of procedure Enq at line 27 col 14 changed to rInd_
\* Procedure variable x of procedure Deq at line 35 col 14 changed to x_
CONSTANT defaultInitValue
VARIABLES rep, pc, stack, x, i_, rInd_, i, x_, range, rInd, rVal

vars == << rep, pc, stack, x, i_, rInd_, i, x_, range, rInd, rVal >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ rep = [back|->1, items|->[n \in 1..Nmax|->null]]
        (* Procedure Enq *)
        /\ x = [ self \in ProcSet |-> defaultInitValue]
        /\ i_ = [ self \in ProcSet |-> defaultInitValue]
        /\ rInd_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Deq *)
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        /\ x_ = [ self \in ProcSet |-> defaultInitValue]
        /\ range = [ self \in ProcSet |-> defaultInitValue]
        /\ rInd = [ self \in ProcSet |-> defaultInitValue]
        /\ rVal = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "P1"
                                        [] self \in Consumers -> "C1"]

E1(self) == /\ pc[self] = "E1"
            /\ /\ rInd_' = [rInd_ EXCEPT ![self] = rep.back]
               /\ rep' = [rep EXCEPT !.back = (rep.back)+1]
            /\ i_' = [i_ EXCEPT ![self] = rInd_'[self]]
            /\ pc' = [pc EXCEPT ![self] = "E2"]
            /\ UNCHANGED << stack, x, i, x_, range, rInd, rVal >>

E2(self) == /\ pc[self] = "E2"
            /\ rep' = [rep EXCEPT !.items[i_[self]] = x[self]]
            /\ pc' = [pc EXCEPT ![self] = "E3"]
            /\ UNCHANGED << stack, x, i_, rInd_, i, x_, range, rInd, rVal >>

E3(self) == /\ pc[self] = "E3"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ i_' = [i_ EXCEPT ![self] = Head(stack[self]).i_]
            /\ rInd_' = [rInd_ EXCEPT ![self] = Head(stack[self]).rInd_]
            /\ x' = [x EXCEPT ![self] = Head(stack[self]).x]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << rep, i, x_, range, rInd, rVal >>

Enq(self) == E1(self) \/ E2(self) \/ E3(self)

D1(self) == /\ pc[self] = "D1"
            /\ pc' = [pc EXCEPT ![self] = "D2"]
            /\ UNCHANGED << rep, stack, x, i_, rInd_, i, x_, range, rInd, rVal >>

D2(self) == /\ pc[self] = "D2"
            /\ rInd' = [rInd EXCEPT ![self] = rep.back]
            /\ pc' = [pc EXCEPT ![self] = "D3"]
            /\ UNCHANGED << rep, stack, x, i_, rInd_, i, x_, range, rVal >>

D3(self) == /\ pc[self] = "D3"
            /\ range' = [range EXCEPT ![self] = rInd[self]-1]
            /\ pc' = [pc EXCEPT ![self] = "D4"]
            /\ UNCHANGED << rep, stack, x, i_, rInd_, i, x_, rInd, rVal >>

D4(self) == /\ pc[self] = "D4"
            /\ i' = [i EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "D5"]
            /\ UNCHANGED << rep, stack, x, i_, rInd_, x_, range, rInd, rVal >>

D5(self) == /\ pc[self] = "D5"
            /\ IF i[self]<=range[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "D6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << rep, stack, x, i_, rInd_, i, x_, range, rInd, rVal >>

D6(self) == /\ pc[self] = "D6"
            /\ /\ rVal' = [rVal EXCEPT ![self] = rep.items[i[self]]]
               /\ rep' = [rep EXCEPT !.items[i[self]] = null]
            /\ pc' = [pc EXCEPT ![self] = "D7"]
            /\ UNCHANGED << stack, x, i_, rInd_, i, x_, range, rInd >>

D7(self) == /\ pc[self] = "D7"
            /\ x_' = [x_ EXCEPT ![self] = rVal[self]]
            /\ IF x_'[self] /= null
                  THEN /\ pc' = [pc EXCEPT ![self] = "D8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D10"]
            /\ UNCHANGED << rep, stack, x, i_, rInd_, i, range, rInd, rVal >>

D8(self) == /\ pc[self] = "D8"
            /\ rVal' = [rVal EXCEPT ![self] = x_[self]]
            /\ pc' = [pc EXCEPT ![self] = "D9"]
            /\ UNCHANGED << rep, stack, x, i_, rInd_, i, x_, range, rInd >>

D9(self) == /\ pc[self] = "D9"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
            /\ x_' = [x_ EXCEPT ![self] = Head(stack[self]).x_]
            /\ range' = [range EXCEPT ![self] = Head(stack[self]).range]
            /\ rInd' = [rInd EXCEPT ![self] = Head(stack[self]).rInd]
            /\ rVal' = [rVal EXCEPT ![self] = Head(stack[self]).rVal]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << rep, x, i_, rInd_ >>

D10(self) == /\ pc[self] = "D10"
             /\ i' = [i EXCEPT ![self] = i[self]+1]
             /\ pc' = [pc EXCEPT ![self] = "D5"]
             /\ UNCHANGED << rep, stack, x, i_, rInd_, x_, range, rInd, rVal >>

Deq(self) == D1(self) \/ D2(self) \/ D3(self) \/ D4(self) \/ D5(self)
                \/ D6(self) \/ D7(self) \/ D8(self) \/ D9(self)
                \/ D10(self)

P1(self) == /\ pc[self] = "P1"
            /\ \E item \in Values:
                 /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enq",
                                                             pc        |->  "Done",
                                                             i_        |->  i_[self],
                                                             rInd_     |->  rInd_[self],
                                                             x         |->  x[self] ] >>
                                                         \o stack[self]]
                    /\ x' = [x EXCEPT ![self] = item]
                 /\ i_' = [i_ EXCEPT ![self] = defaultInitValue]
                 /\ rInd_' = [rInd_ EXCEPT ![self] = defaultInitValue]
                 /\ pc' = [pc EXCEPT ![self] = "E1"]
            /\ UNCHANGED << rep, i, x_, range, rInd, rVal >>

producer(self) == P1(self)

C1(self) == /\ pc[self] = "C1"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Deq",
                                                     pc        |->  "Done",
                                                     i         |->  i[self],
                                                     x_        |->  x_[self],
                                                     range     |->  range[self],
                                                     rInd      |->  rInd[self],
                                                     rVal      |->  rVal[self] ] >>
                                                 \o stack[self]]
            /\ i' = [i EXCEPT ![self] = defaultInitValue]
            /\ x_' = [x_ EXCEPT ![self] = defaultInitValue]
            /\ range' = [range EXCEPT ![self] = defaultInitValue]
            /\ rInd' = [rInd EXCEPT ![self] = defaultInitValue]
            /\ rVal' = [rVal EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << rep, x, i_, rInd_ >>

consumer(self) == C1(self)

Next == (\E self \in ProcSet: Enq(self) \/ Deq(self))
           \/ (\E self \in Producers: producer(self))
           \/ (\E self \in Consumers: consumer(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Producers : WF_vars(producer(self)) /\ WF_vars(Enq(self))
        /\ \A self \in Consumers : WF_vars(consumer(self)) /\ WF_vars(Deq(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Thu Nov 08 17:05:10 PST 2018 by lhochstein
\* Created Wed Oct 24 18:53:25 PDT 2018 by lhochstein
