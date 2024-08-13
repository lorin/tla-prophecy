(***************************************************************************)
(* Queue representation type (REP) from Herlihy & Wing 1990                *)
(* with prophecy variables                                                 *)
(***************************************************************************)
------------------------------ MODULE QueueRepP ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT Values
CONSTANT Producers
CONSTANT Consumers
CONSTANT Nmax

null == CHOOSE x : x \notin Values

CONSTANT defaultInitValue
VARIABLES pc, rep, stack, x, i_, preINC, i, x_, range, rInd, rVal, p

vars == << pc, rep, stack, x, i_, preINC, i, x_, range, rInd, rVal, p >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ rep = [back|->1, items|->[n \in 1..Nmax|->null]]
        (* Procedure Enq *)
        /\ x = [ self \in ProcSet |-> defaultInitValue]
        /\ i_ = [ self \in ProcSet |-> defaultInitValue]
        /\ preINC = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Deq *)
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        /\ x_ = [ self \in ProcSet |-> defaultInitValue]
        /\ range = [ self \in ProcSet |-> defaultInitValue]
        /\ rInd = [ self \in ProcSet |-> defaultInitValue]
        /\ rVal = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "P1"
                                        [] self \in Consumers -> "C1"]
        /\ p = <<>>

E1(self) == /\ pc[self] = "E1"
            /\ /\ preINC' = [preINC EXCEPT ![self] = rep.back]
               /\ rep' = [rep EXCEPT !.back = (rep.back)+1]
            /\ i_' = [i_ EXCEPT ![self] = preINC'[self]]
            /\ pc' = [pc EXCEPT ![self] = "E2"]
            /\ UNCHANGED << stack, x, i, x_, range, rInd, rVal >>
            /\ \E v \in Values: p' = <<v>> \o p

E2(self) == /\ pc[self] = "E2"
            /\ rep' = [rep EXCEPT !.items[i_[self]] = x[self]]
            /\ pc' = [pc EXCEPT ![self] = "E3"]
            /\ UNCHANGED << stack, x, i_, preINC, i, x_, range, rInd, rVal >>
            /\ UNCHANGED p

E3(self) == /\ pc[self] = "E3"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ i_' = [i_ EXCEPT ![self] = Head(stack[self]).i_]
            /\ preINC' = [preINC EXCEPT ![self] = Head(stack[self]).preINC]
            /\ x' = [x EXCEPT ![self] = Head(stack[self]).x]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << rep, i, x_, range, rInd, rVal >>
            /\ UNCHANGED p

Enq(self) == E1(self) \/ E2(self) \/ E3(self)

D1(self) == /\ pc[self] = "D1"
            /\ pc' = [pc EXCEPT ![self] = "D2"]
            /\ UNCHANGED << rep, stack, x, i_, preINC, i, x_, range, rInd, 
                            rVal >>
            /\ UNCHANGED p

D2(self) == /\ pc[self] = "D2"
            /\ rInd' = [rInd EXCEPT ![self] = rep.back]
            /\ pc' = [pc EXCEPT ![self] = "D3"]
            /\ UNCHANGED << rep, stack, x, i_, preINC, i, x_, range, rVal >>
            /\ UNCHANGED p

D3(self) == /\ pc[self] = "D3"
            /\ range' = [range EXCEPT ![self] = rInd[self]-1]
            /\ pc' = [pc EXCEPT ![self] = "D4"]
            /\ UNCHANGED << rep, stack, x, i_, preINC, i, x_, rInd, rVal >>
            /\ UNCHANGED p

D4(self) == /\ pc[self] = "D4"
            /\ i' = [i EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "D5"]
            /\ UNCHANGED << rep, stack, x, i_, preINC, x_, range, rInd, rVal >>
            /\ UNCHANGED p

D5(self) == /\ pc[self] = "D5"
            /\ IF i[self]<=range[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "D6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << rep, stack, x, i_, preINC, i, x_, range, rInd, 
                            rVal >>
            /\ UNCHANGED p

D6(self) == /\ pc[self] = "D6"
            /\ /\ rVal' = [rVal EXCEPT ![self] = rep.items[i[self]]]
               /\ rep' = [rep EXCEPT !.items[i[self]] = null]
            /\ pc' = [pc EXCEPT ![self] = "D7"]
            /\ UNCHANGED << stack, x, i_, preINC, i, x_, range, rInd >>
            /\ UNCHANGED p

D7(self) == /\ pc[self] = "D7"
            /\ x_' = [x_ EXCEPT ![self] = rVal[self]]
            /\ IF x_'[self] /= null
                  THEN /\ pc' = [pc EXCEPT ![self] = "D8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D10"]
            /\ UNCHANGED << rep, stack, x, i_, preINC, i, range, rInd, rVal >>
            /\ UNCHANGED p

D8(self) == /\ pc[self] = "D8"
            /\ rVal' = [rVal EXCEPT ![self] = x_[self]]
            /\ pc' = [pc EXCEPT ![self] = "D9"]
            /\ UNCHANGED << rep, stack, x, i_, preINC, i, x_, range, rInd >>
            /\ UNCHANGED p

D9(self) == /\ pc[self] = "D9"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
            /\ x_' = [x_ EXCEPT ![self] = Head(stack[self]).x_]
            /\ range' = [range EXCEPT ![self] = Head(stack[self]).range]
            /\ rInd' = [rInd EXCEPT ![self] = Head(stack[self]).rInd]
            /\ rVal' = [rVal EXCEPT ![self] = Head(stack[self]).rVal]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << rep, x, i_, preINC >>
            /\ UNCHANGED p

D10(self) == /\ pc[self] = "D10"
             /\ i' = [i EXCEPT ![self] = i[self]+1]
             /\ pc' = [pc EXCEPT ![self] = "D5"]
             /\ UNCHANGED << rep, stack, x, i_, preINC, x_, range, rInd, rVal >>
             /\ UNCHANGED p

Deq(self) == D1(self) \/ D2(self) \/ D3(self) \/ D4(self) \/ D5(self)
                \/ D6(self) \/ D7(self) \/ D8(self) \/ D9(self)
                \/ D10(self)

P1(self) == /\ pc[self] = "P1"
            /\ \E item \in Values:
                 /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enq",
                                                             pc        |->  "Done",
                                                             i_        |->  i_[self],
                                                             preINC    |->  preINC[self],
                                                             x         |->  x[self] ] >>
                                                         \o stack[self]]
                    /\ x' = [x EXCEPT ![self] = item]
                 /\ i_' = [i_ EXCEPT ![self] = defaultInitValue]
                 /\ preINC' = [preINC EXCEPT ![self] = defaultInitValue]
                 /\ pc' = [pc EXCEPT ![self] = "E1"]
            /\ UNCHANGED << rep, i, x_, range, rInd, rVal >>
            /\ UNCHANGED p

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
            /\ UNCHANGED << rep, x, i_, preINC >>
            /\ UNCHANGED p

consumer(self) == C1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: Enq(self) \/ Deq(self))
           \/ (\E self \in Producers: producer(self))
           \/ (\E self \in Consumers: consumer(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

Mapping ==
    INSTANCE Queue WITH 
        Qmax <- Nmax,
        items <- p,
        Val <- Values,
        state <- "ready",
        x <- null

Refinement == Mapping!Spec



=============================================================================
\* Modification History
\* Last modified Thu Nov 08 17:28:50 PST 2018 by lhochstein
\* Created Wed Oct 24 18:53:25 PDT 2018 by lhochstein
