-------------------------- MODULE QueueRefinement --------------------------
EXTENDS Naturals, Sequences

CONSTANT Values
CONSTANT Producers
CONSTANT Consumers

null == CHOOSE x : x \notin Values


\* Procedure variable rInd of procedure Enq at line 45 col 14 changed to rInd_
\* Procedure variable x of procedure Deq at line 54 col 14 changed to x_
CONSTANT defaultInitValue
VARIABLES rep, pc, stack, x, j, rInd_, i, x_, range, rInd, rVal

vars == << rep, pc, stack, x, j, rInd_, i, x_, range, rInd, rVal >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ rep = [back|->1, items|->[n \in Nat|->null]]
        (* Procedure Enq *)
        /\ x = [ self \in ProcSet |-> defaultInitValue]
        /\ j = [ self \in ProcSet |-> defaultInitValue]
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
            /\ pc' = [pc EXCEPT ![self] = "E2"]
            /\ UNCHANGED << stack, x, j, i, x_, range, rInd, rVal >>

E2(self) == /\ pc[self] = "E2"
            /\ j' = [j EXCEPT ![self] = rInd_[self]]
            /\ pc' = [pc EXCEPT ![self] = "E3"]
            /\ UNCHANGED << rep, stack, x, rInd_, i, x_, range, rInd, rVal >>

E3(self) == /\ pc[self] = "E3"
            /\ rep' = [rep EXCEPT !.items[j[self]] = x[self]]
            /\ pc' = [pc EXCEPT ![self] = "E4"]
            /\ UNCHANGED << stack, x, j, rInd_, i, x_, range, rInd, rVal >>

E4(self) == /\ pc[self] = "E4"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ j' = [j EXCEPT ![self] = Head(stack[self]).j]
            /\ rInd_' = [rInd_ EXCEPT ![self] = Head(stack[self]).rInd_]
            /\ x' = [x EXCEPT ![self] = Head(stack[self]).x]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << rep, i, x_, range, rInd, rVal >>

Enq(self) == E1(self) \/ E2(self) \/ E3(self) \/ E4(self)

D1(self) == /\ pc[self] = "D1"
            /\ pc' = [pc EXCEPT ![self] = "D2"]
            /\ UNCHANGED << rep, stack, x, j, rInd_, i, x_, range, rInd, rVal >>

D2(self) == /\ pc[self] = "D2"
            /\ rInd' = [rInd EXCEPT ![self] = rep.back]
            /\ pc' = [pc EXCEPT ![self] = "D3"]
            /\ UNCHANGED << rep, stack, x, j, rInd_, i, x_, range, rVal >>

D3(self) == /\ pc[self] = "D3"
            /\ range' = [range EXCEPT ![self] = rInd[self]-1]
            /\ pc' = [pc EXCEPT ![self] = "D4"]
            /\ UNCHANGED << rep, stack, x, j, rInd_, i, x_, rInd, rVal >>

D4(self) == /\ pc[self] = "D4"
            /\ i' = [i EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "D5"]
            /\ UNCHANGED << rep, stack, x, j, rInd_, x_, range, rInd, rVal >>

D5(self) == /\ pc[self] = "D5"
            /\ IF (i[self]<=range[self])
                  THEN /\ pc' = [pc EXCEPT ![self] = "D6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << rep, stack, x, j, rInd_, i, x_, range, rInd, rVal >>

D6(self) == /\ pc[self] = "D6"
            /\ /\ rVal' = [rVal EXCEPT ![self] = rep.items[i[self]]]
               /\ rep' = [rep EXCEPT !.items[i[self]] = null]
            /\ pc' = [pc EXCEPT ![self] = "D7"]
            /\ UNCHANGED << stack, x, j, rInd_, i, x_, range, rInd >>

D7(self) == /\ pc[self] = "D7"
            /\ x_' = [x_ EXCEPT ![self] = rVal[self]]
            /\ IF x_'[self] = null
                  THEN /\ pc' = [pc EXCEPT ![self] = "D8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D10"]
            /\ UNCHANGED << rep, stack, x, j, rInd_, i, range, rInd, rVal >>

D8(self) == /\ pc[self] = "D8"
            /\ rVal' = [rVal EXCEPT ![self] = x_[self]]
            /\ pc' = [pc EXCEPT ![self] = "D9"]
            /\ UNCHANGED << rep, stack, x, j, rInd_, i, x_, range, rInd >>

D9(self) == /\ pc[self] = "D9"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
            /\ x_' = [x_ EXCEPT ![self] = Head(stack[self]).x_]
            /\ range' = [range EXCEPT ![self] = Head(stack[self]).range]
            /\ rInd' = [rInd EXCEPT ![self] = Head(stack[self]).rInd]
            /\ rVal' = [rVal EXCEPT ![self] = Head(stack[self]).rVal]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << rep, x, j, rInd_ >>

D10(self) == /\ pc[self] = "D10"
             /\ i' = [i EXCEPT ![self] = i[self]+1]
             /\ pc' = [pc EXCEPT ![self] = "D5"]
             /\ UNCHANGED << rep, stack, x, j, rInd_, x_, range, rInd, rVal >>

Deq(self) == D1(self) \/ D2(self) \/ D3(self) \/ D4(self) \/ D5(self)
                \/ D6(self) \/ D7(self) \/ D8(self) \/ D9(self)
                \/ D10(self)

P1(self) == /\ pc[self] = "P1"
            /\ \E item \in Values:
                 /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enq",
                                                             pc        |->  "Done",
                                                             j         |->  j[self],
                                                             rInd_     |->  rInd_[self],
                                                             x         |->  x[self] ] >>
                                                         \o stack[self]]
                    /\ x' = [x EXCEPT ![self] = item]
                 /\ j' = [j EXCEPT ![self] = defaultInitValue]
                 /\ rInd_' = [rInd_ EXCEPT ![self] = defaultInitValue]
                 /\ pc' = [pc EXCEPT ![self] = "E1"]
            /\ UNCHANGED << rep, i, x_, range, rInd, rVal >>

p(self) == P1(self)

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
            /\ UNCHANGED << rep, x, j, rInd_ >>

c(self) == C1(self)

Next == (\E self \in ProcSet: Enq(self) \/ Deq(self))
           \/ (\E self \in Producers: p(self))
           \/ (\E self \in Consumers: c(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

Q == INSTANCE Queue WITH items<-SelectSeq(rep.items, LAMBDA item: item /= null)

=============================================================================
\* Modification History
\* Last modified Sat Oct 27 14:23:00 PDT 2018 by lhochstein
\* Created Sat Oct 27 12:02:21 PDT 2018 by lhochstein
