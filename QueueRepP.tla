----------------------------- MODULE QueueRepP -----------------------------
EXTENDS QueueRepPP

VARIABLE p, ord, ordP, itemsBar

varsP == <<vars, p, ordP, ord, itemsBar>>


(*
p is the prophecy variable

ordP is a prediction of the ordering of when the producer enqueues
take effect. It is derived from p. 

ord is the ordering of when producer enqueues take effect.

itemsBar is the refinement mapping

*)

\* Sequence that represents the order in which the producer process's values
RECURSIVE Ordering(_, _, _, _, _, _, _, _, _, _, _, _, _)
Ordering(po, ordo, repo, pco, stacko, xo, i_o, rInd_o, io, x_o, rangeo, rIndo, rValo) == 
    LET consumersRemaining == {co \in Consumers : \/ pco[co] \in {"C1", "D1", "D2", "D3", "D4", "D5", "D6", "D10"}
                                                  \/ pco[co]="D7" => rValo[co] = null }
        self == po[1]
    IN IF consumersRemaining = {} \/ po = << >> THEN ordo
    ELSE
CASE pco[self] = "E1" -> Ordering(Tail(po), ordo, [repo EXCEPT !.back = (repo.back)+1], [pco EXCEPT ![self] = "E2"],
                                  stacko, xo, i_o, [rInd_o EXCEPT ![self] = repo.back], io, x_o, rangeo, rIndo, rValo)
[] pco[self] = "E2" -> Ordering(Tail(po), ordo, repo, [pco EXCEPT ![self] = "E3"], stacko, xo, [i_o EXCEPT ![self] = rInd_o[self]], rInd_o, io, x_o, rangeo, rIndo, rValo)
[] pco[self] = "E3" -> Ordering(Tail(po), ordo, [repo EXCEPT !.items[i_o[self]] = xo[self]], [pco EXCEPT ![self] = "E4"], stacko, xo, i_o, rInd_o, io, x_o, rangeo, rIndo, rValo)
[] pco[self] = "E4" -> Ordering(Tail(po), ordo, repo, [pco EXCEPT ![self] = Head(stacko[self]).pc], [stacko EXCEPT ![self] = Tail(stacko[self])],
                                xo, [i_o EXCEPT ![self] = Head(stacko[self]).i_o],
                                [rInd_o EXCEPT ![self] = Head(stacko[self]).rInd_o], io, [xo EXCEPT ![self] = Head(stacko[self]).x], rangeo, rIndo, rValo)
[] pco[self] = "D1" -> Ordering(Tail(po), ordo, repo, [pco EXCEPT ![self] = "D2"], stacko, xo, i_o, rInd_o, io, x_o, rangeo, rIndo, rValo)
[] pco[self] = "D2" -> Ordering(Tail(po), ordo, repo, [pco EXCEPT ![self] = "D3"], stacko, xo, i_o, rInd_o, io, x_o, rangeo, [rIndo EXCEPT ![self] = repo.back], rValo)
[] pco[self] = "D3" -> Ordering(Tail(po), ordo, repo, [pco EXCEPT ![self] = "D4"], stacko, xo, i_o, rInd_o, io, x_o, [rangeo EXCEPT ![self] = rIndo[self]-1], rIndo, rValo)
[] pco[self] = "D4" -> Ordering(Tail(po), ordo, repo, [pco EXCEPT ![self] = "D5"], stacko, xo, i_o, rInd_o, [io EXCEPT ![self] = 1], x_o, rangeo, rIndo, rValo)
[] pco[self] = "D5" -> Ordering(Tail(po), ordo, repo, IF (io[self]<=rangeo[self])
                                                      THEN [pco EXCEPT ![self] = "D6"]
                                                      ELSE [pco EXCEPT ![self] = "D1"], stacko, xo, i_o, rInd_o, io, x_o, rangeo, rIndo, rValo)
[] pco[self] = "D6" -> Ordering(Tail(po),
                                IF repo.items[io[self]] = null THEN ordo
                                ELSE LET prod == CHOOSE prod \in Producers : i_o[prod] = io[self]
                                IN Append(ordo, prod),
                                [repo EXCEPT !.items[io[self]] = null],
                                [pco EXCEPT ![self] = "D7"],
                                stacko, xo, i_o, rInd_o, io, x_o, rangeo, rIndo,
                                [rValo EXCEPT ![self] = repo.items[io[self]]])
[] pco[self] = "D7" -> LET x_p == [x_o EXCEPT ![self] = rValo[self]] 
                       IN Ordering(Tail(po), ordo, repo, IF x_p[self] /= null THEN [pco EXCEPT ![self] = "D8"] ELSE  [pco EXCEPT ![self] = "D10"],
                                   stacko, xo, i_o, rInd_o, io, x_p, rangeo, rIndo, rValo)
[] pco[self] = "D8" -> Ordering(Tail(po), ordo, repo, [pco EXCEPT ![self] = "D9"], stacko, xo, i_o, rInd_o, io, x_o, rangeo, rIndo, [rValo EXCEPT ![self] = x_o[self]])
[] pco[self] = "D9" -> Ordering(Tail(po), ordo, repo,
                                [pco EXCEPT ![self] = Head(stacko[self]).pc],
                                [stacko EXCEPT ![self] = Tail(stacko[self])],
                                xo, i_o, rInd_o,
                                [io EXCEPT ![self] = Head(stacko[self]).i],
                                [x_o EXCEPT ![self] = Head(stacko[self]).x_o],
                                [rangeo EXCEPT ![self] = Head(stacko[self]).range],
                                [rIndo EXCEPT ![self] = Head(stacko[self]).rInd],
                                [rValo EXCEPT ![self] = Head(stacko[self]).rVal])
[] pco[self] = "D10" -> Ordering(Tail(po), ordo, repo, [pco EXCEPT ![self] = "D5"], stacko, xo, i_o, rInd_o, [io EXCEPT ![self] = io[self]+1], x_o, rangeo, rIndo, rValo)


[] pco[self] = "P1" -> Ordering(Tail(po), ordo, repo, [pco EXCEPT ![self] = "E1"],
                        [stacko EXCEPT ![self] = << [ procedure |->  "Enq",
                                                     pc        |->  "Done",
                                                     i_        |->  i_o[self],
                                                     rInd_     |->  rInd_o[self],
                                                     x         |->  xo[self] ] >>
                                                 \o stacko[self]],
                        LET item == CHOOSE item \in Values : TRUE IN [xo EXCEPT ![self] = item],
                        [i_o EXCEPT ![self] = defaultInitValue],
                        [rInd_o EXCEPT ![self] = defaultInitValue], io, x_o, rangeo, rIndo, rValo)


[] pco[self] = "C1" -> Ordering(Tail(po), ordo, repo, pco,
                        [stacko EXCEPT ![self] = << [ procedure |->  "Deq",
                                                     pc        |->  "Done",
                                                     i         |->  io[self],
                                                     x_        |->  x_o[self],
                                                     range     |->  rangeo[self],
                                                     rInd      |->  rIndo[self],
                                                     rVal      |->  rValo[self] ] >> \o stacko[self]],
                             xo, i_o, rInd_o,
                             [io EXCEPT ![self] = defaultInitValue],
                             [x_o EXCEPT ![self] = defaultInitValue],
                             [rangeo EXCEPT ![self] = defaultInitValue],
                             [rIndo EXCEPT ![self] = defaultInitValue],
                             [rValo EXCEPT ![self] = defaultInitValue])

[] pco[self] = "Done" -> Ordering(Tail(po), ordo, repo, pco, stacko, xo, i_o, rInd_o, io, x_o, rangeo, rIndo, rValo)


InitP == /\ Init
         /\ (p \in [Dom->Pi])
         /\ ord = << >>
         /\ ordP = Ordering(p, ord, rep, pc, stack, x, i_, rInd, i, x_, range, rInd, rVal)
         /\ itemsBar = << >>

TypeOK == /\ p \in [Dom->Pi]
          /\ ordP \in UNION({[1..N -> Producers] : N \in 1..Cardinality(Producers)})
          /\ ord \in UNION({[1..N -> Producers] : N \in 1..Cardinality(Producers)})
          /\ itemsBar \in UNION({[1..N -> Values] : N \in 1..Cardinality(Producers)})
          
          
\* True if sp is a prefix of s
IsPrefixOf(sp,s) == /\ Len(sp) <= Len(s)
                    /\ sp = SubSeq(s, 1, Len(sp))

\* We take effect at E1 if we are next in line to take effect
RefinementE1(self) == LET ordAndSelf == Append(ord,self)
                      IN IF IsPrefixOf(ordAndSelf, ordP)
                         THEN /\ ord' = ordAndSelf
                              /\ itemsBar' = Append(itemsBar, x[self])
                         ELSE UNCHANGED <<ord, itemsBar>>

\* We take effect at E3 if we have not yet taken effect
RefinementE3(self) == LET alreadyTakenEffect == \E j \in DOMAIN ord : ord[j] = self
                      IN IF alreadyTakenEffect
                         THEN UNCHANGED <<ord, itemsBar>>
                         ELSE /\ ord' = Append(ord,self)
                              /\ itemsBar' = Append(itemsBar, x[self])

\* Dequeue takes effect
RefinementD6(self) == /\ IF rep.items[i[self]] /= null THEN itemsBar' = Tail(itemsBar) ELSE UNCHANGED itemsBar
                      /\ UNCHANGED ord
               /\ UNCHANGED ordP \* Predicted sequence never changes

E1P(self) == ProphAction(E1(self), p, p', DomInj, PredDom, LAMBDA j: Pred(j, self)) /\ RefinementE1(self)
E2P(self) == ProphAction(E2(self), p, p', DomInj, PredDom, LAMBDA j: Pred(j, self)) /\ UNCHANGED <<itemsBar, ord>>
E3P(self) == ProphAction(E3(self), p, p', DomInj, PredDom, LAMBDA j: Pred(j, self)) /\ RefinementE3(self)
E4P(self) == ProphAction(E4(self), p, p', DomInj, PredDom, LAMBDA j: Pred(j, self)) /\ UNCHANGED <<itemsBar, ord>>

EnqP(self) == E1P(self) \/ E2P(self) \/ E3P(self) \/ E4P(self)

D1P(self) == ProphAction(D1(self), p, p', DomInj, PredDom, LAMBDA j: Pred(j, self)) /\ UNCHANGED <<itemsBar, ord>>
D2P(self) == ProphAction(D2(self), p, p', DomInj, PredDom, LAMBDA j: Pred(j, self)) /\ UNCHANGED <<itemsBar, ord>>
D3P(self) == ProphAction(D3(self), p, p', DomInj, PredDom, LAMBDA j: Pred(j, self)) /\ UNCHANGED <<itemsBar, ord>>
D4P(self) == ProphAction(D4(self), p, p', DomInj, PredDom, LAMBDA j: Pred(j, self)) /\ UNCHANGED <<itemsBar, ord>>
D5P(self) == ProphAction(D5(self), p, p', DomInj, PredDom, LAMBDA j: Pred(j, self)) /\ UNCHANGED <<itemsBar, ord>>
D6P(self) == ProphAction(D6(self), p, p', DomInj, PredDom, LAMBDA j: Pred(j, self)) /\ RefinementD6(self)
D7P(self) == ProphAction(D7(self), p, p', DomInj, PredDom, LAMBDA j: Pred(j, self)) /\ UNCHANGED <<itemsBar, ord>>
D8P(self) == ProphAction(D8(self), p, p', DomInj, PredDom, LAMBDA j: Pred(j, self)) /\ UNCHANGED <<itemsBar, ord>>
D9P(self) == ProphAction(D9(self), p, p', DomInj, PredDom, LAMBDA j: Pred(j, self)) /\ UNCHANGED <<itemsBar, ord>>
D10P(self) == ProphAction(D10(self), p, p', DomInj, PredDom, LAMBDA j: Pred(j, self)) /\ UNCHANGED <<itemsBar, ord>>

DeqP(self) == D1P(self) \/ D2P(self) \/ D3P(self) \/ D4P(self) \/ D5P(self)
                \/ D6P(self) \/ D7P(self) \/ D8P(self) \/ D9P(self)
                \/ D10P(self)


P1P(self) == ProphAction(P1(self), p, p', DomInj, PredDom, LAMBDA j: Pred(j, self)) /\ UNCHANGED <<itemsBar, ord>>

producerP(self) == P1P(self)

C1P(self) == ProphAction(C1(self), p, p', DomInj, PredDom, LAMBDA j: Pred(j, self)) /\ UNCHANGED <<itemsBar, ord>>

\* Need to add a no-op "done" to consume the done prophecies
Done(self) == /\ pc[self] = "Done"
              /\ UNCHANGED <<vars, itemsBar, ord>>

DoneP(self) == ProphAction(Done(self), p, p', DomInj, PredDom, LAMBDA j: Pred(j, self))

consumerP(self) == C1P(self)


NextP == /\  \/ (\E self \in ProcSet: EnqP(self) \/ DeqP(self))
             \/ (\E self \in Producers: producerP(self))
             \/ (\E self \in Consumers: consumerP(self))
             \/ (\E self \in ProcSet: DoneP(self)) \* consume prophecy var when executing a "done" process
             \/ (* Disjunct to prevent deadlock on termination *)
                ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED varsP)
        /\ UNCHANGED ordP

SpecP == /\ InitP /\ [][NextP]_varsP 


TerminationP == <>(\A self \in ProcSet: pc[self] = "Done")

Q == INSTANCE Queue WITH items<-itemsBar

THEOREM SpecP => Q!Spec
=============================================================================
\* Modification History
\* Last modified Wed Nov 07 22:41:38 PST 2018 by lhochstein
\* Created Wed Oct 31 21:07:38 PDT 2018 by lhochstein
