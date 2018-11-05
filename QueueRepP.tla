----------------------------- MODULE QueueRepP -----------------------------
EXTENDS QueueRefinement

VARIABLE p

varsP == <<vars,p>>

InitP == Init /\ (p \in [Dom->Pi])

E1P(self) == ProphAction(E1(self), p, p', DomInjE1, PredDomE1, PredE1(self))
E2P(self) == ProphAction(E2(self), p, p', DomInjE2, PredDomE2, PredE2(self))
E3P(self) == ProphAction(E3(self), p, p', DomInjE3, PredDomE3, PredE3(self))
E4P(self) == ProphAction(E4(self), p, p', DomInjE4, PredDomE4, PredE4(self))

EnqP(self) == E1P(self) \/ E2P(self) \/ E3P(self) \/ E4P(self)

D1P(self) == ProphAction(D1(self), p, p', DomInjD1, PredDomD1, PredD1(self))
D2P(self) == ProphAction(D2(self), p, p', DomInjD2, PredDomD2, PredD2(self))
D3P(self) == ProphAction(D3(self), p, p', DomInjD3, PredDomD3, PredD3(self))
D4P(self) == ProphAction(D4(self), p, p', DomInjD4, PredDomD4, PredD4(self))
D5P(self) == ProphAction(D5(self), p, p', DomInjD5, PredDomD5, PredD5(self))
D6P(self) == ProphAction(D6(self), p, p', DomInjD6, PredDomD6, PredD6(self))
D7P(self) == ProphAction(D7(self), p, p', DomInjD7, PredDomD7, PredD7(self))
D8P(self) == ProphAction(D8(self), p, p', DomInjD8, PredDomD8, PredD8(self))
D9P(self) == ProphAction(D9(self), p, p', DomInjD9, PredDomD9, PredD9(self))
D10P(self) == ProphAction(D10(self), p, p', DomInjD10, PredDomD10, PredD10(self))

DeqP(self) == D1P(self) \/ D2P(self) \/ D3P(self) \/ D4P(self) \/ D5P(self)
                \/ D6P(self) \/ D7P(self) \/ D8P(self) \/ D9P(self)
                \/ D10P(self)


DomInjP1 == IdFcn(Dom)
PredDomP1 == {}
PredP1(p) == TRUE

P1P(self) == ProphAction(P1(self), p, p', DomInjP1, PredDomP1, PredP1(self))

producerP(self) == P1P(self)

C1P(self) == ProphAction(C1(self), p, p', DomInjC1, PredDomC1, PredC1(self))

consumerP(self) == C1P(self)

NextP == (\E self \in ProcSet: Enq(self) \/ Deq(self))
           \/ (\E self \in Producers: producerP(self))
           \/ (\E self \in Consumers: consumerP(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED varsP)

Spec == /\ InitP /\ [][NextP]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")
=============================================================================
\* Modification History
\* Last modified Fri Nov 02 17:12:04 PDT 2018 by lhochstein
\* Created Wed Oct 31 21:07:38 PDT 2018 by lhochstein
