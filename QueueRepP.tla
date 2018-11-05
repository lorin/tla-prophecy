----------------------------- MODULE QueueRepP -----------------------------
EXTENDS QueueRefinement

VARIABLE p

varsP == <<vars,p>>

InitP == Init /\ (p \in [Dom->Pi])

E1P(self) == ProphAction(E1(self), p, p', DomInjE1, PredDomE1, LAMBDA j: PredE1(j, self))
E2P(self) == ProphAction(E2(self), p, p', DomInjE2, PredDomE2, LAMBDA j: PredE2(j, self))
E3P(self) == ProphAction(E3(self), p, p', DomInjE3, PredDomE3, LAMBDA j: PredE3(j, self))
E4P(self) == ProphAction(E4(self), p, p', DomInjE4, PredDomE4, LAMBDA j: PredE4(j, self))

EnqP(self) == E1P(self) \/ E2P(self) \/ E3P(self) \/ E4P(self)

D1P(self) == ProphAction(D1(self), p, p', DomInjD1, PredDomD1, LAMBDA j: PredD1(j, self))
D2P(self) == ProphAction(D2(self), p, p', DomInjD2, PredDomD2, LAMBDA j: PredD2(j, self))
D3P(self) == ProphAction(D3(self), p, p', DomInjD3, PredDomD3, LAMBDA j: PredD3(j, self))
D4P(self) == ProphAction(D4(self), p, p', DomInjD4, PredDomD4, LAMBDA j: PredD4(j, self))
D5P(self) == ProphAction(D5(self), p, p', DomInjD5, PredDomD5, LAMBDA j: PredD5(j, self))
D6P(self) == ProphAction(D6(self), p, p', DomInjD6, PredDomD6, LAMBDA j: PredD6(j, self))
D7P(self) == ProphAction(D7(self), p, p', DomInjD7, PredDomD7, LAMBDA j: PredD7(j, self))
D8P(self) == ProphAction(D8(self), p, p', DomInjD8, PredDomD8, LAMBDA j: PredD8(j, self))
D9P(self) == ProphAction(D9(self), p, p', DomInjD9, PredDomD9, LAMBDA j: PredD9(j, self))
D10P(self) == ProphAction(D10(self), p, p', DomInjD10, PredDomD10, LAMBDA j: PredD10(j, self))

DeqP(self) == D1P(self) \/ D2P(self) \/ D3P(self) \/ D4P(self) \/ D5P(self)
                \/ D6P(self) \/ D7P(self) \/ D8P(self) \/ D9P(self)
                \/ D10P(self)


P1P(self) == ProphAction(P1(self), p, p', DomInjP1, PredDomP1, LAMBDA j: PredP1(j, self))

producerP(self) == P1P(self)

C1P(self) == ProphAction(C1(self), p, p', DomInjC1, PredDomC1, LAMBDA j: PredC1(j, self))

consumerP(self) == C1P(self)

NextP == (\E self \in ProcSet: EnqP(self) \/ DeqP(self))
           \/ (\E self \in Producers: producerP(self))
           \/ (\E self \in Consumers: consumerP(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED varsP)

SpecP == /\ InitP /\ [][NextP]_vars

TerminationP == <>(\A self \in ProcSet: pc[self] = "Done")
=============================================================================
\* Modification History
\* Last modified Sun Nov 04 17:18:49 PST 2018 by lhochstein
\* Created Wed Oct 31 21:07:38 PDT 2018 by lhochstein
