-------------------------- MODULE QueueRefinement --------------------------
EXTENDS QueueRep, Utilities

QueueAbs == INSTANCE QueueAbs
Abs(queue,pending,reads)  == QueueAbs!Abs(queue,pending,reads) 
nextIndex(j, max) == QueueAbs!nextIndex(j, max)

pendingWrites ==
    LET pendingProducers == {pr \in Producers : pc[pr] \in {"E2", "E3"}}
    IN  fromPairs({<<rInd_[pr], x[pr] >> : pr \in pendingProducers})

consumerIndexes ==
    LET max == rep.back-1
        pendingConsumersPreIncrement == {cons \in Consumers : pc[cons] \in {"D5","D6"}}
        pendingConsumersPostIncrement == {cons \in Consumers : \/ pc[cons] = "D10"
                                                               \/ pc[cons] = "D7" /\ rVal[cons] = null}
        currentIndex(iCons, mx) == IF iCons <= mx THEN iCons ELSE 1
    IN {currentIndex(i[cons], max): cons \in pendingConsumersPreIncrement} \union {nextIndex(i[cons],max) : cons \in pendingConsumersPostIncrement}

Pi == Abs(rep, pendingWrites, consumerIndexes)
Dom == {1}

INSTANCE Prophecy WITH DomPrime<-Dom'


PredEnq(abs) == \E absp \in Pi' : \/ abs = absp
                                  \/ \E v \in Values: Append(abs,v) = absp
PredDeq(abs) == \E absp \in Pi' : \/ abs = absp 
                                  \/ \E v \in Values: abs = <<v>> \o absp

DomInjE1 == IdFcn(Dom)
PredDomE1 == {1}
PredE1(p) == PredEnq(p[1]) 

DomInjE2 == IdFcn(Dom)
PredDomE2 == {1}
PredE2(p) == PredEnq(p[1]) 

DomInjE3 == IdFcn(Dom)
PredDomE3 == {1}
PredE3(p) == PredEnq(p[1]) 

DomInjE4 == IdFcn(Dom)
PredDomE4 == {1}
PredE4(p) == PredEnq(p[1]) 

DomInjD1 == IdFcn(Dom)
PredDomD1 == {1}
PredD1(p) == PredDeq(p[1]) 

DomInjD2 == IdFcn(Dom)
PredDomD2 == {1}
PredD2(p) == PredDeq(p[1]) 

DomInjD3 == IdFcn(Dom)
PredDomD3 == {1}
PredD3(p) == PredDeq(p[1]) 

DomInjD4 == IdFcn(Dom)
PredDomD4 == {1}
PredD4(p) == PredDeq(p[1]) 

DomInjD5 == IdFcn(Dom)
PredDomD5 == {1}
PredD5(p) == PredDeq(p[1]) 

DomInjD6 == IdFcn(Dom)
PredDomD6 == {1}
PredD6(p) == PredDeq(p[1]) 

DomInjD7 == IdFcn(Dom)
PredDomD7 == {1}
PredD7(p) == PredDeq(p[1]) 

DomInjD8 == IdFcn(Dom)
PredDomD8 == {1}
PredD8(p) == PredDeq(p[1]) 

DomInjD9 == IdFcn(Dom)
PredDomD9 == {1}
PredD9(p) == PredDeq(p[1]) 

DomInjD10 == IdFcn(Dom)
PredDomD10 == {1}
PredD10(p) == PredDeq(p[1]) 

Condition ==
    /\ \A pr \in Producers: ProphCondition(E1(pr), DomInjE1, PredDomE1, PredE1)
    /\ \A pr \in Producers: ProphCondition(E2(pr), DomInjE2, PredDomE2, PredE2)
    /\ \A pr \in Producers: ProphCondition(E3(pr), DomInjE3, PredDomE3, PredE3)
    /\ \A pr \in Producers: ProphCondition(E4(pr), DomInjE4, PredDomE4, PredE4)
    /\ \A co \in Consumers: ProphCondition(D1(co), DomInjD1, PredDomD1, PredD1)
    /\ \A co \in Consumers: ProphCondition(D2(co), DomInjD2, PredDomD2, PredD2)
    /\ \A co \in Consumers: ProphCondition(D3(co), DomInjD3, PredDomD3, PredD3)
    /\ \A co \in Consumers: ProphCondition(D4(co), DomInjD4, PredDomD4, PredD4)
    /\ \A co \in Consumers: ProphCondition(D5(co), DomInjD5, PredDomD5, PredD5)
    /\ \A co \in Consumers: ProphCondition(D6(co), DomInjD6, PredDomD6, PredD6)
    /\ \A co \in Consumers: ProphCondition(D7(co), DomInjD7, PredDomD7, PredD7)
    /\ \A co \in Consumers: ProphCondition(D8(co), DomInjD8, PredDomD8, PredD8)
    /\ \A co \in Consumers: ProphCondition(D9(co), DomInjD9, PredDomD9, PredD9)
    /\ \A co \in Consumers: ProphCondition(D10(co), DomInjD10, PredDomD10, PredD10)
=============================================================================
\* Modification History
\* Last modified Sat Nov 03 21:38:09 PDT 2018 by lhochstein
\* Created Sat Oct 27 12:02:21 PDT 2018 by lhochstein
