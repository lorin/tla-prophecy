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


PredEnq(abs) == \E absp \in Pi' : (abs = absp \/ \E v \in Values: Append(abs,v) = absp)

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

Condition ==
    /\ \A pr \in Producers: ProphCondition(E1(pr), DomInjE1, PredDomE1, PredE1)
    /\ \A pr \in Producers: ProphCondition(E2(pr), DomInjE2, PredDomE2, PredE2)
    /\ \A pr \in Producers: ProphCondition(E3(pr), DomInjE3, PredDomE3, PredE3)
    /\ \A pr \in Producers: ProphCondition(E4(pr), DomInjE4, PredDomE4, PredE4)

=============================================================================
\* Modification History
\* Last modified Sat Nov 03 21:27:58 PDT 2018 by lhochstein
\* Created Sat Oct 27 12:02:21 PDT 2018 by lhochstein
