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

Condition ==
    /\ \A pr \in Producers: ProphCondition(E1(pr), DomInjE1, PredDomE1, PredE1)

=============================================================================
\* Modification History
\* Last modified Sat Nov 03 21:23:57 PDT 2018 by lhochstein
\* Created Sat Oct 27 12:02:21 PDT 2018 by lhochstein
