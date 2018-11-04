-------------------------- MODULE QueueRefinement --------------------------
EXTENDS QueueRep, Utilities

QueueAbs == INSTANCE QueueAbs
Abs(queue,pending,reads)  == QueueAbs!Abs(queue,pending,reads) 

pendingWrites ==
    LET pendingProducers == {pr \in Producers : pc[pr] \in {"E2", "E3"}}
        RECURSIVE build(_, _)
        build(f, prs) == IF prs = {} THEN f
                         ELSE LET pr == CHOOSE pr \in pendingProducers : TRUE
                             IN build(f @@ rInd_[pr] :> x[pr], prs \ {pr})
    IN IF pendingProducers = {} THEN << >> ELSE build(<<>>, pendingProducers)

consumerIndexes ==
    LET pendingConsumersPreIncrement == {cons \in Consumers : pc[cons] \in {"D5","D6"}}
        pendingConsumersPostIncrement == {cons \in Consumers : \/ pc[cons] = "D10"
                                                               \/ pc[cons] = "D7" /\ rVal[cons] = null}
    IN {i[cons] : cons \in pendingConsumersPreIncrement} \union {i[cons]+1 : cons \in pendingConsumersPostIncrement}

Pi == Abs(rep, pendingWrites, consumerIndexes)
Dom == {1}

INSTANCE Prophecy WITH DomPrime<-Dom'


PredEnq(p) == \E pp \in Pi' : \/ p = pp
                              \/ \E v \in Values: Append(p,v) = pp

DomInjE1 == IdFcn(Dom)
PredDomE1 == {1}
PredE1(p) == PredEnq(p)

Condition ==
    /\ \A pr \in Producers: ProphCondition(E1(pr), DomInjE1, PredDomE1, PredE1)

=============================================================================
\* Modification History
\* Last modified Sat Nov 03 19:39:06 PDT 2018 by lhochstein
\* Created Sat Oct 27 12:02:21 PDT 2018 by lhochstein
