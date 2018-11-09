(***************************************************************************)
(* Operators required for prophecy variables.                              *)
(***************************************************************************)
----------------------------- MODULE QueueRepPP -----------------------------
EXTENDS QueueRep, Utilities, Naturals

(***************************************************************************)
(* The prophecy variable is a sequence that predicts the order in which    *)
(* the scheduler the processes.                                            *)
(***************************************************************************)

Dom == Nat \ {0}
Pi == ProcSet

INSTANCE Prophecy WITH DomPrime<-Dom'

DomInj == [j \in Nat \ {0,1} |-> j-1]
PredDom == {1}
Pred(p, process) == p[1] = process

Condition ==
    /\ \A pr \in Producers: ProphCondition(E1(pr), DomInj, PredDom, LAMBDA p: Pred(p, pr))
    /\ \A pr \in Producers: ProphCondition(E2(pr), DomInj, PredDom, LAMBDA p: Pred(p, pr))
    /\ \A pr \in Producers: ProphCondition(E3(pr), DomInj, PredDom, LAMBDA p: Pred(p, pr))
    /\ \A co \in Consumers: ProphCondition(D1(co), DomInj, PredDom, LAMBDA p: Pred(p, co))
    /\ \A co \in Consumers: ProphCondition(D2(co), DomInj, PredDom, LAMBDA p: Pred(p, co))
    /\ \A co \in Consumers: ProphCondition(D3(co), DomInj, PredDom, LAMBDA p: Pred(p, co))
    /\ \A co \in Consumers: ProphCondition(D4(co), DomInj, PredDom, LAMBDA p: Pred(p, co))
    /\ \A co \in Consumers: ProphCondition(D5(co), DomInj, PredDom, LAMBDA p: Pred(p, co))
    /\ \A co \in Consumers: ProphCondition(D6(co), DomInj, PredDom, LAMBDA p: Pred(p, co))
    /\ \A co \in Consumers: ProphCondition(D7(co), DomInj, PredDom, LAMBDA p: Pred(p, co))
    /\ \A co \in Consumers: ProphCondition(D8(co), DomInj, PredDom, LAMBDA p: Pred(p, co))
    /\ \A co \in Consumers: ProphCondition(D9(co), DomInj, PredDom, LAMBDA p: Pred(p, co))
    /\ \A co \in Consumers: ProphCondition(D10(co), DomInj, PredDom, LAMBDA p: Pred(p, co))


THEOREM Spec => [][Condition]_vars

=============================================================================
\* Modification History
\* Last modified Thu Nov 08 17:05:28 PST 2018 by lhochstein
\* Created Sat Oct 27 12:02:21 PDT 2018 by lhochstein
