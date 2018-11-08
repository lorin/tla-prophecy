----------------------------- MODULE QueueRepPP -----------------------------
EXTENDS QueueRep, Utilities, Naturals

(***************************************************************************)
(* The prophecy variable predicts how the scheduler will interleave        *)
(* statements among the processes.                                         *)
(***************************************************************************)

Dom == Nat \ {0}
Pi == ProcSet

INSTANCE Prophecy WITH DomPrime<-Dom'


DomInjE1 == [j \in Nat \ {0,1} |-> j-1]
PredDomE1 == {1}
PredE1(p, process) == p[1] = process

DomInjE2 == [j \in Nat \ {0,1} |-> j-1]
PredDomE2 == {1}
PredE2(p, process) == p[1] = process

DomInjE3 == [j \in Nat \ {0,1} |-> j-1]
PredDomE3 == {1}
PredE3(p, process) == p[1] = process 

DomInjE4 == [j \in Nat \ {0,1} |-> j-1]
PredDomE4 == {1}
PredE4(p, process) == p[1] = process

DomInjC1 == [j \in Nat \ {0,1} |-> j-1]
PredDomC1 == {1}
PredC1(p, process) == p[1] = process

DomInjD1 == [j \in Nat \ {0,1} |-> j-1]
PredDomD1 == {1}
PredD1(p, process) == p[1] = process 

DomInjD2 == [j \in Nat \ {0,1} |-> j-1]
PredDomD2 == {1}
PredD2(p, process) == p[1] = process 

DomInjD3 == [j \in Nat \ {0,1} |-> j-1]
PredDomD3 == {1}
PredD3(p, process) == p[1] = process 

DomInjD4 == [j \in Nat \ {0,1} |-> j-1]
PredDomD4 == {1}
PredD4(p, process) == p[1] = process

DomInjD5 == [j \in Nat \ {0,1} |-> j-1]
PredDomD5 == {1}
PredD5(p, process) == p[1] = process 

DomInjD6 == [j \in Nat \ {0,1} |-> j-1]
PredDomD6 == {1}
PredD6(p, process) == p[1] = process

DomInjD7 == [j \in Nat \ {0,1} |-> j-1]
PredDomD7 == {1}
PredD7(p, process) == p[1] = process

DomInjD8 == [j \in Nat \ {0,1} |-> j-1]
PredDomD8 == {1}
PredD8(p, process) == p[1] = process

DomInjD9 == [j \in Nat \ {0,1} |-> j-1]
PredDomD9 == {1}
PredD9(p, process) == p[1] = process

DomInjD10 == [j \in Nat \ {0,1} |-> j-1]
PredDomD10 == {1}
PredD10(p, process) == p[1] = process

DomInjP1 == [j \in Nat \ {0,1} |-> j-1]
PredDomP1 == {1}
PredP1(p, process) == p[1] = process

DomInjDone == [j \in Nat \ {0,1} |-> j-1]
PredDomDone == {1}
PredDone(p, process) == p[1] = process


Condition ==
    /\ \A pr \in Producers: ProphCondition(E1(pr), DomInjE1, PredDomE1, LAMBDA p: PredE1(p, pr))
    /\ \A pr \in Producers: ProphCondition(E2(pr), DomInjE2, PredDomE2, LAMBDA p: PredE2(p, pr))
    /\ \A pr \in Producers: ProphCondition(E3(pr), DomInjE3, PredDomE3, LAMBDA p: PredE3(p, pr))
    /\ \A pr \in Producers: ProphCondition(E4(pr), DomInjE4, PredDomE4, LAMBDA p: PredE4(p, pr))
    /\ \A co \in Consumers: ProphCondition(D1(co), DomInjD1, PredDomD1, LAMBDA p: PredD1(p, co))
    /\ \A co \in Consumers: ProphCondition(D2(co), DomInjD2, PredDomD2, LAMBDA p: PredD2(p, co))
    /\ \A co \in Consumers: ProphCondition(D3(co), DomInjD3, PredDomD3, LAMBDA p: PredD3(p, co))
    /\ \A co \in Consumers: ProphCondition(D4(co), DomInjD4, PredDomD4, LAMBDA p: PredD4(p, co))
    /\ \A co \in Consumers: ProphCondition(D5(co), DomInjD5, PredDomD5, LAMBDA p: PredD5(p, co))
    /\ \A co \in Consumers: ProphCondition(D6(co), DomInjD6, PredDomD6, LAMBDA p: PredD6(p, co))
    /\ \A co \in Consumers: ProphCondition(D7(co), DomInjD7, PredDomD7, LAMBDA p: PredD7(p, co))
    /\ \A co \in Consumers: ProphCondition(D8(co), DomInjD8, PredDomD8, LAMBDA p: PredD8(p, co))
    /\ \A co \in Consumers: ProphCondition(D9(co), DomInjD9, PredDomD9, LAMBDA p: PredD9(p, co))
    /\ \A co \in Consumers: ProphCondition(D10(co), DomInjD10, PredDomD10, LAMBDA p: PredD10(p, co))


=============================================================================
\* Modification History
\* Last modified Sun Nov 04 17:36:17 PST 2018 by lhochstein
\* Created Sat Oct 27 12:02:21 PDT 2018 by lhochstein
