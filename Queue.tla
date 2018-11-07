------------------------------- MODULE Queue -------------------------------
(*** A specification for an abstract, sequential queue ***)

EXTENDS Sequences

CONSTANT Values

VARIABLE items

Enq(val, q, qp) == qp = Append(q, val)

Deq(val, q, qp) == /\ q /= << >>
                   /\ val = Head(q)
                   /\ qp = Tail(q)
                   
                   
Init == /\ items = << >>

Next == \/ \E v \in Values : /\ Enq(v, items, items')
        \/ \E v \in Values : /\ Deq(v, items, items')
        
Spec == Init /\ [] [Next]_<<items>>

              

=============================================================================
\* Modification History
\* Last modified Sat Oct 27 12:03:44 PDT 2018 by lhochstein
\* Created Fri Apr 20 23:43:41 PDT 2018 by lhochstein
