------------------------------- MODULE Queue -------------------------------
(***************************************************************************)
(* A high-level specification for a sequential queue                       *)
(***************************************************************************)

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
\* Last modified Thu Nov 08 19:07:01 PST 2018 by lhochstein
\* Created Fri Apr 20 23:43:41 PDT 2018 by lhochstein
