------------------------------ MODULE QueueAbs ------------------------------
(***************************************************************************)
(* Abstraction function for queue representation, as described in          *)
(* Herlihy & Wing 1990                                                     *)
(***************************************************************************)
EXTENDS QueueRep

(***************************************************************************
Abs identifies the set of legal linearized values for the given state of
the queue.


 ***************************************************************************)
RECURSIVE Abs(_,_)
Abs(queue, consInds) == 
    IF \E j \in 1..queue.back-1 : queue.items[j] /= null THEN {}
    ELSE {}


=============================================================================
\* Modification History
\* Last modified Fri Nov 02 21:56:05 PDT 2018 by lhochstein
\* Created Fri Nov 02 21:52:24 PDT 2018 by lhochstein
