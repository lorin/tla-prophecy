------------------------------ MODULE QueueAbs ------------------------------
(***************************************************************************)
(* Abstraction function for queue representation, as described in          *)
(* Herlihy & Wing 1990                                                     *)
(***************************************************************************)
EXTENDS QueueRep

(***************************************************************************)
(* Abs identifies the set of legal linearized values for the given state of *)
(* the queue.                                                              *)
(*                                                                         *)
(***************************************************************************)
 
 
 \* queue is the rep queue 
 \* consInds is the set of indexes where the current consumers are
 \* pendingProdVals maps indexes to values to enqueue

 
RECURSIVE Abs(_,_,_)
Abs(queue, consInds,pendingProdVals) == 
    LET itemInds(q) == {j \in 1..q.back -1 : q.items[j] /= null}
        queueEmpty(q) == itemInds(q) = {}
        fVals(q,pending) == [d \in itemInds|->q.items[d]] @@ pending

    IN CASE queueEmpty -> {}
         [] ~queueEmpty /\ consInds = {} /\ pendingProdVals = {} -> SelectSeq(SubSeq(queue.items, 1, queue.back-1), LAMBDA val: val /= null)
         [] ~queueEmpty /\ consInds /= {} -> LET j == CHOOSE j \in consInds: TRUE
                                                 RECURSIVE candidateInds(_,_)
                                                 candidateInds(k, pending) == IF queueEmpty THEN {}
                                                                              ELSE IF queue.items[k] /= null THEN {k}
                                                                              ELSE IF k \in pending THEN {k} \union candidateInds(k, pending\{k})
                                                                              ELSE IF k=queue.back THEN candidateInds(1, pending)
                                                                              ELSE candidateInds(k+1,pending)
                                                             
                                             \* for each consumer index:
                                             \* figure out the candidate first element of the queue, and the recursion for the next
                                             




=============================================================================
\* Modification History
\* Last modified Fri Nov 02 22:35:36 PDT 2018 by lhochstein
\* Created Fri Nov 02 21:52:24 PDT 2018 by lhochstein
