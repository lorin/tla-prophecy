(*************************************************)
(* From Lamport's Science of Concurrent Programs *)
(*************************************************)
---- MODULE IPOFifo ----

CONSTANTS EnQers, DeQers, Data, Busy, Done, Ids
VARIABLES enq,deq,elts,before,adding
v ==    <<enq,deq,elts,before,adding>>

NonElt == CHOOSE NonElt : NonElt \notin (Data \X Ids)

beingAdded == {adding[e] : e \in EnQers} \ {NonElt}

Init == /\ enq = [e \in EnQers |-> Done]
        /\ deq \in [DeQers -> Data]
        /\ elts = {}
        /\ before = {}
        /\ adding = [e \in EnQers |-> NonElt]

BeginEnq(e) == /\ enq[e] = Done
               /\ \E D \in Data : \E id \in {i \in Ids : <<D,i>> \notin (elts \union beingAdded)} :
                    /\ enq' = [enq EXCEPT ![e]=D]
                    /\ elts' = elts \union {<<D,id>>}
                    /\ before' = before \union {<<el,<<D,id>>>> : el \in (elts \ beingAdded)}
                    /\ adding' = [adding EXCEPT ![e]= <<D,id>> ]
               /\ deq' = deq

EndEnq(e) == /\ enq[e] # Done
             /\ enq' = [enq EXCEPT ![e]=Done] 
             /\ adding' = [adding EXCEPT ![e]=NonElt]
             /\ UNCHANGED <<deq, elts, before>>

BeginDeq(d) == /\ deq[d] # Busy
               /\ deq' = [deq EXCEPT ![d]=Busy]
               /\ UNCHANGED <<enq, elts, before, adding>>

isBefore(e1,e2) == <<e1,e2>> \in before

EndDeq(d) == /\ deq[d] = Busy
             /\ \E el \in elts:
               /\ \A el2 \in elts: ~(isBefore(el2,el))
               /\ elts' = elts \ {el}
               /\ deq' = [deq EXCEPT ![d]=el[1]]
               /\ before' = before \intersect (elts' \X elts')
             /\ UNCHANGED <<enq, adding>>


Next == \/ \E e \in EnQers : BeginEnq(e) \/ EndEnq(e)
        \/ \E d \in DeQers : BeginDeq(d) \/ EndDeq(d)


Spec == Init /\ [][Next]_v


====