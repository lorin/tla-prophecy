---- MODULE POFifo ----
(*************************************************)
(* From Lamport's Science of Concurrent Programs *)
(*************************************************)

EXTENDS Sequences, Naturals, TLC

CONSTANTS EnQers, DeQers, Data, Ids,
          Done, Busy, NonElt

ASSUME Done \notin Data
ASSUME Busy \notin Data
ASSUME NonElt \notin (Data \X Ids)

VARIABLES
    (* external variables *)
    enq,deq,

    (* internal variables *)
    elts,before,adding

beingAdded == {adding[e] : e \in EnQers} \ {NonElt}
IsBefore(e1,e2) == <<e1,e2>> \in before

Init == /\ enq = [e \in EnQers |-> Done]
        /\ deq \in [DeQers -> Data]
        /\ elts = {}
        /\ before = {}
        /\ adding = [e \in EnQers |-> NonElt]

Range(seq) == {seq[i]: i \in DOMAIN seq}
IndexOf(seq, val) == CHOOSE i \in DOMAIN seq : seq[i]=val

BeginEnq(e) == /\ enq[e] = Done
               /\ \E D \in Data : \E id \in {i \in Ids : <<D,i>> \notin (elts \union beingAdded)} :
                    LET w == <<D,id>>
                    IN /\ enq' = [enq EXCEPT ![e]=D]
                       /\ elts' = elts \union {w}
                       /\ before' = before \union {<<el,w>> : el \in (elts \ beingAdded)}
                       /\ adding' = [adding EXCEPT ![e]= w ]
               /\ UNCHANGED deq


EndEnq(e) == /\ enq[e] # Done
             /\ enq' = [enq EXCEPT ![e]=Done]
             /\ adding' = [adding EXCEPT ![e]=NonElt]
             /\ UNCHANGED <<deq, elts, before>>

BeginDeq(d) == /\ deq[d] # Busy
               /\ deq' = [deq EXCEPT ![d]=Busy]
               /\ UNCHANGED <<enq, elts, before, adding>>


EndDeq(d) == /\ deq[d] = Busy
             /\ \E el \in elts:
               /\ \A el2 \in elts: ~(IsBefore(el2,el))
               /\ elts' = elts \ {el}
               /\ deq' = [deq EXCEPT ![d]=el[1]]
               /\ before' = before \intersect (elts' \X elts')
             /\ UNCHANGED <<enq, adding>>

Next == \/ \E e \in EnQers : \/ BeginEnq(e)
                             \/ EndEnq(e)
        \/ \E d \in DeQers :  \/ BeginDeq(d)
                              \/ EndDeq(d)


v == <<enq,deq,elts,before,adding>>
Spec == Init /\ [][Next]_v 

====