---- MODULE IPOFifo ----
(*************************************************)
(* From Lamport's Science of Concurrent Programs *)
(*************************************************)

EXTENDS Sequences

CONSTANTS EnQers, DeQers, Data, Busy, Done, Ids
VARIABLES enq,deq,elts,before,adding,p,pg,eb, queueBar
v == <<enq,deq,elts,before,adding,p,pg,eb>>

qBar == pg \o eb

NonElt == CHOOSE NonElt : NonElt \notin (Data \X Ids)

beingAdded == {adding[e] : e \in EnQers} \ {NonElt}

Init == /\ enq = [e \in EnQers |-> Done]
        /\ deq \in [DeQers -> Data]
        /\ elts = {}
        /\ before = {}
        /\ adding = [e \in EnQers |-> NonElt]
        /\ p = <<>>
        /\ pg = <<>>
        /\ eb = <<>>
        /\ queueBar = <<>>

InBlockedState == \E u \in elts : u \notin beingAdded /\ u \notin {pg[i] : i \in DOMAIN pg}

BeginEnq(e) == /\ enq[e] = Done
               /\ \E D \in Data : \E id \in {i \in Ids : <<D,i>> \notin (elts \union beingAdded)} :
                    /\ enq' = [enq EXCEPT ![e]=D]
                    /\ elts' = elts \union {<<D,id>>}
                    /\ before' = before \union {<<el,<<D,id>>>> : el \in (elts \ beingAdded)}
                    /\ adding' = [adding EXCEPT ![e]= <<D,id>> ]
                    /\ \E el \in Data \X Ids : p' = Append(p, el)
                    /\ pg' = IF eb = <<>> THEN Append(pg, <<D, id>>) ELSE pg
               /\ deq' = deq
               /\ UNCHANGED eb

EndEnq(e) == /\ enq[e] # Done
             /\ enq' = [enq EXCEPT ![e]=Done] 
             /\ adding' = [adding EXCEPT ![e]=NonElt]
             /\ eb' = IF InBlockedState THEN Append(eb, adding[e]) ELSE eb
             /\ UNCHANGED <<deq, elts, before, p>>

BeginDeq(d) == /\ deq[d] # Busy
               /\ deq' = [deq EXCEPT ![d]=Busy]
               /\ UNCHANGED <<enq, elts, before, adding, p, eb>>

isBefore(e1,e2) == <<e1,e2>> \in before

EndDeq(d) == /\ deq[d] = Busy
             /\ pg # <<>>
             /\ \E el \in elts:
               /\ \A el2 \in elts: ~(isBefore(el2,el))
               /\ elts' = elts \ {el}
               /\ deq' = [deq EXCEPT ![d]=el[1]]
               /\ before' = before \intersect (elts' \X elts')
               /\ elts' = elts \ {p[1]}
               /\ p' = Tail(p)
               /\ pg' = Tail(pg)
             /\ UNCHANGED <<enq, adding, eb>>


Next == \/ \E e \in EnQers : BeginEnq(e) \/ EndEnq(e)
        \/ \E d \in DeQers : BeginDeq(d) \/ EndDeq(d)


Spec == Init /\ [][Next]_v


====