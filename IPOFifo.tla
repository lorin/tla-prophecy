------------------------------ MODULE IPOFifo ------------------------------

(********************************************************************************

This spec is copied directly from Lamport's book "Science of Concurrent Programs".

Chapter 6: Auxiliary Variables, p233

 ********************************************************************************)
 
EXTENDS Sequences
 

CONSTANTS EnQers,
          DeQers,
          Data,
          Done,
          NonElt,
          Ids,
          Busy,
          NoData
          
           
VARIABLES enq, deq, elts, before, adding



beingAdded == {adding[e] : e \in EnQers} \ {NonElt}


prec(u, v) == <<u,v>> \in before 


POInit == /\ enq = [e \in EnQers |-> Done]
          /\ deq \in [DeQers -> Data]
          /\ elts = {}
          /\ before = {}
          /\ adding = [e \in EnQers |-> NonElt]
          
BeginPOEnq(e) == 
    /\ enq[e] = Done
    /\ \E D \in Data : \E id \in {i \in Ids : <<D,i>> \notin (elts \union beingAdded)} :
        /\ enq' = [enq EXCEPT ![e] = D]
        /\ elts' = elts \union {<<D,id>>}
        /\ before' = before \union {<<el, <<D, id>>>> : el \in (elts \ beingAdded)}
        /\ adding' = [adding EXCEPT ![e] = <<D,id>>]
    /\ deq' = deq 

EndPOEnq(e) == /\ enq[e] /= Done
               /\ enq' = [enq EXCEPT ![e]=Done]
               /\ adding' = [adding EXCEPT ![e]=NonElt]
               /\ UNCHANGED <<deq, elts, before>>
               
BeginPODeq(d) == /\ deq[d] /= Busy
                 /\ deq' = [deq EXCEPT ![d]=Busy]
                 /\ UNCHANGED <<enq, elts, before, adding>>
                 
                 
EndPODeq(d) == /\ deq[d] = Busy
               /\ \E el \in elts:
                     /\ \A el2 \in elts: ~prec(el2, el)
                     /\ elts' = elts \ {el}
                     /\ deq' = [deq EXCEPT ![d]=el[1]]
                     /\ before' = before \intersect (elts' \X elts')
               /\ UNCHANGED <<enq, adding>>

PONext == \/ \E e \in EnQers : BeginPOEnq(e) \/ EndPOEnq(e)
          \/ \E d \in DeQers : BeginPODeq(d) \/ EndPODeq(d) 


POv == <<enq, deq, elts, before, adding, beingAdded>>

IPOFifo == POInit /\ [][PONext]_POv

\* Prophecy
VARIABLES p, pg, eb

qBar == pg \o eb


BeginPOEnqp(e) == /\ BeginPOEnq(e)
                  /\ \E el \in Data \X Ids : p' = Append(p, el)
                  \* TODO: Determine how pg and eb should evolve here 

EndPOEnqp(e) == /\ EndPOEnq(e)
                /\ (p'=p)
                

BeginPODeqp(d) == BeginPODeq(d) /\ (p'=p)


EndPODeqp(d) == /\ EndPODeq(d)
                /\ pg /= << >> 
                /\ (elts' = elts \ {p[1]}) 
                /\ (p' = Tail(p))
                /\ pg' = Tail(pg)
                /\ qBar' = Tail(qBar)
                \* An EndPOENqp step that removes from beingAdded a datum w that is in elts but not in pg appends w to eb and hence to qBar
                /\ eb' = LET S == (beingAdded \intersect elts) \ (beingAdded' \union pg)
                         IN IF \E w: /\ w \in beingAdded
                                     /\ w \notin beingAdded'
                                     /\ w \in elts
                                     /\ w \notin pg
                            THEN CHOOSE w \in S : Append(eb, w)
                            ELSE eb                 
                

Initp == /\ POInit 
         /\ p = <<>>
         /\ pg = <<>>
         /\ eb = <<>>
Nextp  == \/ \E e \in EnQers : BeginPOEnqp(e) \/ EndPOEnqp(e)
          \/ \E d \in DeQers : BeginPODeqp(d) \/ EndPODeqp(d) 

vp == <<enq, deq, elts, before, adding, p, pg, eb>>

IPFifop == Initp /\ [][Nextp]_vp


BeginPOEnqpq(e) == /\ BeginPOEnqp(e)



enqBar == FALSE
deqBar == FALSE
queueBar == FALSE
enqInnerBar == FALSE
deqInnerBar == FALSE


INSTANCE IFifo WITH enq<-enqBar, deq<-deqBar, queue<-queueBar, enqInner<-enqInnerBar, deqInner<-deqInnerBar


=============================================================================
\* Modification History
\* Last modified Tue Jan 30 21:46:07 PST 2024 by lorin
\* Created Tue Jan 30 20:41:39 PST 2024 by lorin
