------------------------------ MODULE IPOFifoP ------------------------------

(********************************************************************************

This spec is copied directly from Lamport's book "Science of Concurrent Programs".

Chapter 6: Auxiliary Variables, p233

 ********************************************************************************)
 
EXTENDS IPOFifo
 

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
