------------------------------- MODULE IFifo -------------------------------

(********************************************************************************

This spec is copied directly from Lamport's book "Science of Concurrent Programs".

Chapter 6: Auxiliary Variables, p229

 ********************************************************************************)

EXTENDS Sequences

CONSTANTS EnQers, 
          DeQers,
          Data,
          Done,
          Busy,
          NoData

VARIABLES enq, deq, queue, enqInner, deqInner



BeginEnq(e) ==  /\ enq[e] = Done
                /\ \E D \in Data: enq' = [enq EXCEPT ![e] = D]
                /\ enqInner' = [enqInner EXCEPT ![e] = Busy] 
                /\ UNCHANGED <<deq, queue, deqInner>>

DoEnq(e) == /\ enqInner[e] = Busy
            /\ queue' = Append(queue, enq[e])
            /\ enqInner' = [enqInner EXCEPT ![e] = Done]
            /\ UNCHANGED <<deq, enq, deqInner>>
            
EndEnq(e) ==  /\ enq[e] /= Done
              /\ enqInner[e] = Done
              /\ enq' = [enq EXCEPT ![e] = Done]
              /\ UNCHANGED <<deq, queue, enqInner, deqInner>>
              
BeginDeq(d) ==  /\ deq[d] /= Busy
                /\ deq' = [deq EXCEPT ![d] = Busy]
                /\ deqInner' = [deqInner EXCEPT ![d] = NoData]
                /\ UNCHANGED <<enq, queue, enqInner>>

DoDeq(d) == /\ deq[d] = Busy
            /\ deqInner[d] = NoData
            /\ queue /= <<>>
            /\ deqInner' = [deqInner EXCEPT ![d] = Head(queue)]
            /\ queue' = Tail(queue)
            /\ UNCHANGED <<enq, deq, enqInner>>
            
EndDeq(d) == /\ deq[d] = Busy
             /\ deqInner[d] /= NoData
             /\ deq' = [deq EXCEPT ![d] = deqInner[d]]
             /\ UNCHANGED <<enq, queue, enqInner, deqInner>> 


Init == /\ enq = [e \in EnQers |-> Done]
        /\ deq \in [DeQers -> Data]
        /\ queue = <<>>
        /\ enqInner = [e \in EnQers |-> Done]
        /\ deqInner = deq
                        
        
Next == \/ \E e \in EnQers : BeginEnq(e) \/ DoEnq(e) \/ EndEnq(e)
        \/ \E d \in DeQers : BeginDeq(d) \/ DoDeq(d) \/ EndDeq(d)

v == <<enq, deq, queue, enqInner, deqInner>>

Spec == Init /\ [][Next]_v


=============================================================================
\* Modification History
\* Last modified Tue Jan 30 18:12:57 PST 2024 by lorin
\* Created Tue Jan 30 17:43:01 PST 2024 by lorin
