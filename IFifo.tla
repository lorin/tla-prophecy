---- MODULE IFifo ----
(*************************************************)
(* From Lamport's Science of Concurrent Programs *)
(* Figure 6.9                                    *)
(*************************************************)

EXTENDS Sequences

CONSTANTS EnQers, DeQers, Data, Done, Busy, NoData
VARIABLES enq,deq,queue,enqInner,deqInner

ASSUME NoData \notin Data


Init == /\ enq = [e \in EnQers |-> Done]
        /\ deq = [DeQers -> Data]
        /\ queue = <<>>
        /\ enqInner = [e \in EnQers |-> Done]
        /\ deqInner = deq

BeginEnq(e) == /\ enq[e] = Done
               /\ \E D \in Data : enq' = [enq EXCEPT ![e]=D]
               /\ enqInner' = [enqInner EXCEPT ![e]=Busy]
               /\ UNCHANGED <<deq,queue,deqInner>>

DoEnq(e) ==  /\ enqInner[e] = Busy
             /\ queue' = Append(queue,enq[e])
             /\ enqInner' = [enqInner EXCEPT ![e]=Done]
             /\ UNCHANGED <<deq,enq,deqInner>>

EndEnq(e) == /\ enq[e] # Done
             /\ enqInner[e] = Done
             /\ enq' = [enq EXCEPT ![e]=Done]
             /\ UNCHANGED <<deq,queue,enqInner,deqInner>>

BeginDeq(d) ==  /\ deq[d] # Busy
                /\ deq' = [deq EXCEPT ![d]=Busy]
                /\ deqInner' = [deqInner EXCEPT ![d]=NoData]
                /\ UNCHANGED <<enq,queue,enqInner>>

DoDeq(d) == /\ deq[d] = Busy
            /\ deqInner[d] = NoData
            /\ queue # <<>>
            /\ deqInner' = [deqInner EXCEPT ![d]=Head(queue)]

EndDeq(d) == /\ deq[d] = Busy
             /\ deqInner[d] # NoData
             /\ deq' = [deq EXCEPT ![d]=deqInner[d]]
             /\ UNCHANGED <<enq,queue,enqInner,deqInner>>

Next == \/ \E e \in EnQers : BeginEnq(e) \/ DoEnq(e) \/ EndEnq(e)
        \/ \E d \in DeQers : BeginDeq(d) \/ DoDeq(d) \/ EndDeq(d)

v == <<enq,deq,queue,enqInner,deqInner>>
Spec == Init /\ [][Next]_v


====