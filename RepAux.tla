------------------------------ MODULE RepAux -------------------------------

Rep == INSTANCE Rep


\* Used for refinement mapping
\* From Herlihy & Wing, p478
\* Let <r be the partial order such that x<r y if the STORE operation for x precedes the INC operation for y in H|REP
CONSTANT  NonElt
VARIABLES beforeBar, addingBar

TypeOK == Rep!TypeOK

Init == /\ Rep!Init
        /\ beforeBar = {}
        /\ addingBar = [e \in EnQers |-> NonElt]
        /\ enqBar = [e \in EnQers |-> Done]

IncEnq(e) ==  LET 
                xe == x[e]
                v == <<xe, back>>
                dones == {ee \in EnQers : pce[ee] = "done"} \* indexes of stored values
                us == {<<items[u], u>>: u \in dones} \* (val, index) pair of stored values
              IN
               /\ Rep!IncEnq(e)
               /\ beforeBar' = beforeBar \union {<<u, v>> : u \in us}
               /\ addingBar' = [addingBar EXCEPT ![e] = v]
               /\ enqBar' = [encBar EXCEPT ![e]=xe]
               /\ UNCHANGED <<items, x, range, pcd>>

StoreEnq(e) == LET
                 ie == i[e]
                 xe == x[e]
               IN
                /\ RepP!StoreEnq(e)
                /\ addingBar' = [addingBar EXCEPT ![e]=NonElt]
                /\ enqBar' = [encBar EXCEPT ![e]=Done]
                /\ UNCHANGED <<back, i, x, range, pcd, beforeBar>>


RangeDeq(d) == /\ Rep!RangeDeq(d)
               /\ UNCHANGED <<beforeBar, addingBar, enqBar>>

ForDeq(d) == /\ Rep!ForDeq(d)
             /\ UNCHANGED <<beforeBar, addingBar, enqBar>>

SwapDeq(d) == /\ Rep!SwapDeq(d)
              /\ UNCHANGED <<beforeBar, addingBar, enqBar>>

ReturnDeq(d) == /\ Rep!ReturnDeq(d)
                /\ UNCHANGED <<beforeBar, addingBar, enqBar>>
 

Next == \/ \E e \in EnQers :
            \/ IncEnq(e) 
            \/ StoreEnq(e)
        \/ \E d \in DeQers :
            \/ RangeDeq(d)
            \/ ForDeq(d)
            \/ SwapDeq(d)
            \/ ReturnDeq(d)

v == Rep!v \o <<beforBar, addingBar, enqBar>>

Spec == Init /\ [Next]_v

\* Refinement mapping

CONSTANTS Done, Busy

deqBar == FALSE
eltsBar == FALSE


INSTANCE IPOFifo WITH enq<-enqBar, deq<-deqBar, elts<-eltsBar, adding<-addingBar, before<-beforeBar, Data<-Values, Ids<-Nat\{0}

=============================================================================
\* Modification History
\* Last modified Wed Jan 31 20:34:03 PST 2024 by lorin
\* Created Wed Jan 31 17:11:38 PST 2024 by lorin
