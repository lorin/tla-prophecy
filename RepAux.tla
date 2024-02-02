------------------------------ MODULE RepAux -------------------------------

EXTENDS Naturals, Sequences

CONSTANTS Values, 
          EnQers, 
          DeQers

VARIABLES items, 
          back,
          pcd, pce,
          i,
          x,
          range 

Rep == INSTANCE Rep

\* Refinement mapping

CONSTANTS Done, Busy

deqBar == FALSE
eltsBar == FALSE



\* Used for refinement mapping
\* From Herlihy & Wing, p478
\* Let <r be the partial order such that x<r y if the STORE operation for x precedes the INC operation for y in H|REP
CONSTANT  NonElt
VARIABLES beforeBar, addingBar, enqBar

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
               /\ enqBar' = [enqBar EXCEPT ![e]=xe]
               /\ UNCHANGED <<items, x, range, pcd>>

StoreEnq(e) == LET
                 ie == i[e]
                 xe == x[e]
               IN
                /\ Rep!StoreEnq(e)
                /\ addingBar' = [addingBar EXCEPT ![e]=NonElt]
                /\ enqBar' = [enqBar EXCEPT ![e]=Done]
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

v == Rep!v \o <<beforeBar, addingBar, enqBar>>

Spec == Init /\ [Next]_v



INSTANCE IPOFifo WITH enq<-enqBar, deq<-deqBar, elts<-eltsBar, adding<-addingBar, before<-beforeBar, Data<-Values, Ids<-Nat\{0}

=============================================================================
\* Modification History
\* Last modified Fri Feb 02 12:18:52 PST 2024 by lorin
\* Created Wed Jan 31 17:11:38 PST 2024 by lorin
