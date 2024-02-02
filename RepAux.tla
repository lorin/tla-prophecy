------------------------------ MODULE RepAux -------------------------------

Rep == INSTANCE Rep

EXTENDS Naturals, Sequences

CONSTANTS Values, 
          EnQers, 
          DeQers

VARIABLES items, 
          back,
          pcd, pce,
          i,
          x,
          range \* deq only

\* Used for refinement mapping
\* From Herlihy & Wing, p478
\* Let <r be the partial order such that x<r y if the STORE operation for x precedes the INC operation for y in H|REP
CONSTANT  NonElt
VARIABLES beforeBar, addingBar

null == CHOOSE y : y \notin Values

Procs == EnQers \union DeQers

TypeOK == /\ items \in [Nat \ {0} -> Values \union {null}]
          /\ back \in Nat
          /\ i \in [Procs -> Nat]
          /\ x \in [Procs -> Values \union {null}]
          /\ range \in [DeQers -> Nat]
          /\ pce \in [EnQers -> {"inc", "store",  "done"}]
          /\ pcd \in [DeQers -> {"range", "for", "swap", "return", "done"}]


Init == /\ items = [j \in Nat\{0} |-> null]
        /\ back = 1
        /\ i \in [Procs -> Nat]
        /\ x \in [Procs -> Values]
        /\ range \in [DeQers -> Nat]
        /\ pce = [e \in EnQers |-> "inc"]
        /\ pcd = [d \in DeQers |-> "range"]
        /\ beforeBar = {}
        /\ addingBar = [e \in EnQers |-> NonElt]
        /\ enqBar = [e \in EnQers |-> Done]


IncEnq(e) ==  LET 
                xe == x[e]
                v == <<xe, back>>
                dones == {ee \in EnQers : pce[ee] = "done"} \* indexes of stored values
                us == {<<items[u], u>>: u \in dones} \* (val, index) pair of stored values
              IN
               /\ pce[e] = "inc"
               /\ i' = [i EXCEPT ![e]=back]
               /\ back' = back+1
               /\ pce' = [pce EXCEPT ![e]="store"]
               /\ beforeBar' = beforeBar \union {<<u, v>> : u \in us}
               /\ addingBar' = [addingBar EXCEPT ![e] = v]
               /\ enqBar' = [encBar EXCEPT ![e]=xe]
               /\ UNCHANGED <<items, x, range, pcd>>

StoreEnq(e) == LET
                 ie == i[e]
                 xe == x[e]
               IN
                /\ pce[e] = "store"
                /\ items' = [items EXCEPT ![ie]=xe]
                /\ pce' = [pce EXCEPT ![e]="done"]
                /\ addingBar' = [addingBar EXCEPT ![e]=NonElt]
                /\ enqBar' = [encBar EXCEPT ![e]=Done]
                /\ UNCHANGED <<back, i, x, range, pcd, beforeBar>>


RangeDeq(d) == /\ pcd[d] = "range"
               /\ range' = [range EXCEPT ![d]=back-1]
               /\ pcd' = [pcd EXCEPT ![d]="for"]
               /\ i' = [i EXCEPT ![d]=0] \* initialize i to 0 before the for loop
               /\ UNCHANGED <<items, back, x, pce, beforeBar, addingBar, enqBar>>

ForDeq(d) == /\ pcd[d] = "for"
             /\ i' = [i EXCEPT ![d]=@+1]
             /\ pcd' = [pcd EXCEPT ![d] = IF i'[d] <= range[d] THEN "swap" ELSE "range"]
             /\ UNCHANGED <<items, back, x, range, pce, beforeBar, addingBar, enqBar>>

SwapDeq(d) == LET id == i[d] IN 
              /\ pcd[d] = "swap"
              /\ x' = [x EXCEPT ![d]=items[id]]
              /\ items' = [items EXCEPT ![id] = null]
              /\ pcd' = [pcd EXCEPT ![d] = "return"]
              /\ UNCHANGED <<back, i, range, pce, beforeBar, addingBar, enqBar>>

ReturnDeq(d) == /\ pcd[d] = "return"
                /\ pcd' = [pcd EXCEPT ![d] = IF x[d] /= null THEN "done" ELSE "range"]
                /\ UNCHANGED <<items, back, i, x, range, pce, beforeBar, addingBar, enqBar>>
 

Next == \/ \E e \in EnQers :
            \/ IncEnq(e) 
            \/ StoreEnq(e)
        \/ \E d \in DeQers :
            \/ RangeDeq(d)
            \/ ForDeq(d)
            \/ SwapDeq(d)
            \/ ReturnDeq(d)

v == <<items, back, pcd, pce, i, x, range, beforBar, addingBar, enqBar>>

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
