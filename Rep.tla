-------------------------------- MODULE Rep --------------------------------

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
VARIABLE before

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


IncEnq(e) == /\ pce[e] = "inc"
               /\ i' = [i EXCEPT ![e]=back]
               /\ back' = back+1
               /\ pce' = [pce EXCEPT ![e]="store"]
               /\ UNCHANGED <<items, x, range, pcd>>

StoreEnq(e) == LET
                 ie == i[e]
                 xe == x[e]
              IN
                /\ pce[e] = "store"
                /\ items' = [items EXCEPT ![ie]=xe]
                /\ pce' = [pce EXCEPT ![e]="done"]
                /\ UNCHANGED <<back, i, x, range, pcd>>


RangeDeq(d) == /\ pcd[d] = "range"
               /\ range' = [range EXCEPT ![d]=back-1]
               /\ pcd' = [pcd EXCEPT ![d]="for"]
               /\ i' = [i EXCEPT ![d]=0] \* initialize i to 0 before the for loop
               /\ UNCHANGED <<items, back, x, pce>>

ForDeq(d) == /\ pcd[d] = "for"
             /\ i' = [i EXCEPT ![d]=@+1]
             /\ pcd' = [pcd EXCEPT ![d] = IF i'[d] <= range[d] THEN "swap" ELSE "range"]
             /\ UNCHANGED <<items, back, x, range, pce>>

SwapDeq(d) == LET id == i[d] IN 
              /\ pcd[d] = "swap"
              /\ x' = [x EXCEPT ![d]=items[id]]
              /\ items' = [items EXCEPT ![id] = null]
              /\ pcd' = [pcd EXCEPT ![d] = "return"]
              /\ UNCHANGED <<back, i, range, pce>>

ReturnDeq(d) == /\ pcd[d] = "return"
                /\ pcd' = [pcd EXCEPT ![d] = IF x[d] /= null THEN "done" ELSE "range"]
                /\ UNCHANGED <<items, back, i, x, range, pce>>
 

Next == \/ \E e \in EnQers :
            \/ IncEnq(e) 
            \/ StoreEnq(e)
        \/ \E d \in DeQers :
            \/ RangeDeq(d)
            \/ ForDeq(d)
            \/ SwapDeq(d)
            \/ ReturnDeq(d)

v == <<items, back, pcd, pce, i, x, range>>

Spec == Init /\ [Next]_v

\* Refinement mapping

CONSTANTS Done, Ids, NonElt, Busy

INSTANCE IPOFifo WITH enq<-FALSE, deq<-FALSE, elts<-FALSE, before<-FALSE, adding<-FALSE, Data<-Values

=============================================================================
\* Modification History
\* Last modified Wed Jan 31 19:58:26 PST 2024 by lorin
\* Created Wed Jan 31 17:11:38 PST 2024 by lorin
