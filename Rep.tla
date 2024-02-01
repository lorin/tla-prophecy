-------------------------------- MODULE Rep --------------------------------

EXTENDS Naturals, Sequences

CONSTANTS Values, 
          EnQers, 
          DeQers

VARIABLES items, 
          back,
          pc,
          i,
          x,
          range \* deq only

null == CHOOSE y : y \notin Values

Procs == EnQers \union DeQers

TypeOK == /\ items \in [Nat -> Values \union {null}]
          /\ back \in Nat
          /\ i \in [Procs -> Nat]
          /\ x \in [Procs -> Values]
          /\ range \in [DeQers -> Nat]
          /\ pc \in [Procs -> {"alloc", "fill",  "done", "range", "for", "swap", "return"}]


Init == /\ items = [j \in Nat\{0} |-> null]
        /\ back = 1
        /\ i \in [Procs -> Nat]
        /\ x \in [EnQers -> Values]
        /\ range \in [DeQers -> Nat]
        /\ \A e \in EnQers: pc[e] = "alloc"
        /\ \A d \in DeQers: pc[d] = "while"


AllocEnq(e) == /\ pc[e] = "alloc"
               /\ i'[e] = back
               /\ back' = back+1
               /\ pc' = [pc EXCEPT ![e]="fill"]
               /\ UNCHANGED <<items, x, range>>

FillEnq(e) == /\ pc[e] = "fill"
              /\ items' = [items EXCEPT ![i[e]]=x[e]]
              /\ pc' = [pc EXCEPT ![e]="done"]
              /\ UNCHANGED <<back, i, x, range>>


RangeDeq(d) == /\ pc[d] = "range"
               /\ range' = [range EXCEPT ![d]=back-1]
               /\ pc' = [pc EXCEPT ![d]="for"]
               /\ i' = [i EXCEPT ![d]=0] \* initialize i to 0 before the for loop
               /\ UNCHANGED <<items, back, x>>

ForDeq(d) == /\ pc[d] = "for"
             /\ i'=[i EXCEPT ![d]=@+1]
             /\ pc' = [pc EXCEPT ![d] = IF i'[d] <= range THEN "swap" ELSE "range"]
             /\ UNCHANGED <<items, back, x, range>>

SwapDeq(d) == LET id == i[d] IN 
              /\ pc[d] = "swap"
              /\ x' = [x EXCEPT ![d]=items[id]]
              /\ items' = [items EXCEPT ![id] = null]
              /\ pc' = [pc EXCEPT ![d] = "return"]
              /\ UNCHANGED <<back, i, range>>

ReturnDeq(d) == /\ pc[d] = "return"
                /\ pc' = [pc EXCEPT ![d] = IF x[d] /= null THEN "done" ELSE "range"]
                /\ UNCHANGED <<items, back, i, x, range>>
 

Next == \/ \E e \in EnQers :
            \/ AllocEnq(e) 
            \/ FillEnq(e)
        \/ \E d \in DeQers :
            \/ RangeDeq(d)
            \/ ForDeq(d)
            \/ SwapDeq(d)
            \/ ReturnDeq(d)

v == <<items, back, pc, i, x, range>>

Spec == Init /\ [Next]_v


=============================================================================
\* Modification History
\* Last modified Wed Jan 31 18:59:42 PST 2024 by lorin
\* Created Wed Jan 31 17:11:38 PST 2024 by lorin
