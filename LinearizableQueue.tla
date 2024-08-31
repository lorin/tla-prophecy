---- MODULE LinearizableQueue ----
EXTENDS Sequences

CONSTANTS Val,Thread,none 
VARIABLES op,arg,rval,up,done,d

ASSUME none \notin Val

EnqStart(Ti) == /\ done[Ti] 
                /\ op' = [op EXCEPT ![Ti] = "enq"]
                /\ \E x \in Val: arg' = [arg EXCEPT ![Ti] = x]
                /\ rval' = [rval EXCEPT ![Ti] = none]
                /\ up' = [up EXCEPT ![Ti] = FALSE]
                /\ done' = [done EXCEPT ![Ti] = FALSE]
                /\ UNCHANGED d

EnqTakesEffect(Ti) ==  /\ op[Ti]="enq"
                       /\ ~done[Ti] 
                       /\ ~up[Ti]
                       /\ up' = [up EXCEPT ![Ti] = TRUE]
                       /\ d' = Append(d, arg[Ti])
                       /\ UNCHANGED <<op,arg,rval,done>>

EnqDone(Ti) == /\ op[Ti]="enq"
               /\ up[Ti]
               /\ ~done[Ti]
               /\ done' = [done EXCEPT ![Ti] = TRUE]
               /\ UNCHANGED <<op,arg,rval,up,d>>

DeqStart(Ti) == /\ done[Ti]
                /\ op' = [op EXCEPT ![Ti] = "deq"]
                /\ arg' = [arg EXCEPT ![Ti] = none]
                /\ rval' = [rval EXCEPT ![Ti] = none]
                /\ up' = [up EXCEPT ![Ti] = FALSE]
                /\ done' = [done EXCEPT ![Ti] = FALSE]
                /\ UNCHANGED d

DeqTakesEffect(Ti) == /\ op[Ti] = "deq"
                      /\ d # <<>>
                      /\ ~up[Ti]
                      /\ ~done[Ti]
                      /\ rval' = [rval EXCEPT ![Ti]=Head(d)]
                      /\ up' = [up EXCEPT ![Ti] = TRUE]
                      /\ d' = Tail(d)
                      /\ UNCHANGED <<op,arg,done>>

\* 
DeqDone(Ti) == /\ op[Ti] = "deq"
               /\ up[Ti]
               /\ ~done[Ti]
               /\ done' = [done EXCEPT ![Ti] = TRUE]
               /\ UNCHANGED <<op,arg,rval,up,d>>

Init == /\ op = [Ti \in Thread |-> "start"]
        /\ arg = [Ti \in Thread |-> none]
        /\ rval = [Ti \in Thread |-> none]
        /\ up = [Ti \in Thread |-> TRUE]
        /\ done = [Ti \in Thread |-> TRUE]
        /\ d = <<>>

Next == \E Ti \in Thread:
        \/ EnqStart(Ti)
        \/ EnqTakesEffect(Ti)
        \/ EnqDone(Ti)
        \/ DeqStart(Ti)
        \/ DeqTakesEffect(Ti)
        \/ DeqDone(Ti)

Spec == Init /\ [][Next]_<<op,arg,rval,up,done,d>>
====