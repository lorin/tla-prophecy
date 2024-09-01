---- MODULE LinearizableQueue ----
EXTENDS Sequences

CONSTANTS Values,Threads,none 
VARIABLES op,arg,rval,up,done,d

ASSUME none \notin Values

EnqStart(t,x) == /\ done[t] 
                 /\ op' = [op EXCEPT ![t] = "enq"]
                 /\ arg' = [arg EXCEPT ![t] = x]
                 /\ rval' = [rval EXCEPT ![t] = none]
                 /\ up' = [up EXCEPT ![t] = FALSE]
                 /\ done' = [done EXCEPT ![t] = FALSE]
                 /\ UNCHANGED d

EnqTakesEffect(t,x) ==  /\ op[t]="enq"
                        /\ arg[t]=x
                        /\ ~done[t] 
                        /\ ~up[t]
                        /\ up' = [up EXCEPT ![t] = TRUE]
                        /\ d' = Append(d, x)
                        /\ UNCHANGED <<op,arg,rval,done>>

EnqEnd(t) == /\ op[t]="enq"
             /\ up[t]
             /\ ~done[t]
             /\ done' = [done EXCEPT ![t] = TRUE]
             /\ UNCHANGED <<op,arg,rval,up,d>>

DeqStart(t) == /\ done[t]
               /\ op' = [op EXCEPT ![t] = "deq"]
               /\ arg' = [arg EXCEPT ![t] = none]
               /\ rval' = [rval EXCEPT ![t] = none]
               /\ up' = [up EXCEPT ![t] = FALSE]
               /\ done' = [done EXCEPT ![t] = FALSE]
               /\ UNCHANGED d

DeqTakesEffect(t,x) == /\ op[t] = "deq"
                       /\ d # <<>>
                       /\ x=Head(d)
                       /\ ~up[t]
                       /\ ~done[t]
                       /\ rval' = [rval EXCEPT ![t]=x]
                       /\ up' = [up EXCEPT ![t] = TRUE]
                       /\ d' = Tail(d)
                       /\ UNCHANGED <<op,arg,done>>


DeqEnd(t,x) == /\ op[t] = "deq"
               /\ rval[t]=x
               /\ up[t]
               /\ ~done[t]
               /\ done' = [done EXCEPT ![t] = TRUE]
               /\ UNCHANGED <<op,arg,rval,up,d>>

Init == /\ op = [t \in Threads |-> ""]
        /\ arg = [t \in Threads |-> none]
        /\ rval = [t \in Threads |-> none]
        /\ up = [t \in Threads |-> TRUE]
        /\ done = [t \in Threads |-> TRUE]
        /\ d = <<>>

Next == \E t \in Threads, x \in Values:
        \/ EnqStart(t,x)
        \/ EnqTakesEffect(t,x)
        \/ EnqEnd(t)
        \/ DeqStart(t)
        \/ DeqTakesEffect(t,x)
        \/ DeqEnd(t,x)

Spec == Init /\ [][Next]_<<op,arg,rval,up,done,d>>
====