---- MODULE LinearizableQueue ----
EXTENDS Sequences

CONSTANTS Values,Threads,none 
VARIABLES op,arg,rval,up,done,d

ASSUME none \notin Values

EnqStart(t) == /\ done[t] 
                 /\ op' = [op EXCEPT ![t] = "enq"]
                 /\ \E x \in Values: arg' = [arg EXCEPT ![t] = x]
                 /\ rval' = [rval EXCEPT ![t] = none]
                 /\ up' = [up EXCEPT ![t] = FALSE]
                 /\ done' = [done EXCEPT ![t] = FALSE]
                 /\ UNCHANGED d

EnqTakesEffect(t) ==  /\ op[t] = "enq"
                      /\ ~done[t] 
                      /\ ~up[t]
                      /\ \E x \in Values:
                          /\ arg[t] = x
                          /\ d' = Append(d, x)
                      /\ up' = [up EXCEPT ![t] = TRUE]
                      /\ UNCHANGED <<op,arg,rval,done>>

EnqEnd(t) == /\ op[t] = "enq"
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

DeqTakesEffect(t) == /\ op[t] = "deq"
                       /\ d # <<>>
                       /\ ~up[t]
                       /\ ~done[t]
                       /\ \E x \in Values: 
                            /\ x = Head(d)
                            /\ rval' = [rval EXCEPT ![t]=x]
                       /\ up' = [up EXCEPT ![t] = TRUE]
                       /\ d' = Tail(d)
                       /\ UNCHANGED <<op,arg,done>>

DeqEnd(t) == /\ op[t] = "deq"
               /\ \E x \in Values: rval[t] = x
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

Next == \E t \in Threads:
        \/ EnqStart(t)
        \/ EnqTakesEffect(t)
        \/ EnqEnd(t)
        \/ DeqStart(t)
        \/ DeqTakesEffect(t)
        \/ DeqEnd(t)

Spec == Init /\ [][Next]_<<op,arg,rval,up,done,d>>
====