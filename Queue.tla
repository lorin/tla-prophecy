---- MODULE queue ----
EXTENDS Sequences

CONSTANTS Values,none
VARIABLES op,arg,rval,d

ASSUME none \notin Values

Enq ==  /\ op' = "enq"
        /\ rval' = none
        /\ arg' \in Values
        /\ d' = Append(d, arg')

Deq == /\ d # <<>>
       /\ op' = "deq"
       /\ arg' = none
       /\ rval' = Head(d)
       /\ d' = Tail(d)

Init == /\ op = ""
        /\ arg = none
        /\ rval = none
        /\ d = <<>>

Next == Enq \/ Deq

Spec == Init /\ [][Next]_<<op,arg,rval,d>>

====