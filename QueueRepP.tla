----------------------------- MODULE QueueRepP -----------------------------
(***************************************************************************
We prophecize the ordering of the consumer writes to the "rep" array.

Specifically, we predict:
- the ordering that the consumer writes to effect
- the indexes of those writes

 ***************************************************************************)
 
EXTENDS QueueRep, FiniteSets, Utilities



(***************************************************************************
The set of consumers whose writes have not yet taken effect. 
 ***************************************************************************)

pendingConsumers == {c \in Consumers : /\ pc[c] \notin {"D8","D9","DONE"} 
                                       /\ pc[c]="D6" => rep.items[i[c]] = null
                                       /\ pc[c]="D7" => rVal[c] = null}

Pi == LET orderings == Perms(Consumers)
          indexSets == {y \in SUBSET(1..Cardinality(Producers)): Cardinality(y)=Cardinality(Consumers)}
          indexes == UNION({Perms(y) : y \in indexSets})
      IN {Zip(y[1], y[2]): y \in orderings \X indexes}
Dom == 1..Cardinality(pendingConsumers)

=============================================================================
\* Modification History
\* Last modified Wed Oct 31 22:01:43 PDT 2018 by lhochstein
\* Created Wed Oct 31 21:07:38 PDT 2018 by lhochstein
