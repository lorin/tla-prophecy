----------------------------- MODULE QueueRepP -----------------------------
(***************************************************************************
We prophecize the ordering of the consumer writes to the "rep" array.

Specifically, we predict:
- the ordering that the consumer writes to effect
- the indexes of those writes

 ***************************************************************************)
 
EXTENDS QueueRep


(***************************************************************************
The set of consumers whose writes have not yet taken effect. 
 ***************************************************************************)

pendingConsumers == {c \in Consumers : /\ pc[c] \notin {"D8","D9","DONE"} 
                                       /\ pc[c]="D6" => rep.items[i[c]] = null
                                       /\ pc[c]="D7" => rVal[c] = null}
 


=============================================================================
\* Modification History
\* Last modified Wed Oct 31 21:13:43 PDT 2018 by lhochstein
\* Created Wed Oct 31 21:07:38 PDT 2018 by lhochstein
