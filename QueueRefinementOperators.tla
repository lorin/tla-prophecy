---------------------- MODULE QueueRefinementOperators ----------------------
EXTENDS QueueRep, FiniteSets
 
(***************************************************************************
Our prophecy variable maps consumer process ids to records that indicate the
order in which the dequeue will happen, and the index into the rep array
where the dequeues will happen
 ***************************************************************************)
 Dom == Consumers
 Pi == [order:1..Cardinality(Consumers), ind:1..Cardinality(Producers)]

INSTANCE Prophecy WITH DomPrime<-Dom'


(***************************************************************************)
(* True if barrier stands between the consumer and its goal location.      *)
(*                                                                         *)
(* iCons is the index of the consumer process in the array.                *)
(*                                                                         *)
(* pcCons is the pc of the consumer.                                       *)
(*                                                                         *)
(* We use this to check if a producer writing into the array would violate *)
(* the prophecy.                                                           *)
(***************************************************************************)
IsBlocking(iCons, pcCons, goal, bar) == 
    CASE goal = bar -> FALSE \* Can't block if we are the goal!
      [] goal < bar ->  CASE pcCons \in {"C1", "D1", "D2", "D3", "D4"} -> FALSE
                               [] pcCons \in {"D5", "D6"} -> iCons>goal /\ iCons<=bar
                               [] pcCons \in {"D7","D10"} -> iCons>=goal /\ iCons<bar
                               [] pcCons \in {"D8", "D9", "Done"} -> FALSE \* already read
      [] goal > bar -> CASE pcCons \in {"C1", "D1", "D2", "D3", "D4"} -> TRUE
                               [] pcCons \in {"D5", "D6"} -> iCons<=bar \/ iCons>goal
                               [] pcCons \in {"D7","D10"} -> iCons<bar \/ iCons>=goal
                               [] pcCons \in {"D8", "D9", "Done"} -> FALSE \* already read

(***************************************************************************)
(* Precondition check to see if we need to check the isBlocking condition  *)
(*                                                                         *)
(* We only need to do the blocking check if it is possible that a producer *)
(* writing at prodInd could be written by the consumer cons.               *)
(*                                                                         *)
(* It's impossible if the consumer associated with the producer is         *)
(* scheduled first. In that case, the write will be nulled out.            *)
(*                                                                         *)
(* If there is no such consumer, or if the consumer associated with the    *)
(* producer will be scheduled later than "cons", then there is a risk that *)
(* the write could be read.                                                *)
(***************************************************************************)
CouldReadMyWrite(cons, prodInd, p) ==
    \/ ~\E c \in Consumers : p.ind[c] = prodInd  \* There is no consumer who will read my write
    \/ LET consAssocWithProd == CHOOSE c \in Consumers : p[c].ind = prodInd
       IN p.ord[cons] < p.ord[consAssocWithProd]
    

DomInjE1 == IdFcn(Dom)
PredDomE1 == {}
PredE1(p) == TRUE

DomInjE2 == IdFcn(Dom)
PredDomE2 == {}
PredE2(p) == TRUE

(***************************************************************************)
(* This is the action for the producer (enqueue) to write to the rep       *)
(* array.                                                                  *)
(*                                                                         *)
(* We need to verify that the write doesn't violate the prophecy.          *)
(***************************************************************************)
DomInjE3 == IdFcn(Dom)
PredDomE3 == {}
PredE3(p, prod) == \A cons \in Consumers :
    (/\ CouldReadMyWrite(cons, i_[prod], p)
     /\ pc[cons] \notin {"D8", "D9", "Done"}) => ~IsBlocking(i[cons], pc[cons], p[cons].ind, i_[prod])

DomInjE4 == IdFcn(Dom)
PredDomE4 == {}
PredE4(p) == TRUE

DomInjD1 == IdFcn(Dom)
PredDomD1 == {}
PredD1(p) == TRUE

DomInjD2 == IdFcn(Dom)
PredDomD2 == {}
PredD2(p) == TRUE

DomInjD3 == IdFcn(Dom)
PredDomD3 == {}
PredD3(p) == TRUE

DomInjD4 == IdFcn(Dom)
PredDomD4 == {}
PredD4(p) == TRUE

DomInjD5 == IdFcn(Dom)
PredDomD5 == {}
PredD5(p) == TRUE

(***************************************************************************
This is the action for the consumer (dequeue) to atomically swap an element
of the rep array with null.

If the element of the rep array is null, and this is where we are supposed
to read, we need to make sure we can come all of the way back to this
element (i.e., there are all nulls elsewhere)

If the element of the rep array isn't null, we need to make sure that this
is where we are supposed to read, and that it's our turn.
 ***************************************************************************)
DomInjD6 == IdFcn(Dom)
PredDomD6 == {}
PredD6(p, cons) == TRUE

=============================================================================
\* Modification History
\* Last modified Tue Oct 30 20:15:32 PDT 2018 by lhochstein
\* Created Tue Oct 30 19:35:10 PDT 2018 by lhochstein
