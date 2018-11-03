----------------------------- MODULE QueueRepP -----------------------------
(***************************************************************************
We prophecize the ordering of the consumer writes to the "rep" array.

Specifically, we predict:
- the ordering that the consumer writes to effect
- the indexes of those writes

The prophecy variable is an ordered list of conumer writes. Each element
is a tuple: (consumer process id, write index)

 ***************************************************************************)
 
EXTENDS QueueRep, FiniteSets, Utilities, TLC


\* A consumer is committed to a course of action. It has already written
hasCommitted(c) == \/ pc[c] \in {"D8","D9","DONE"} 
                   \/ /\ pc[c] = "D7"
                      /\ rVal[c] /= null

(***************************************************************************
The set of consumers whose writes have not yet taken effect. 
 ***************************************************************************)
pendingConsumers == {c \in Consumers : ~hasCommitted(c)}

numPendingConsumers == Cardinality(pendingConsumers)


Pi == LET orderings == Perms(Consumers)
          indexSets == {y \in SUBSET(1..Cardinality(Producers)): Cardinality(y)=Cardinality(Consumers)}
          indexes == UNION({Perms(y) : y \in indexSets})
      IN {Zip(y[1], y[2]): y \in orderings \X indexes}

Dom == {1}

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
      [] goal < bar -> (CASE pcCons \in {"C1", "D1", "D2", "D3", "D4"} -> FALSE
                               [] pcCons \in {"D5", "D6"} -> iCons>goal /\ iCons<=bar
                               [] pcCons \in {"D7","D10"} -> iCons>=goal /\ iCons<bar
                               [] pcCons \in {"D8", "D9", "Done"} -> FALSE) \* already read
      [] goal > bar -> (CASE pcCons \in {"C1", "D1", "D2", "D3", "D4"} -> TRUE
                               [] pcCons \in {"D5", "D6"} -> iCons<=bar \/ iCons>goal
                               [] pcCons \in {"D7","D10"} -> iCons<bar \/ iCons>=goal
                               [] pcCons \in {"D8", "D9", "Done"} -> FALSE) \* already read

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
    \/ ~\E j \in 1..numPendingConsumers : p[1][j][2] = prodInd  \* There is no consumer who will read my write
    \/ LET myConsumerRank == CHOOSE j \in 1..numPendingConsumers : p[1][j][2] = prodInd
           consumerRank == CHOOSE j \in 1..numPendingConsumers: p[1][j][1] = cons
       IN consumerRank < myConsumerRank

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
PredDomE3 == {1}
PredE3(p, prod) == 
    \A cons \in Consumers :
     CouldReadMyWrite(cons, i_[prod], p) => 
        LET j == CHOOSE j \in 1..Cardinality(Producers) : p[1][j][1]=cons
            consInd == p[1][j][2]
            \* If the consumer hasn't committed to a course of action, it can't
            \* block another consumer that is supposed to commit earlier
         IN ~hasCommitted(cons) => ~IsBlocking(i[cons], pc[cons], consInd, i_[prod])
             
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


next == Cardinality({c \in Consumers: hasCommitted(c)}) + 1

DomInjD6 == IdFcn(Dom)
PredDomD6 == {} 
PredD6(p, cons) == 
         \* We're next, and we are in the correct place to write
         LET ourRank == CHOOSE j \in 1..Cardinality(Consumers) : p[1][j][1] = cons
             ourLocationToWrite == p[1][ourRank][2]
             isOurTurnToWrite == ourRank = next
             ourCurrentLocation == i_[cons]
             locationIsPopulated == rep.items[ourCurrentLocation] /= null
         IN CASE /\ isOurTurnToWrite
                 /\ ourLocationToWrite = ourCurrentLocation
                 /\ locationIsPopulated -> TRUE \* right place at the right time!
              [] /\ ~isOurTurnToWrite
                 /\ ourLocationToWrite = ourCurrentLocation
                 /\ locationIsPopulated -> FALSE \*right place at the wrong time!
              [] /\ ourLocationToWrite /= ourCurrentLocation
                 /\ locationIsPopulated -> FALSE \* wrong place!
                 \* Right place but not populated yet. If a lower ranked
                 \* consumer's location has been written, we can't advance
              [] /\ isOurTurnToWrite
                 /\ ourLocationToWrite = ourCurrentLocation
                 /\ ~locationIsPopulated -> ~\E j \in ourRank+1..Cardinality(Consumers): rep.items[p[1][j][2]] /= null
              [] OTHER -> TRUE


DomInjD7 == IdFcn(Dom)
PredDomD7 == {} 
PredD7(p) == TRUE

DomInjD8 == IdFcn(Dom)
PredDomD8 == {} 
PredD8(p) == TRUE

DomInjD9 == IdFcn(Dom)
PredDomD9 == {} 
PredD9(p) == TRUE

DomInjD10 == IdFcn(Dom)
PredDomD10 == {} 
PredD10(p) == TRUE

Condition ==
    /\ \A pr \in Producers: ProphCondition(E1(pr), DomInjE1, PredDomE1, PredE1)
    /\ \A pr \in Producers: ProphCondition(E2(pr), DomInjE2, PredDomE2, PredE2)
    /\ \A pr \in Producers: ProphCondition(E3(pr), DomInjE3, PredDomE3, LAMBDA p: PredE3(p, pr))
=============================================================================
\* Modification History
\* Last modified Fri Nov 02 17:12:04 PDT 2018 by lhochstein
\* Created Wed Oct 31 21:07:38 PDT 2018 by lhochstein
