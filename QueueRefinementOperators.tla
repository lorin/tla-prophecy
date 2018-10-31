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

DomInjE3 == IdFcn(Dom)
PredDomE3 == {}
PredE3(p, prod) == \A cons \in Consumers :
    (/\ CouldReadMyWrite(cons, i_[prod], p)
     /\ pc[cons] \notin {"D8", "D9", "Done"}) => ~IsBlocking(i[cons], pc[cons], p[cons].ind, i_[prod])

=============================================================================
\* Modification History
\* Last modified Tue Oct 30 20:04:36 PDT 2018 by lhochstein
\* Created Tue Oct 30 19:35:10 PDT 2018 by lhochstein
