-------------------------- MODULE QueueRefinement --------------------------
EXTENDS QueueRep,Utilities

(***************************************************************************
We use a sequence of dequeueing indexes as our prophecy variable. It predicts
the order in which data will be dequeued.
 ***************************************************************************)

Pi == 1..Cardinality(Producers)
Dom == 1..Cardinality(Consumers)

INSTANCE Prophecy WITH DomPrime<-Dom'


DomInjE1 == IdFcn(Dom)
PredDomE1 == {}
PredE1(p) == TRUE

DomInjE2 == IdFcn(Dom)
PredDomE2 == {}
PredE2(p) == TRUE

\* TODO: Beter constraints here
DomInjE3 == IdFcn(Dom)
PredDomE3 == {}
PredE3(p) == TRUE

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

\* TODO: better constraints here
DomInjD6 == IF p[1] = ind THEN [i \in 2..Cardinality(Len(p))|->i-1] ELSE IdFcn(Dom)
PredDomD6 == {1}
PredD6(p) == LET ind=i[self]
             IN rep.items[ind] = null \/ p[1] = ind

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

DomInjP1 == IdFcn(Dom)
PredDomP1 == {}
PredP1(p) == TRUE

DomInjC1 == IdFcn(Dom)
PredDomC1 == {}
PredC1(p) == TRUE

----------------------------------------------------------------------------


VARIABLES p, \* Prophecy
          itemsBar \* abstraction function for the queue

\* True if barrier stands between the consumer (where i=iCons, and pc=pcCons) and its goal location
(*
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

      
\* A consumer cons could read producer prod's write if cons is scheduled to read/write
\* before the consumer that reads prod's write
CouldReadMyWrite(cons, prod, pr) ==
    \/ ~\E co \in Consumers : pr.cons[co] = pr.prod[prod] \* No such consumer
    \/ LET consAssocWithProd == CHOOSE co \in Consumers : pr.cons[co] = pr.prod[prod]
        index(ps) == CHOOSE ind \in 1..Len(pr.ord) : pr.ord[ind] = ps
        IN index(cons) < index(consAssocWithProd)
 *)         
varsP == <<vars, p, itemsBar>>

OneToOne(f) == \A s,t \in DOMAIN f : f[s] = f[t] => s=t

InitP == /\ Init
         /\ p \in {f \in [Dom->Pi] : OneToOne(f)}
         /\ itemsBar = << >>
         

E1P(self) == ProphAction(E1(self), p, p', DomInjE1, PredDomE1, PredE1)
E2P(self) == ProphAction(E2(self), p, p', DomInjE2, PredDomE2, PredE2)
E3P(self) == ProphAction(E3(self), p, p', DomInjE3, PredDomE3, PredE3)
E4P(self) == ProphAction(E4(self), p, p', DomInjE4, PredDomE4, PredE4)
         
(*
         
E1P(self) == /\ E1(self)
             /\ proph.prod[self] = rep.back
             /\ UNCHANGED <<proph, itemsBar>>

E2P(self) == E2(self) /\ UNCHANGED <<proph, itemsBar>>

E3P(self) == /\ E3(self)
             /\ proph.ord[proph.next] = self
                \* Prevent blocking a consumer from getting to their proper destination
             /\ \A cons \in Consumers : (/\ proph.cons[cons] /= i_[self]
                                         /\ CouldReadMyWrite(cons,self,proph)
                                         /\ pc[cons] \notin {"D8", "D9", "Done"}) => ~IsBlocking(i[cons], pc[cons], proph.cons[cons], i_[self])
             /\ proph' = [proph EXCEPT !.next = @+1]
             /\ UNCHANGED itemsBar

E4P(self) == /\ E4(self)
             /\ UNCHANGED <<proph, itemsBar>>

*)
EnqP(self) == E1P(self) \/ E2P(self) \/ E3P(self) \/ E4P(self)


D1P(self) == ProphAction(D1(self), p, p', DomInjD1, PredDomD1, PredD1)
D2P(self) == ProphAction(D2(self), p, p', DomInjD2, PredDomD2, PredD2)
D3P(self) == ProphAction(D3(self), p, p', DomInjD3, PredDomD3, PredD3)
D4P(self) == ProphAction(D4(self), p, p', DomInjD4, PredDomD4, PredD4)
D5P(self) == ProphAction(D5(self), p, p', DomInjD5, PredDomD5, PredD5)
D6P(self) == ProphAction(D6(self), p, p', DomInjD6, PredDomD6, PredD6)
D7P(self) == ProphAction(D7(self), p, p', DomInjD7, PredDomD7, PredD7)
D8P(self) == ProphAction(D8(self), p, p', DomInjD8, PredDomD8, PredD8)
D9P(self) == ProphAction(D9(self), p, p', DomInjD9, PredDomD9, PredD9)
D10P(self) == ProphAction(D10(self), p, p', DomInjD10, PredDomD10, PredD10)


(*
D1P(self) == D1(self) /\ UNCHANGED <<proph, itemsBar>>

D2P(self) == D2(self) /\ UNCHANGED <<proph, itemsBar>>

D3P(self) == D3(self) /\ UNCHANGED <<proph, itemsBar>>

D4P(self) == D4(self) /\ UNCHANGED <<proph, itemsBar>>

D5P(self) == D5(self) /\ UNCHANGED <<proph, itemsBar>>

D6P(self) == /\ D6(self)
             /\ \/ /\ rep.items[i[self]] = null 
                   /\ proph.cons[self] = i[self] => \A j \in 1..rep.back : rep.items[j] = null 
                   /\ UNCHANGED <<proph, itemsBar>>
                \/ /\ rep.items[i[self]] /= null 
                   /\ proph.ord[proph.next] = self
                   /\ proph.cons[self] = i[self]
                   /\ proph' = [proph EXCEPT !.next = @+1]
                   /\ UNCHANGED itemsBar

D7P(self) == D7(self) /\ UNCHANGED <<proph, itemsBar>>

D8P(self) == D8(self) /\ UNCHANGED <<proph, itemsBar>>

D9P(self) == D9(self) /\ UNCHANGED <<proph, itemsBar>>

D10P(self) == D10(self) /\ UNCHANGED <<proph, itemsBar>>
*)


DeqP(self) == D1P(self) \/ D2P(self) \/ D3P(self) \/ D4P(self) \/
D5P(self) \/ D6P(self) \/ D7P(self) \/ D8P(self) \/ D9P(self) \/ D10P(self)

P1P(self) == ProphAction(P1(self), p, p', DomInjP1, PredDomP1, PredP1)

(*

P1P(self) == P1(self) /\ UNCHANGED <<proph, itemsBar>>
*)

producerP(self) == P1P(self)

C1P(self) == ProphAction(C1(self), p, p', DomInjC1, PredDomC1, PredC1)

(*
C1P(self) == C1(self) /\ UNCHANGED <<proph, itemsBar>>
*)

consumerP(self) == C1P(self)

NextP == (\E self \in ProcSet: EnqP(self) \/ DeqP(self))
           \/ (\E self \in Producers: producerP(self))
           \/ (\E self \in Consumers: consumerP(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED varsP)


SpecP == /\ InitP /\ [][NextP]_varsP
         /\ \A self \in Producers : WF_vars(producerP(self)) /\ WF_vars(EnqP(self))
         /\ \A self \in Consumers : WF_vars(consumerP(self)) /\ WF_vars(DeqP(self))


Q == INSTANCE Queue WITH items<-itemsBar

=============================================================================
\* Modification History
\* Last modified Sun Oct 28 22:19:34 PDT 2018 by lhochstein
\* Created Sat Oct 27 12:02:21 PDT 2018 by lhochstein
