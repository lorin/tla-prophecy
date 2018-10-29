-------------------------- MODULE QueueRefinement --------------------------
EXTENDS QueueRep,Utilities

VARIABLES proph, \* Prophecized orderig of producers
          itemsBar \* abstraction function for the queue
          
\* True if barrier stands between the consumer (where i=iCons, and pc=pcCons) and its goal location
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
          
varsP == <<vars, proph, itemsBar>>
InitP == /\ Init
         /\ LET numProducers(s) == Cardinality({j \in 1..Len(s) : s[j] \in Producers})
                numConsumers(s) == Cardinality({j \in 1..Len(s) : s[j] \in Consumers})
                alwaysEnoughProducers(s) == \A j \in 1..Len(s) : LET ss == SubSeq(s, 1,j) IN numProducers(ss) \geq numConsumers(ss)
                producerMustPrecedeConsumer(s, prod, cons) ==
                    \A j \in 1..Len(s) :
                        (s[j] \in Consumers) => \E k \in 1..j-1 :
                            /\ s[k] \in Producers
                            /\ cons[s[j]] = prod[s[k]]
                ord == {s \in Perms(Producers \union Consumers) : alwaysEnoughProducers(s) }
                OneToOne(f) == \A s,t \in DOMAIN f : f[s] = f[t] => s=t
                prod == LET N == Cardinality(Producers) IN {f \in [Producers -> 1..N] : OneToOne(f)}
                cons == LET N == Cardinality(Consumers) IN {f \in [Consumers -> 1..N] : OneToOne(f)}
                IN proph \in {r \in [ord:ord, prod:prod, cons:cons, next:{1}] : producerMustPrecedeConsumer(r.ord, r.prod, r.cons)}
         /\ itemsBar = << >>
         
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

EnqP(self) == E1P(self) \/ E2P(self) \/ E3P(self) \/ E4P(self)

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


DeqP(self) == D1P(self) \/ D2P(self) \/ D3P(self) \/ D4P(self) \/ D5P(self)
                \/ D6P(self) \/ D7P(self) \/ D8P(self) \/ D9P(self)
                \/ D10P(self)

P1P(self) == P1(self) /\ UNCHANGED <<proph, itemsBar>>

pP(self) == P1P(self)

C1P(self) == C1(self) /\ UNCHANGED <<proph, itemsBar>>

cP(self) == C1P(self)

NextP == (\E self \in ProcSet: EnqP(self) \/ DeqP(self))
           \/ (\E self \in Producers: pP(self))
           \/ (\E self \in Consumers: cP(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED varsP)


SpecP == /\ InitP /\ [][NextP]_varsP
         /\ \A self \in Producers : WF_vars(pP(self)) /\ WF_vars(EnqP(self))
         /\ \A self \in Consumers : WF_vars(cP(self)) /\ WF_vars(DeqP(self))


Q == INSTANCE Queue WITH items<-itemsBar

=============================================================================
\* Modification History
\* Last modified Sun Oct 28 19:29:38 PDT 2018 by lhochstein
\* Created Sat Oct 27 12:02:21 PDT 2018 by lhochstein
