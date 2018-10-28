-------------------------- MODULE QueueRefinement --------------------------
EXTENDS QueueRep,Utilities

VARIABLES proph, \* Prophecized orderig of producers
          absQ \* abstraction function for the queue
varsP == <<vars, proph, absQ>>
InitP == /\ Init
         /\ LET perms == Perms(Producers)
            IN proph \in {f \in [ord:perms, toEnq:perms, toDeq:perms] : f.ord = f.toEnq /\ f.ord = f.toDeq}
         /\ absQ = << >>
         

EnqueueAbs(self, val) == IF Head(proph.ord) = self
                         THEN /\ proph' = [proph EXCEPT !["toEnq"] = Tail(@)]
                              /\ absQ' = Append(absQ, val)
                         ELSE UNCHANGED <<proph, absQ>>

\* set of indexes into the queue for consumer processes that have not
\* committed to a dequeue yet
pendingConsumerIndexes == {i[c] : c \in Consumers /\ pc[c] \notin {"D7", "D8", "D9", "Done"}} 

\* set of orderings (ordered pair of producers) relative to a pending consumer process
\* at index i
\* 

\* TODO: I am here!
repOrderingAtConsumerIndex(q, i) ==
    LET afterIndex == {}
        beforeIndex == {}
        acrossIndex == {}
    IN afterIndex \union beforeIndex \union acrossIndex


ConsistentWithProphecy(q) == 
    LET repOrdering = UNION({repOrderingAtConsumerIndex(q, j) : j \in pendingConsumerIndexes})
        prophecyOrdering = {t \in Producers \X Producers : \E j,k \in 1..Len(proph.ord) : /\ j<k 
    IN  repOrdering \subseteq prophecyOrdering

E1P(self) == E1(self) /\ EnqueueAbs(self, x[self])

E2P(self) == E2(self) /\ UNCHANGED <<proph, absQ>>

E3P(self) == E3(self) /\ EnqueueAbs(self, x[self]) /\ ConsistentWithProphecy(rep')

E4P(self) == E4(self) /\ UNCHANGED <<proph, absQ>>

EnqP(self) == E1P(self) \/ E2P(self) \/ E3P(self) \/ E4P(self)

D1P(self) == D1(self) /\ UNCHANGED <<proph, absQ>>

D2P(self) == D2(self) /\ UNCHANGED <<proph, absQ>>

D3P(self) == D3(self) /\ UNCHANGED <<proph, absQ>>

D4P(self) == D4(self) /\ UNCHANGED <<proph, absQ>>

D5P(self) == D5(self) /\ UNCHANGED <<proph, absQ>>

D6P(self) == D6(self) /\ UNCHANGED <<proph, absQ>>

D7P(self) == D7(self) /\ UNCHANGED <<proph, absQ>>

D8P(self) == D8(self) /\ UNCHANGED <<proph, absQ>>

D9P(self) == D9(self) /\ UNCHANGED <<proph, absQ>>

D10P(self) == D10(self) /\ UNCHANGED <<proph, absQ>>


DeqP(self) == D1P(self) \/ D2P(self) \/ D3P(self) \/ D4P(self) \/ D5P(self)
                \/ D6P(self) \/ D7P(self) \/ D8P(self) \/ D9P(self)
                \/ D10P(self)

P1P(self) == P1(self) /\ UNCHANGED <<proph, absQ>>

pP(self) == P1P(self)

C1P(self) == C1(self) /\ UNCHANGED <<proph, absQ>>

cP(self) == C1P(self)

NextP == (\E self \in ProcSet: EnqP(self) \/ DeqP(self))
           \/ (\E self \in Producers: pP(self))
           \/ (\E self \in Consumers: cP(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED varsP)


SpecP == InitP /\ [][NextP]_varsP


Q == INSTANCE Queue WITH items<-absQ

=============================================================================
\* Modification History
\* Last modified Sat Oct 27 17:56:25 PDT 2018 by lhochstein
\* Created Sat Oct 27 12:02:21 PDT 2018 by lhochstein
