-------------------------- MODULE QueueRefinement --------------------------
EXTENDS QueueRep,Utilities

VARIABLES proph, \* Prophecized orderig of producers
          absQ \* abstraction function for the queue
varsP == <<vars, proph, absQ>>
InitP == /\ Init
         /\ LET numProducers(s) == Cardinality({j \in 1..Len(s) : s[j] \in Producers})
                numConsumers(s) == Cardinality({j \in 1..Len(s) : s[j] \in Consumers})
                ord == {s \in Perms(Producers \union Consumers) : \A j \in 1..Len(s) : LET ss == SubSeq(s, 1,j) IN numProducers(ss) \geq numConsumers(ss)}
                OneToOne(f) == \A s,t \in DOMAIN f : f[s] = f[t] => s=t
                fprod == LET N == Cardinality(Producers) IN {f \in [Producers -> 1..N] : OneToOne(f)}
                fcons == LET N == Cardinality(Consumers) IN {f \in [Consumers -> 1..N] : OneToOne(f)}
             IN proph \in [ord:ord, prod:fprod, cons:fcons]
         /\ absQ = << >>
         
E1P(self) == E1(self) /\ UNCHANGED <<proph, absQ>>

E2P(self) == E2(self) /\ UNCHANGED <<proph, absQ>>

E3P(self) == E3(self) /\ UNCHANGED <<proph, absQ>>

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
\* Last modified Sat Oct 27 20:17:36 PDT 2018 by lhochstein
\* Created Sat Oct 27 12:02:21 PDT 2018 by lhochstein
