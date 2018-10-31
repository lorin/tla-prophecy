---------------------- MODULE QueueRefinementOperators ----------------------
(***************************************************************************

Our prophecy variable maps consumer process ids to records 

 ***************************************************************************)
EXTENDS QueueRep, FiniteSets
 
 \* For now, we'll just keep this constant. Later we might reduce this
 \* as threads get retired
 Dom == Consumers
 
 Pi == [order:1..Cardinality(Consumers), ind:1..Cardinality(Producers)]

=============================================================================
\* Modification History
\* Last modified Tue Oct 30 19:39:49 PDT 2018 by lhochstein
\* Created Tue Oct 30 19:35:10 PDT 2018 by lhochstein
