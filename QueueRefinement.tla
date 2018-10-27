-------------------------- MODULE QueueRefinement --------------------------
EXTENDS QueueRep, Sequences


Q == INSTANCE Queue WITH items<-SelectSeq(rep.items, LAMBDA item: item /= null)

=============================================================================
\* Modification History
\* Last modified Sat Oct 27 13:11:02 PDT 2018 by lhochstein
\* Created Sat Oct 27 12:02:21 PDT 2018 by lhochstein
