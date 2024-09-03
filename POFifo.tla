---- MODULE POFifo ----
CONSTANTS EnQers, DeQers, Data, Busy, Done, Ids
VARIABLES enq,deq

IPOFifo(elts,before,adding) == INSTANCE IPOFifo

Spec == \EE elts,before,adding : IPOFifo(elts,before,adding)

====