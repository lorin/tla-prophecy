---- MODULE POFifop ----
(*************************************************)
(*                                               *)
(* From Lamport's Science of Concurrent Programs *)
(*                                               *)
(* Augments POFifo with a prophecy variable.     *)
(*                                               *)
(*************************************************)
EXTENDS Sequences

CONSTANTS EnQers, DeQers, Data, Ids,
          Done, Busy, NonElt

VARIABLES
    (* external variables *)
    enq,deq,

    (* internal variables *)
    elts,before,adding,

    (* prophecy variable *)
    p

ASSUME Done \notin Data
ASSUME Busy \notin Data
ASSUME NonElt \notin (Data \X Ids)

POFifo == INSTANCE POFifo

Init == /\ POFifo!Init 
        /\ p = <<>>

Values == Data \X Ids

BeginPOEnq(e) == /\ POFifo!BeginPOEnq(e)
               /\ \E el \in Values : p' = Append(p, el)

EndPOEnq(e) == /\ POFifo!EndPOEnq(e)
             /\ UNCHANGED p

BeginPODeq(d) ==  /\ POFifo!BeginPODeq(d)
                /\ UNCHANGED p

EndPODeq(d) == /\ POFifo!EndPODeq(d)
             /\ elts' = elts \ {p[1]}
             /\ p' = Tail(p)

Next == \/ \E e \in EnQers : \/ BeginPOEnq(e)
                             \/ EndPOEnq(e)
        \/ \E d \in DeQers :  \/ BeginPODeq(d)
                              \/ EndPODeq(d)


v == POFifo!v \o p
Spec == Init /\ [][Next]_v 

====