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

BeginEnq(e) == /\ POFifo!BeginEnq(e)
               /\ \E el \in Values : p' = Append(p, el)

EndEnq(e) == /\ POFifo!EndEnq(e)
             /\ UNCHANGED p

BeginDeq(d) ==  /\ POFifo!BeginDeq(d)
                /\ UNCHANGED p

EndDeq(d) == /\ POFifo!EndDeq(d)
             /\ elts' = elts \ {p[1]}
             /\ p' = Tail(p)

Next == \/ \E e \in EnQers : \/ BeginEnq(e)
                             \/ EndEnq(e)
        \/ \E d \in DeQers :  \/ BeginDeq(d)
                              \/ EndDeq(d)


v == POFifo!v \o p
Spec == Init /\ [][Next]_v 

====