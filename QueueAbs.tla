------------------------------ MODULE QueueAbs ------------------------------
(***************************************************************************)
(* Abstraction function for queue representation, as described in          *)
(* Herlihy & Wing 1990                                                     *)
(***************************************************************************)
EXTENDS Naturals, Sequences, TLC

CONSTANT Values

null == CHOOSE x : x \notin Values

\* Remove an element from the domain of a function
f -- xp == [x \in DOMAIN f \ {xp} |-> f[x]]

RECURSIVE lin(_, _, _, _) 

(***************************************************************************)
(* Return set of linearizations                                            *)
(*                                                                         *)
(* ind: index of reader                                                    *)
(* writes: function that map indexes to values that have been written      *)
(* pending: function that map indexes to values that are pending to be written *)
(* reads: set of indexes of locations of readers (other than read)         *)
(***************************************************************************)
RECURSIVE linr(_, _, _, _, _)
linr(i, writes, pending, reads, max) ==
         \* base case
    CASE DOMAIN writes = {} /\ DOMAIN pending = {} -> {<< >>} 
         \* only pendings are left. To ensure the recursion terminates, need
         \* to handle the cases where the pendings never take effect, or
         \* each one takes effect
      [] DOMAIN writes = {} /\ DOMAIN pending /= {} -> {<< >>} \union
          UNION({linr(i, writes @@ x:>pending[x], pending--x, reads, max): x \in DOMAIN pending})
         \* ind corresponds to a written value
      [] i \in DOMAIN writes -> UNION({<<writes[i]>> \o s : s \in lin(writes -- i, pending, reads, max)})
         \* ind corresponds to a pending value
      [] i \in DOMAIN pending -> UNION({<<pending[i]>> \o s : s \in lin(writes, pending -- i, reads, max) })
         \union linr(i+1,writes,pending,reads, max)
      [] i \notin DOMAIN(writes) \union DOMAIN(pending) /\ i=max -> linr(1,writes,pending,reads,max)
      [] OTHER -> linr(i+1,writes,pending,reads,max)

(***************************************************************************)
(* Set of linearizations                                                   *)
(*                                                                         *)
(* writes: function that map indexes to values that have been written      *)
(* pending: function that map indexes to values that are pending to be     *)
(*          written                                                        *)
(* reads: indexes of location of readers                                   *)
(* max: max value for the array                                            *)
(***************************************************************************)
lin(writes, pending, reads, max) ==
    IF DOMAIN reads = {} THEN linr(1,writes,pending,{}, max)
    ELSE UNION({linr(r,writes,pending,reads \ {r}, max) : r \in reads})


(***************************************************************************)
(* Abs identifies the set of legal linearized values for the given         *)
(* state of the queue.                                                     *)
(***************************************************************************)
Abs(queue,pending,reads) ==
    LET max == queue.back-1
        domain == {ind \in 1..max : queue.items[ind] /= null}
        writes == [d \in domain |-> queue.items[d]]
    IN lin(writes,pending,reads,max)
    
   
Empty == Abs([items|-><<null,null>>, back|->1], << >>, << >>)

=============================================================================
\* Modification History
\* Last modified Sat Nov 03 15:25:28 PDT 2018 by lhochstein
\* Created Fri Nov 02 21:52:24 PDT 2018 by lhochstein
