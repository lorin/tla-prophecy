------------------------------- MODULE Queue -------------------------------
(***************************************************************************)
(* A high-level specification for a sequential queue                       *)
(***************************************************************************)

EXTENDS Sequences, Naturals

CONSTANTS Val, Nmax, null, Producers, Consumers

ASSUME null \notin Val

(*
--algorithm Queue {
    variable items = << >>

    process (producer \in Producers)
    variable x \in Val;
    {
      E: 
          await Len(items) < Nmax;
          items := <<x>> \o items;
    }

    process (consumer \in Consumers) 
    variable r = null;
    {
        D:
            await items # <<>>;
            r := Head(items);
            items := Tail(items);
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "7bc98894" /\ chksum(tla) = "70cd88ba")
VARIABLES pc, items, x, r

vars == << pc, items, x, r >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ items = << >>
        (* Process producer *)
        /\ x \in [Producers -> Val]
        (* Process consumer *)
        /\ r = [self \in Consumers |-> null]
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "E"
                                        [] self \in Consumers -> "D"]

E(self) == /\ pc[self] = "E"
           /\ Len(items) < Nmax
           /\ items' = <<x[self]>> \o items
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << x, r >>

producer(self) == E(self)

D(self) == /\ pc[self] = "D"
           /\ items # <<>>
           /\ r' = [r EXCEPT ![self] = Head(items)]
           /\ items' = Tail(items)
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ x' = x

consumer(self) == D(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Producers: producer(self))
           \/ (\E self \in Consumers: consumer(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Inv == items = <<>>
              

=============================================================================
\* Modification History
\* Last modified Thu Nov 08 19:07:01 PST 2018 by lhochstein
\* Created Fri Apr 20 23:43:41 PDT 2018 by lhochstein
