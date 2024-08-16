------------------------------- MODULE Queue -------------------------------
(***************************************************************************)
(* A high-level specification for a sequential queue                       *)
(***************************************************************************)

EXTENDS Sequences, Naturals

CONSTANTS Val, null, Producers, Consumers

ASSUME null \notin Val

(*
--algorithm Queue {
    variable items = << >>


    \*
    \* Enq(x)
    \* 
    process (producer \in Producers)
    variable x \in Val;
    {
      E: 
          items := Append(items, x);
    }

    \*
    \* Deq() -> retVal
    \*
    process (consumer \in Consumers) 
    variable retVal = null;
    {
        D:
            await items /= <<>>;
            retVal := Head(items);
            items := Tail(items);
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "8edcca63" /\ chksum(tla) = "772e8152")
VARIABLES pc, items, x, retVal

vars == << pc, items, x, retVal >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ items = << >>
        (* Process producer *)
        /\ x \in [Producers -> Val]
        (* Process consumer *)
        /\ retVal = [self \in Consumers |-> null]
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "E"
                                        [] self \in Consumers -> "D"]

E(self) == /\ pc[self] = "E"
           /\ items' = Append(items, x[self])
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << x, retVal >>

producer(self) == E(self)

D(self) == /\ pc[self] = "D"
           /\ items # <<>>
           /\ retVal' = [retVal EXCEPT ![self] = Head(items)]
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
