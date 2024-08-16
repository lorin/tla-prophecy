(***************************************************************************)
(*                                                                         *)
(* Queue representation type (REP) from Herlihy & Wing 1990.               *)
(* Includes prophecy variables.                                            *)
(***************************************************************************)
------------------------------ MODULE QueueRepProphecy -----------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS Val, Producers, Consumers, Nmax

null == CHOOSE x : x \notin Val

(*
--algorithm Rep {

variables rep = [back|->1, items|->[n \in 1..Nmax|->null]],
          ps = <<>>;

macro INC(x) { x := x+1 || INC_return := x }
macro STORE(loc, val) { loc := val }
macro READ(ind) { READ_return := ind }
macro SWAP(loc, val) { loc := val || SWAP_return := loc }

\*
\* Enq(item)
\*
process (producer \in Producers) 
variables
    item \in Val,
    p \in Val, \* prophecy variable
    i, INC_return; {
E1:  INC(rep.back);
     i := INC_return;
     ps := Append(ps, p);
E2:  STORE(rep.items[i], item);
}

\*
\* Deq() -> Deq_return
\*
process (consumer \in Consumers) 
variables i, x, range, READ_return, SWAP_return, Deq_return {
D1: while(TRUE) {
D2:   READ(rep.back);
D3:   range := READ_return-1;
D4:   i := 1;
D5:   while(i<=range) {
D6:     SWAP(rep.items[i], null);
D7:     x := SWAP_return;
        if(x /= null) {
D8:       await Head(ps) = x;
          ps := Tail(ps);
          Deq_return := x;
D9:       goto "Done"
        };
D10:    i:= i+1
      }
    }
}

}
*)
\* BEGIN TRANSLATION
\* Process variable i of process producer at line 31 col 5 changed to i_
CONSTANT defaultInitValue
VARIABLES pc, rep, ps, item, p, i_, INC_return, i, x, range, READ_return, 
          SWAP_return, Deq_return

vars == << pc, rep, ps, item, p, i_, INC_return, i, x, range, READ_return, 
           SWAP_return, Deq_return >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ rep = [back|->1, items|->[n \in 1..Nmax|->null]]
        /\ ps = <<>>
        (* Process producer *)
        /\ item \in [Producers -> Val]
        /\ p \in [Producers -> Val]
        /\ i_ = [self \in Producers |-> defaultInitValue]
        /\ INC_return = [self \in Producers |-> defaultInitValue]
        (* Process consumer *)
        /\ i = [self \in Consumers |-> defaultInitValue]
        /\ x = [self \in Consumers |-> defaultInitValue]
        /\ range = [self \in Consumers |-> defaultInitValue]
        /\ READ_return = [self \in Consumers |-> defaultInitValue]
        /\ SWAP_return = [self \in Consumers |-> defaultInitValue]
        /\ Deq_return = [self \in Consumers |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "E1"
                                        [] self \in Consumers -> "D1"]

E1(self) == /\ pc[self] = "E1"
            /\ /\ INC_return' = [INC_return EXCEPT ![self] = rep.back]
               /\ rep' = [rep EXCEPT !.back = (rep.back)+1]
            /\ i_' = [i_ EXCEPT ![self] = INC_return'[self]]
            /\ ps' = Append(ps, p[self])
            /\ pc' = [pc EXCEPT ![self] = "E2"]
            /\ UNCHANGED << item, p, i, x, range, READ_return, SWAP_return, 
                            Deq_return >>

E2(self) == /\ pc[self] = "E2"
            /\ rep' = [rep EXCEPT !.items[i_[self]] = item[self]]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << ps, item, p, i_, INC_return, i, x, range, 
                            READ_return, SWAP_return, Deq_return >>

producer(self) == E1(self) \/ E2(self)

D1(self) == /\ pc[self] = "D1"
            /\ pc' = [pc EXCEPT ![self] = "D2"]
            /\ UNCHANGED << rep, ps, item, p, i_, INC_return, i, x, range, 
                            READ_return, SWAP_return, Deq_return >>

D2(self) == /\ pc[self] = "D2"
            /\ READ_return' = [READ_return EXCEPT ![self] = rep.back]
            /\ pc' = [pc EXCEPT ![self] = "D3"]
            /\ UNCHANGED << rep, ps, item, p, i_, INC_return, i, x, range, 
                            SWAP_return, Deq_return >>

D3(self) == /\ pc[self] = "D3"
            /\ range' = [range EXCEPT ![self] = READ_return[self]-1]
            /\ pc' = [pc EXCEPT ![self] = "D4"]
            /\ UNCHANGED << rep, ps, item, p, i_, INC_return, i, x, 
                            READ_return, SWAP_return, Deq_return >>

D4(self) == /\ pc[self] = "D4"
            /\ i' = [i EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "D5"]
            /\ UNCHANGED << rep, ps, item, p, i_, INC_return, x, range, 
                            READ_return, SWAP_return, Deq_return >>

D5(self) == /\ pc[self] = "D5"
            /\ IF i[self]<=range[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "D6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << rep, ps, item, p, i_, INC_return, i, x, range, 
                            READ_return, SWAP_return, Deq_return >>

D6(self) == /\ pc[self] = "D6"
            /\ /\ SWAP_return' = [SWAP_return EXCEPT ![self] = rep.items[i[self]]]
               /\ rep' = [rep EXCEPT !.items[i[self]] = null]
            /\ pc' = [pc EXCEPT ![self] = "D7"]
            /\ UNCHANGED << ps, item, p, i_, INC_return, i, x, range, 
                            READ_return, Deq_return >>

D7(self) == /\ pc[self] = "D7"
            /\ x' = [x EXCEPT ![self] = SWAP_return[self]]
            /\ IF x'[self] /= null
                  THEN /\ pc' = [pc EXCEPT ![self] = "D8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D10"]
            /\ UNCHANGED << rep, ps, item, p, i_, INC_return, i, range, 
                            READ_return, SWAP_return, Deq_return >>

D8(self) == /\ pc[self] = "D8"
            /\ Head(ps) = x[self]
            /\ ps' = Tail(ps)
            /\ Deq_return' = [Deq_return EXCEPT ![self] = x[self]]
            /\ pc' = [pc EXCEPT ![self] = "D9"]
            /\ UNCHANGED << rep, item, p, i_, INC_return, i, x, range, 
                            READ_return, SWAP_return >>

D9(self) == /\ pc[self] = "D9"
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << rep, ps, item, p, i_, INC_return, i, x, range, 
                            READ_return, SWAP_return, Deq_return >>

D10(self) == /\ pc[self] = "D10"
             /\ i' = [i EXCEPT ![self] = i[self]+1]
             /\ pc' = [pc EXCEPT ![self] = "D5"]
             /\ UNCHANGED << rep, ps, item, p, i_, INC_return, x, range, 
                             READ_return, SWAP_return, Deq_return >>

consumer(self) == D1(self) \/ D2(self) \/ D3(self) \/ D4(self) \/ D5(self)
                     \/ D6(self) \/ D7(self) \/ D8(self) \/ D9(self)
                     \/ D10(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Producers: producer(self))
           \/ (\E self \in Consumers: consumer(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

NotDone == ~(\A self \in ProcSet: pc[self] = "Done")

pcBar == [c \in Producers \union Consumers |->
    CASE pc[c] \in {"P1", "E1"} -> "E"
      [] pc[c] \in {"C1", "D1", "D2", "D3", "D4", "D5", "D6", "D7", "D8", "D10"} -> "D"
      [] pc[c] \in {"E2", "E3", "D9", "Done"} -> "Done"
]
itemsBar == ps
xBar == p
rBar == [c \in Consumers |-> IF pc[c] \in {"D9", "Done"} THEN Deq_return[c] ELSE null]

Mapping ==
    INSTANCE Queue WITH
        pc <- pcBar,
        items <- itemsBar,
        x <- xBar,
        r <- rBar

Refinement == Mapping!Spec

Alias == [
    pcBar |-> pcBar,
    itemsBar |-> itemsBar,
    xBar |-> xBar,
    rBar |-> rBar,
    INC_return |-> INC_return,
    SWAP_return |-> SWAP_return,
    Deq_return |-> Deq_return,
    i |-> i,
    p |-> p,
    x |-> x,
    pc |-> pc,
    rep |-> rep,
    READ_return |-> READ_return,
    range |-> range,
    i_ |-> i_
]

=============================================================================
\* Modification History
\* Last modified Thu Nov 08 17:28:50 PST 2018 by lhochstein
\* Created Wed Oct 24 18:53:25 PDT 2018 by lhochstein
