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

macro INC(x) { x := x+1 || preINC := x }
macro STORE(loc, val) { loc := val }
macro READ(ind) { rInd := ind }
macro SWAP(loc, val) { loc := val || rVal := loc }

\*
\* Enq(item)
\*
process (producer \in Producers) 
variables
    item \in Val,
    p \in Val, \* prophecy variable
    i, preINC; {
E1:  INC(rep.back);
     i := preINC;
     ps := <<p>> \o ps;
E2:  STORE(rep.items[i], item);
}

\*
\* Deq() -> rVal
\*
process (consumer \in Consumers) 
variables i, x, range, rInd, rVal {
D1: while(TRUE) {
D2:   READ(rep.back);
D3:   range := rInd-1;
D4:   i := 1;
D5:   while(i<=range) {
D6:     SWAP(rep.items[i], null);
D7:     x := rVal;
        if(x /= null) {
D8:       await Head(ps) = x;
          ps := Tail(ps);
          rVal := x;
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
VARIABLES pc, rep, ps, item, p, i_, preINC, i, x, range, rInd, rVal

vars == << pc, rep, ps, item, p, i_, preINC, i, x, range, rInd, rVal >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ rep = [back|->1, items|->[n \in 1..Nmax|->null]]
        /\ ps = <<>>
        (* Process producer *)
        /\ item \in [Producers -> Val]
        /\ p \in [Producers -> Val]
        /\ i_ = [self \in Producers |-> defaultInitValue]
        /\ preINC = [self \in Producers |-> defaultInitValue]
        (* Process consumer *)
        /\ i = [self \in Consumers |-> defaultInitValue]
        /\ x = [self \in Consumers |-> defaultInitValue]
        /\ range = [self \in Consumers |-> defaultInitValue]
        /\ rInd = [self \in Consumers |-> defaultInitValue]
        /\ rVal = [self \in Consumers |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "E1"
                                        [] self \in Consumers -> "D1"]

E1(self) == /\ pc[self] = "E1"
            /\ /\ preINC' = [preINC EXCEPT ![self] = rep.back]
               /\ rep' = [rep EXCEPT !.back = (rep.back)+1]
            /\ i_' = [i_ EXCEPT ![self] = preINC'[self]]
            /\ ps' = <<p[self]>> \o ps
            /\ pc' = [pc EXCEPT ![self] = "E2"]
            /\ UNCHANGED << item, p, i, x, range, rInd, rVal >>

E2(self) == /\ pc[self] = "E2"
            /\ rep' = [rep EXCEPT !.items[i_[self]] = item[self]]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << ps, item, p, i_, preINC, i, x, range, rInd, rVal >>

producer(self) == E1(self) \/ E2(self)

D1(self) == /\ pc[self] = "D1"
            /\ pc' = [pc EXCEPT ![self] = "D2"]
            /\ UNCHANGED << rep, ps, item, p, i_, preINC, i, x, range, rInd, 
                            rVal >>

D2(self) == /\ pc[self] = "D2"
            /\ rInd' = [rInd EXCEPT ![self] = rep.back]
            /\ pc' = [pc EXCEPT ![self] = "D3"]
            /\ UNCHANGED << rep, ps, item, p, i_, preINC, i, x, range, rVal >>

D3(self) == /\ pc[self] = "D3"
            /\ range' = [range EXCEPT ![self] = rInd[self]-1]
            /\ pc' = [pc EXCEPT ![self] = "D4"]
            /\ UNCHANGED << rep, ps, item, p, i_, preINC, i, x, rInd, rVal >>

D4(self) == /\ pc[self] = "D4"
            /\ i' = [i EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "D5"]
            /\ UNCHANGED << rep, ps, item, p, i_, preINC, x, range, rInd, rVal >>

D5(self) == /\ pc[self] = "D5"
            /\ IF i[self]<=range[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "D6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << rep, ps, item, p, i_, preINC, i, x, range, rInd, 
                            rVal >>

D6(self) == /\ pc[self] = "D6"
            /\ /\ rVal' = [rVal EXCEPT ![self] = rep.items[i[self]]]
               /\ rep' = [rep EXCEPT !.items[i[self]] = null]
            /\ pc' = [pc EXCEPT ![self] = "D7"]
            /\ UNCHANGED << ps, item, p, i_, preINC, i, x, range, rInd >>

D7(self) == /\ pc[self] = "D7"
            /\ x' = [x EXCEPT ![self] = rVal[self]]
            /\ IF x'[self] /= null
                  THEN /\ pc' = [pc EXCEPT ![self] = "D8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D10"]
            /\ UNCHANGED << rep, ps, item, p, i_, preINC, i, range, rInd, rVal >>

D8(self) == /\ pc[self] = "D8"
            /\ Head(ps) = x[self]
            /\ rVal' = [rVal EXCEPT ![self] = x[self]]
            /\ ps' = Tail(ps)
            /\ pc' = [pc EXCEPT ![self] = "D9"]
            /\ UNCHANGED << rep, item, p, i_, preINC, i, x, range, rInd >>

D9(self) == /\ pc[self] = "D9"
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << rep, ps, item, p, i_, preINC, i, x, range, rInd, 
                            rVal >>

D10(self) == /\ pc[self] = "D10"
             /\ i' = [i EXCEPT ![self] = i[self]+1]
             /\ pc' = [pc EXCEPT ![self] = "D5"]
             /\ UNCHANGED << rep, ps, item, p, i_, preINC, x, range, rInd, 
                             rVal >>

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
rBar == [c \in Consumers |-> IF pc[c] \in {"D9", "Done"} THEN rVal[c] ELSE null]

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
    preINC |-> preINC,
    rVal |-> rVal,
    i |-> i,
    p |-> p,
    x |-> x,
    pc |-> pc,
    rep |-> rep,
    rInd |-> rInd,
    range |-> range,
    i_ |-> i_
]

=============================================================================
\* Modification History
\* Last modified Thu Nov 08 17:28:50 PST 2018 by lhochstein
\* Created Wed Oct 24 18:53:25 PDT 2018 by lhochstein
