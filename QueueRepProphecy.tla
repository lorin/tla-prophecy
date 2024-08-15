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
          p = <<>>;

macro INC(x) { x := x+1 || preINC := x }
macro STORE(loc, val) { loc := val }
macro READ(ind) { rInd := ind }
macro SWAP(loc, val) { loc := val || rVal := loc }

procedure Enq(v, pp)
variables i, preINC {
E1:  INC(rep.back);
     i := preINC;
     p := <<pp>> \o p;
E2:  STORE(rep.items[i], v);
E3:  return
}


process (producer \in Producers) 
variable p1 \in Val; {
P1: with (item \in Val) {
    call Enq(item, p1)
    }
}

\*
\* Deq
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
D8:       await Head(p) = x;
          rVal := x;
          p := Tail(p);
D9:       goto "Done"
        };
D10:    i:= i+1
      }
    }
}

}
*)
\* BEGIN TRANSLATION
\* Process variable i of process consumer at line 45 col 11 changed to i_
CONSTANT defaultInitValue
VARIABLES pc, rep, p, stack, v, pp, i, preINC, p1, i_, x, range, rInd, rVal

vars == << pc, rep, p, stack, v, pp, i, preINC, p1, i_, x, range, rInd, rVal
        >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ rep = [back|->1, items|->[n \in 1..Nmax|->null]]
        /\ p = <<>>
        (* Procedure Enq *)
        /\ v = [ self \in ProcSet |-> defaultInitValue]
        /\ pp = [ self \in ProcSet |-> defaultInitValue]
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        /\ preINC = [ self \in ProcSet |-> defaultInitValue]
        (* Process producer *)
        /\ p1 \in [Producers -> Val]
        (* Process consumer *)
        /\ i_ = [self \in Consumers |-> defaultInitValue]
        /\ x = [self \in Consumers |-> defaultInitValue]
        /\ range = [self \in Consumers |-> defaultInitValue]
        /\ rInd = [self \in Consumers |-> defaultInitValue]
        /\ rVal = [self \in Consumers |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "P1"
                                        [] self \in Consumers -> "D1"]

E1(self) == /\ pc[self] = "E1"
            /\ /\ preINC' = [preINC EXCEPT ![self] = rep.back]
               /\ rep' = [rep EXCEPT !.back = (rep.back)+1]
            /\ i' = [i EXCEPT ![self] = preINC'[self]]
            /\ p' = <<pp[self]>> \o p
            /\ pc' = [pc EXCEPT ![self] = "E2"]
            /\ UNCHANGED << stack, v, pp, p1, i_, x, range, rInd, rVal >>

E2(self) == /\ pc[self] = "E2"
            /\ rep' = [rep EXCEPT !.items[i[self]] = v[self]]
            /\ pc' = [pc EXCEPT ![self] = "E3"]
            /\ UNCHANGED << p, stack, v, pp, i, preINC, p1, i_, x, range, rInd, 
                            rVal >>

E3(self) == /\ pc[self] = "E3"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
            /\ preINC' = [preINC EXCEPT ![self] = Head(stack[self]).preINC]
            /\ v' = [v EXCEPT ![self] = Head(stack[self]).v]
            /\ pp' = [pp EXCEPT ![self] = Head(stack[self]).pp]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << rep, p, p1, i_, x, range, rInd, rVal >>

Enq(self) == E1(self) \/ E2(self) \/ E3(self)

P1(self) == /\ pc[self] = "P1"
            /\ \E item \in Val:
                 /\ /\ pp' = [pp EXCEPT ![self] = p1[self]]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enq",
                                                             pc        |->  "Done",
                                                             i         |->  i[self],
                                                             preINC    |->  preINC[self],
                                                             v         |->  v[self],
                                                             pp        |->  pp[self] ] >>
                                                         \o stack[self]]
                    /\ v' = [v EXCEPT ![self] = item]
                 /\ i' = [i EXCEPT ![self] = defaultInitValue]
                 /\ preINC' = [preINC EXCEPT ![self] = defaultInitValue]
                 /\ pc' = [pc EXCEPT ![self] = "E1"]
            /\ UNCHANGED << rep, p, p1, i_, x, range, rInd, rVal >>

producer(self) == P1(self)

D1(self) == /\ pc[self] = "D1"
            /\ pc' = [pc EXCEPT ![self] = "D2"]
            /\ UNCHANGED << rep, p, stack, v, pp, i, preINC, p1, i_, x, range, 
                            rInd, rVal >>

D2(self) == /\ pc[self] = "D2"
            /\ rInd' = [rInd EXCEPT ![self] = rep.back]
            /\ pc' = [pc EXCEPT ![self] = "D3"]
            /\ UNCHANGED << rep, p, stack, v, pp, i, preINC, p1, i_, x, range, 
                            rVal >>

D3(self) == /\ pc[self] = "D3"
            /\ range' = [range EXCEPT ![self] = rInd[self]-1]
            /\ pc' = [pc EXCEPT ![self] = "D4"]
            /\ UNCHANGED << rep, p, stack, v, pp, i, preINC, p1, i_, x, rInd, 
                            rVal >>

D4(self) == /\ pc[self] = "D4"
            /\ i_' = [i_ EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "D5"]
            /\ UNCHANGED << rep, p, stack, v, pp, i, preINC, p1, x, range, 
                            rInd, rVal >>

D5(self) == /\ pc[self] = "D5"
            /\ IF i_[self]<=range[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "D6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << rep, p, stack, v, pp, i, preINC, p1, i_, x, range, 
                            rInd, rVal >>

D6(self) == /\ pc[self] = "D6"
            /\ /\ rVal' = [rVal EXCEPT ![self] = rep.items[i_[self]]]
               /\ rep' = [rep EXCEPT !.items[i_[self]] = null]
            /\ pc' = [pc EXCEPT ![self] = "D7"]
            /\ UNCHANGED << p, stack, v, pp, i, preINC, p1, i_, x, range, rInd >>

D7(self) == /\ pc[self] = "D7"
            /\ x' = [x EXCEPT ![self] = rVal[self]]
            /\ IF x'[self] /= null
                  THEN /\ pc' = [pc EXCEPT ![self] = "D8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D10"]
            /\ UNCHANGED << rep, p, stack, v, pp, i, preINC, p1, i_, range, 
                            rInd, rVal >>

D8(self) == /\ pc[self] = "D8"
            /\ Head(p) = x[self]
            /\ rVal' = [rVal EXCEPT ![self] = x[self]]
            /\ p' = Tail(p)
            /\ pc' = [pc EXCEPT ![self] = "D9"]
            /\ UNCHANGED << rep, stack, v, pp, i, preINC, p1, i_, x, range, 
                            rInd >>

D9(self) == /\ pc[self] = "D9"
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << rep, p, stack, v, pp, i, preINC, p1, i_, x, range, 
                            rInd, rVal >>

D10(self) == /\ pc[self] = "D10"
             /\ i_' = [i_ EXCEPT ![self] = i_[self]+1]
             /\ pc' = [pc EXCEPT ![self] = "D5"]
             /\ UNCHANGED << rep, p, stack, v, pp, i, preINC, p1, x, range, 
                             rInd, rVal >>

consumer(self) == D1(self) \/ D2(self) \/ D3(self) \/ D4(self) \/ D5(self)
                     \/ D6(self) \/ D7(self) \/ D8(self) \/ D9(self)
                     \/ D10(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: Enq(self))
           \/ (\E self \in Producers: producer(self))
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
itemsBar == p
xBar == p1
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
    v |-> v,
    x |-> x,
    pc |-> pc,
    rep |-> rep,
    rInd |-> rInd,
    ragne |-> range,
    i_ |-> i_,
    stack |-> stack
]

=============================================================================
\* Modification History
\* Last modified Thu Nov 08 17:28:50 PST 2018 by lhochstein
\* Created Wed Oct 24 18:53:25 PDT 2018 by lhochstein
