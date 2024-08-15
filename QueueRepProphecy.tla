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

procedure Deq()
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
D9:       return
        };
D10:    i:= i+1
      }
    }
}

process (producer \in Producers) 
variable p1 \in Val; {
P1: with (item \in Val) {
    call Enq(item, p1)
    }
}

process (consumer \in Consumers) {
C1: call Deq()
}

}
*)
\* BEGIN TRANSLATION
\* Procedure variable i of procedure Enq at line 25 col 11 changed to i_
CONSTANT defaultInitValue
VARIABLES pc, rep, p, stack, v, pp, i_, preINC, i, x, range, rInd, rVal, p1

vars == << pc, rep, p, stack, v, pp, i_, preINC, i, x, range, rInd, rVal, p1
        >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ rep = [back|->1, items|->[n \in 1..Nmax|->null]]
        /\ p = <<>>
        (* Procedure Enq *)
        /\ v = [ self \in ProcSet |-> defaultInitValue]
        /\ pp = [ self \in ProcSet |-> defaultInitValue]
        /\ i_ = [ self \in ProcSet |-> defaultInitValue]
        /\ preINC = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Deq *)
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        /\ x = [ self \in ProcSet |-> defaultInitValue]
        /\ range = [ self \in ProcSet |-> defaultInitValue]
        /\ rInd = [ self \in ProcSet |-> defaultInitValue]
        /\ rVal = [ self \in ProcSet |-> defaultInitValue]
        (* Process producer *)
        /\ p1 \in [Producers -> Val]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "P1"
                                        [] self \in Consumers -> "C1"]

E1(self) == /\ pc[self] = "E1"
            /\ /\ preINC' = [preINC EXCEPT ![self] = rep.back]
               /\ rep' = [rep EXCEPT !.back = (rep.back)+1]
            /\ i_' = [i_ EXCEPT ![self] = preINC'[self]]
            /\ p' = <<pp[self]>> \o p
            /\ pc' = [pc EXCEPT ![self] = "E2"]
            /\ UNCHANGED << stack, v, pp, i, x, range, rInd, rVal, p1 >>

E2(self) == /\ pc[self] = "E2"
            /\ rep' = [rep EXCEPT !.items[i_[self]] = v[self]]
            /\ pc' = [pc EXCEPT ![self] = "E3"]
            /\ UNCHANGED << p, stack, v, pp, i_, preINC, i, x, range, rInd, 
                            rVal, p1 >>

E3(self) == /\ pc[self] = "E3"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ i_' = [i_ EXCEPT ![self] = Head(stack[self]).i_]
            /\ preINC' = [preINC EXCEPT ![self] = Head(stack[self]).preINC]
            /\ v' = [v EXCEPT ![self] = Head(stack[self]).v]
            /\ pp' = [pp EXCEPT ![self] = Head(stack[self]).pp]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << rep, p, i, x, range, rInd, rVal, p1 >>

Enq(self) == E1(self) \/ E2(self) \/ E3(self)

D1(self) == /\ pc[self] = "D1"
            /\ pc' = [pc EXCEPT ![self] = "D2"]
            /\ UNCHANGED << rep, p, stack, v, pp, i_, preINC, i, x, range, 
                            rInd, rVal, p1 >>

D2(self) == /\ pc[self] = "D2"
            /\ rInd' = [rInd EXCEPT ![self] = rep.back]
            /\ pc' = [pc EXCEPT ![self] = "D3"]
            /\ UNCHANGED << rep, p, stack, v, pp, i_, preINC, i, x, range, 
                            rVal, p1 >>

D3(self) == /\ pc[self] = "D3"
            /\ range' = [range EXCEPT ![self] = rInd[self]-1]
            /\ pc' = [pc EXCEPT ![self] = "D4"]
            /\ UNCHANGED << rep, p, stack, v, pp, i_, preINC, i, x, rInd, rVal, 
                            p1 >>

D4(self) == /\ pc[self] = "D4"
            /\ i' = [i EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "D5"]
            /\ UNCHANGED << rep, p, stack, v, pp, i_, preINC, x, range, rInd, 
                            rVal, p1 >>

D5(self) == /\ pc[self] = "D5"
            /\ IF i[self]<=range[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "D6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << rep, p, stack, v, pp, i_, preINC, i, x, range, 
                            rInd, rVal, p1 >>

D6(self) == /\ pc[self] = "D6"
            /\ /\ rVal' = [rVal EXCEPT ![self] = rep.items[i[self]]]
               /\ rep' = [rep EXCEPT !.items[i[self]] = null]
            /\ pc' = [pc EXCEPT ![self] = "D7"]
            /\ UNCHANGED << p, stack, v, pp, i_, preINC, i, x, range, rInd, p1 >>

D7(self) == /\ pc[self] = "D7"
            /\ x' = [x EXCEPT ![self] = rVal[self]]
            /\ IF x'[self] /= null
                  THEN /\ pc' = [pc EXCEPT ![self] = "D8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D10"]
            /\ UNCHANGED << rep, p, stack, v, pp, i_, preINC, i, range, rInd, 
                            rVal, p1 >>

D8(self) == /\ pc[self] = "D8"
            /\ Head(p) = x[self]
            /\ rVal' = [rVal EXCEPT ![self] = x[self]]
            /\ p' = Tail(p)
            /\ pc' = [pc EXCEPT ![self] = "D9"]
            /\ UNCHANGED << rep, stack, v, pp, i_, preINC, i, x, range, rInd, 
                            p1 >>

D9(self) == /\ pc[self] = "D9"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
            /\ x' = [x EXCEPT ![self] = Head(stack[self]).x]
            /\ range' = [range EXCEPT ![self] = Head(stack[self]).range]
            /\ rInd' = [rInd EXCEPT ![self] = Head(stack[self]).rInd]
            /\ rVal' = [rVal EXCEPT ![self] = Head(stack[self]).rVal]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << rep, p, v, pp, i_, preINC, p1 >>

D10(self) == /\ pc[self] = "D10"
             /\ i' = [i EXCEPT ![self] = i[self]+1]
             /\ pc' = [pc EXCEPT ![self] = "D5"]
             /\ UNCHANGED << rep, p, stack, v, pp, i_, preINC, x, range, rInd, 
                             rVal, p1 >>

Deq(self) == D1(self) \/ D2(self) \/ D3(self) \/ D4(self) \/ D5(self)
                \/ D6(self) \/ D7(self) \/ D8(self) \/ D9(self)
                \/ D10(self)

P1(self) == /\ pc[self] = "P1"
            /\ \E item \in Val:
                 /\ /\ pp' = [pp EXCEPT ![self] = p1[self]]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enq",
                                                             pc        |->  "Done",
                                                             i_        |->  i_[self],
                                                             preINC    |->  preINC[self],
                                                             v         |->  v[self],
                                                             pp        |->  pp[self] ] >>
                                                         \o stack[self]]
                    /\ v' = [v EXCEPT ![self] = item]
                 /\ i_' = [i_ EXCEPT ![self] = defaultInitValue]
                 /\ preINC' = [preINC EXCEPT ![self] = defaultInitValue]
                 /\ pc' = [pc EXCEPT ![self] = "E1"]
            /\ UNCHANGED << rep, p, i, x, range, rInd, rVal, p1 >>

producer(self) == P1(self)

C1(self) == /\ pc[self] = "C1"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Deq",
                                                     pc        |->  "Done",
                                                     i         |->  i[self],
                                                     x         |->  x[self],
                                                     range     |->  range[self],
                                                     rInd      |->  rInd[self],
                                                     rVal      |->  rVal[self] ] >>
                                                 \o stack[self]]
            /\ i' = [i EXCEPT ![self] = defaultInitValue]
            /\ x' = [x EXCEPT ![self] = defaultInitValue]
            /\ range' = [range EXCEPT ![self] = defaultInitValue]
            /\ rInd' = [rInd EXCEPT ![self] = defaultInitValue]
            /\ rVal' = [rVal EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << rep, p, v, pp, i_, preINC, p1 >>

consumer(self) == C1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: Enq(self) \/ Deq(self))
           \/ (\E self \in Producers: producer(self))
           \/ (\E self \in Consumers: consumer(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

NotDone == ~(\A self \in ProcSet: pc[self] = "Done")

pcBar == [c \in Producers \union Consumers |->
    CASE pc[c] \in {"P1", "E1"} -> "E"
      [] pc[c] \in {"C1", "D1", "D2", "D3", "D4", "D5", "D6", "D7", "D8", "D9", "D10"} -> "D"
      [] pc[c] \in {"E2", "E3", "Done"} -> "Done"
]
itemsBar == p
xBar == p1
rBar == [c \in Consumers |-> IF rVal[c]=defaultInitValue THEN null ELSE rVal[c]]

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
