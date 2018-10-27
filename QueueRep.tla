(****************************************************************************

Queue representation type (REP) from Herlihy & Wing 1990

****************************************************************************)
------------------------------ MODULE QueueRep ------------------------------
EXTENDS Naturals, Sequences

CONSTANT Values

CONSTANT null
CONSTANT producers
CONSTANT consumers


TypeOk(r) == r \in [back:Nat, items:Seq(Values \union null)]

(*
--algorithm Rep

variables rep = [back|->1, items|->[n \in Nat|->null]],
          rVal = [p \in producers \union consumers|->null];

macro INC(x)
begin
    x := x+1 || rVal[self] := x;
end macro

macro STORE(loc, val)
begin
    loc := val
end macro


macro READ(val)
begin
    rVal[self] := val;
end macro

macro SWAP(loc, val)
begin
    loc := val || rVal[self] := loc
end macro

procedure Enq(q, x)
variable j;
begin
E1: INC(q.back);
E2: j := rVal[self];
E3: STORE(q.items[j], x);
E4: return;
end procedure

procedure Deq(q)
variables i, range;
begin
D1: while(TRUE) do
    D2: READ(q.back);
    D3: range := rVal[self]-1;
    D4: i := 1;
    D5: while(i<=range) do
        D6: SWAP(q.items[i], null);
        D7: x := rVal[self];
            if x = null then
                D8: rVal[self] := x;
                    return;
            end if;
        D9: i:= i+1;
    end while
end while
end procedure


process p \in producers
begin
P1: with item \in Values do
    call Enq(rep, item);
end with;
end process

process c \in consumers
begin
C1: call Deq(rep);
end process


end algorithm
*)
\* BEGIN TRANSLATION
\* Parameter q of procedure Enq at line 45 col 15 changed to q_
CONSTANT defaultInitValue
VARIABLES rep, rVal, pc, stack, q_, x, j, q, i, range

vars == << rep, rVal, pc, stack, q_, x, j, q, i, range >>

ProcSet == (producers) \cup (consumers)

Init == (* Global variables *)
        /\ rep = [back|->1, items|->[n \in Nat|->null]]
        /\ rVal = [p \in producers \union consumers|->null]
        (* Procedure Enq *)
        /\ q_ = [ self \in ProcSet |-> defaultInitValue]
        /\ x = [ self \in ProcSet |-> defaultInitValue]
        /\ j = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Deq *)
        /\ q = [ self \in ProcSet |-> defaultInitValue]
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        /\ range = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in producers -> "P1"
                                        [] self \in consumers -> "C1"]

E1(self) == /\ pc[self] = "E1"
            /\ /\ q_' = [q_ EXCEPT ![self].back = (q_[self].back)+1]
               /\ rVal' = [rVal EXCEPT ![self] = q_[self].back]
            /\ pc' = [pc EXCEPT ![self] = "E2"]
            /\ UNCHANGED << rep, stack, x, j, q, i, range >>

E2(self) == /\ pc[self] = "E2"
            /\ j' = [j EXCEPT ![self] = rVal[self]]
            /\ pc' = [pc EXCEPT ![self] = "E3"]
            /\ UNCHANGED << rep, rVal, stack, q_, x, q, i, range >>

E3(self) == /\ pc[self] = "E3"
            /\ q_' = [q_ EXCEPT ![self].items[j[self]] = x[self]]
            /\ pc' = [pc EXCEPT ![self] = "E4"]
            /\ UNCHANGED << rep, rVal, stack, x, j, q, i, range >>

E4(self) == /\ pc[self] = "E4"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ j' = [j EXCEPT ![self] = Head(stack[self]).j]
            /\ q_' = [q_ EXCEPT ![self] = Head(stack[self]).q_]
            /\ x' = [x EXCEPT ![self] = Head(stack[self]).x]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << rep, rVal, q, i, range >>

Enq(self) == E1(self) \/ E2(self) \/ E3(self) \/ E4(self)

D1(self) == /\ pc[self] = "D1"
            /\ pc' = [pc EXCEPT ![self] = "D2"]
            /\ UNCHANGED << rep, rVal, stack, q_, x, j, q, i, range >>

D2(self) == /\ pc[self] = "D2"
            /\ rVal' = [rVal EXCEPT ![self] = q[self].back]
            /\ pc' = [pc EXCEPT ![self] = "D3"]
            /\ UNCHANGED << rep, stack, q_, x, j, q, i, range >>

D3(self) == /\ pc[self] = "D3"
            /\ range' = [range EXCEPT ![self] = rVal[self]-1]
            /\ pc' = [pc EXCEPT ![self] = "D4"]
            /\ UNCHANGED << rep, rVal, stack, q_, x, j, q, i >>

D4(self) == /\ pc[self] = "D4"
            /\ i' = [i EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "D5"]
            /\ UNCHANGED << rep, rVal, stack, q_, x, j, q, range >>

D5(self) == /\ pc[self] = "D5"
            /\ IF (i[self]<=range[self])
                  THEN /\ pc' = [pc EXCEPT ![self] = "D6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << rep, rVal, stack, q_, x, j, q, i, range >>

D6(self) == /\ pc[self] = "D6"
            /\ /\ q' = [q EXCEPT ![self].items[i[self]] = null]
               /\ rVal' = [rVal EXCEPT ![self] = q[self].items[i[self]]]
            /\ pc' = [pc EXCEPT ![self] = "D7"]
            /\ UNCHANGED << rep, stack, q_, x, j, i, range >>

D7(self) == /\ pc[self] = "D7"
            /\ x' = [x EXCEPT ![self] = rVal[self]]
            /\ IF x'[self] = null
                  THEN /\ pc' = [pc EXCEPT ![self] = "D8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D9"]
            /\ UNCHANGED << rep, rVal, stack, q_, j, q, i, range >>

D8(self) == /\ pc[self] = "D8"
            /\ rVal' = [rVal EXCEPT ![self] = x[self]]
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
            /\ range' = [range EXCEPT ![self] = Head(stack[self]).range]
            /\ q' = [q EXCEPT ![self] = Head(stack[self]).q]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << rep, q_, x, j >>

D9(self) == /\ pc[self] = "D9"
            /\ i' = [i EXCEPT ![self] = i[self]+1]
            /\ pc' = [pc EXCEPT ![self] = "D5"]
            /\ UNCHANGED << rep, rVal, stack, q_, x, j, q, range >>

Deq(self) == D1(self) \/ D2(self) \/ D3(self) \/ D4(self) \/ D5(self)
                \/ D6(self) \/ D7(self) \/ D8(self) \/ D9(self)

P1(self) == /\ pc[self] = "P1"
            /\ \E item \in Values:
                 /\ /\ q_' = [q_ EXCEPT ![self] = rep]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enq",
                                                             pc        |->  "Done",
                                                             j         |->  j[self],
                                                             q_        |->  q_[self],
                                                             x         |->  x[self] ] >>
                                                         \o stack[self]]
                    /\ x' = [x EXCEPT ![self] = item]
                 /\ j' = [j EXCEPT ![self] = defaultInitValue]
                 /\ pc' = [pc EXCEPT ![self] = "E1"]
            /\ UNCHANGED << rep, rVal, q, i, range >>

p(self) == P1(self)

C1(self) == /\ pc[self] = "C1"
            /\ /\ q' = [q EXCEPT ![self] = rep]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Deq",
                                                        pc        |->  "Done",
                                                        i         |->  i[self],
                                                        range     |->  range[self],
                                                        q         |->  q[self] ] >>
                                                    \o stack[self]]
            /\ i' = [i EXCEPT ![self] = defaultInitValue]
            /\ range' = [range EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << rep, rVal, q_, x, j >>

c(self) == C1(self)

Next == (\E self \in ProcSet: Enq(self) \/ Deq(self))
           \/ (\E self \in producers: p(self))
           \/ (\E self \in consumers: c(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Sat Oct 27 12:07:19 PDT 2018 by lhochstein
\* Created Wed Oct 24 18:53:25 PDT 2018 by lhochstein
