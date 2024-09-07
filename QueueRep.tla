------------------------------ MODULE QueueRep ------------------------------
(***************************************************************************)
(*                                                                         *)
(* Queue representation type (REP) from Herlihy & Wing 1990                *)
(*                                                                         *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS Values, Producers, Consumers, Nmax

null == CHOOSE x : x \notin Values

(*--algorithm Rep
variables
    (*********************************************)
    (* Public variables                          *)
    (*********************************************)
    op = [t \in ProcSet |-> ""];
    arg = [t \in ProcSet |-> null];
    rval = [t \in ProcSet |-> null];
    done = [t \in ProcSet |-> TRUE];

    (*********************************************)
    (* Internal variables                        *)
    (*********************************************)
    q = [back|->1, items|->[n \in 1..Nmax|->null]];

(***********************************)
(* Enq(x: Values)                  *)
(***********************************)
procedure Enq(x)
variable i;
begin
E1: x := x+1 || i := x; (* Allocate a new slot *)
E2: q.items[i] := x;    (* Fill it *)
E3: return;
end procedure;

(***********************************)
(* Deq() -> rval[self] : Values    *)
(***********************************)
procedure Deq()
variables j, y, range;
begin
D1: while(TRUE) do
D2:   range := q.back-1;
D3:   j := 1;
D4:   while(j<=range) do
D5:   q.items[j] := null || y := q.items[j];
D6:   if(y /= null) then
D7:       rval[self] := y;
D8:       return;
        end if;
D9:     j:= j+1;
      end while;
    end while;
end procedure;


process prod \in Producers
begin
enq:
    with itm \in Values do
        op[self] := "enq";
        arg[self] := itm;
        rval[self] := null;
        done[self] := FALSE;
        call Enq(itm);
    end with;
enqdone:
    done[self] := TRUE;
end process;

process con \in Consumers
begin
deq:
    op[self] := "deq";
    arg[self] := null;
    rval[self] := null;
    done[self] := FALSE;

    call Deq();
deqdone:
    done[self] := TRUE;

end process;

end algorithm;*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES pc, op, arg, rval, done, q, stack, x, i, j, y, range

vars == << pc, op, arg, rval, done, q, stack, x, i, j, y, range >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ op = [t \in ProcSet |-> ""]
        /\ arg = [t \in ProcSet |-> null]
        /\ rval = [t \in ProcSet |-> null]
        /\ done = [t \in ProcSet |-> TRUE]
        /\ q = [back|->1, items|->[n \in 1..Nmax|->null]]
        (* Procedure Enq *)
        /\ x = [ self \in ProcSet |-> defaultInitValue]
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Deq *)
        /\ j = [ self \in ProcSet |-> defaultInitValue]
        /\ y = [ self \in ProcSet |-> defaultInitValue]
        /\ range = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "enq"
                                        [] self \in Consumers -> "deq"]

E1(self) == /\ pc[self] = "E1"
            /\ /\ i' = [i EXCEPT ![self] = x[self]]
               /\ x' = [x EXCEPT ![self] = x[self]+1]
            /\ pc' = [pc EXCEPT ![self] = "E2"]
            /\ UNCHANGED << op, arg, rval, done, q, stack, j, y, range >>

E2(self) == /\ pc[self] = "E2"
            /\ q' = [q EXCEPT !.items[i[self]] = x[self]]
            /\ pc' = [pc EXCEPT ![self] = "E3"]
            /\ UNCHANGED << op, arg, rval, done, stack, x, i, j, y, range >>

E3(self) == /\ pc[self] = "E3"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
            /\ x' = [x EXCEPT ![self] = Head(stack[self]).x]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << op, arg, rval, done, q, j, y, range >>

Enq(self) == E1(self) \/ E2(self) \/ E3(self)

D1(self) == /\ pc[self] = "D1"
            /\ pc' = [pc EXCEPT ![self] = "D2"]
            /\ UNCHANGED << op, arg, rval, done, q, stack, x, i, j, y, range >>

D2(self) == /\ pc[self] = "D2"
            /\ range' = [range EXCEPT ![self] = q.back-1]
            /\ pc' = [pc EXCEPT ![self] = "D3"]
            /\ UNCHANGED << op, arg, rval, done, q, stack, x, i, j, y >>

D3(self) == /\ pc[self] = "D3"
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "D4"]
            /\ UNCHANGED << op, arg, rval, done, q, stack, x, i, y, range >>

D4(self) == /\ pc[self] = "D4"
            /\ IF (j[self]<=range[self])
                  THEN /\ pc' = [pc EXCEPT ![self] = "D5"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << op, arg, rval, done, q, stack, x, i, j, y, range >>

D5(self) == /\ pc[self] = "D5"
            /\ /\ q' = [q EXCEPT !.items[j[self]] = null]
               /\ y' = [y EXCEPT ![self] = q.items[j[self]]]
            /\ pc' = [pc EXCEPT ![self] = "D6"]
            /\ UNCHANGED << op, arg, rval, done, stack, x, i, j, range >>

D6(self) == /\ pc[self] = "D6"
            /\ IF (y[self] /= null)
                  THEN /\ pc' = [pc EXCEPT ![self] = "D7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D9"]
            /\ UNCHANGED << op, arg, rval, done, q, stack, x, i, j, y, range >>

D7(self) == /\ pc[self] = "D7"
            /\ rval' = [rval EXCEPT ![self] = y[self]]
            /\ pc' = [pc EXCEPT ![self] = "D8"]
            /\ UNCHANGED << op, arg, done, q, stack, x, i, j, y, range >>

D8(self) == /\ pc[self] = "D8"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ j' = [j EXCEPT ![self] = Head(stack[self]).j]
            /\ y' = [y EXCEPT ![self] = Head(stack[self]).y]
            /\ range' = [range EXCEPT ![self] = Head(stack[self]).range]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << op, arg, rval, done, q, x, i >>

D9(self) == /\ pc[self] = "D9"
            /\ j' = [j EXCEPT ![self] = j[self]+1]
            /\ pc' = [pc EXCEPT ![self] = "D4"]
            /\ UNCHANGED << op, arg, rval, done, q, stack, x, i, y, range >>

Deq(self) == D1(self) \/ D2(self) \/ D3(self) \/ D4(self) \/ D5(self)
                \/ D6(self) \/ D7(self) \/ D8(self) \/ D9(self)

enq(self) == /\ pc[self] = "enq"
             /\ \E itm \in Values:
                  /\ op' = [op EXCEPT ![self] = "enq"]
                  /\ arg' = [arg EXCEPT ![self] = itm]
                  /\ rval' = [rval EXCEPT ![self] = null]
                  /\ done' = [done EXCEPT ![self] = FALSE]
                  /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enq",
                                                              pc        |->  "enqdone",
                                                              i         |->  i[self],
                                                              x         |->  x[self] ] >>
                                                          \o stack[self]]
                     /\ x' = [x EXCEPT ![self] = itm]
                  /\ i' = [i EXCEPT ![self] = defaultInitValue]
                  /\ pc' = [pc EXCEPT ![self] = "E1"]
             /\ UNCHANGED << q, j, y, range >>

enqdone(self) == /\ pc[self] = "enqdone"
                 /\ done' = [done EXCEPT ![self] = TRUE]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << op, arg, rval, q, stack, x, i, j, y, range >>

prod(self) == enq(self) \/ enqdone(self)

deq(self) == /\ pc[self] = "deq"
             /\ op' = [op EXCEPT ![self] = "deq"]
             /\ arg' = [arg EXCEPT ![self] = null]
             /\ rval' = [rval EXCEPT ![self] = null]
             /\ done' = [done EXCEPT ![self] = FALSE]
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Deq",
                                                      pc        |->  "deqdone",
                                                      j         |->  j[self],
                                                      y         |->  y[self],
                                                      range     |->  range[self] ] >>
                                                  \o stack[self]]
             /\ j' = [j EXCEPT ![self] = defaultInitValue]
             /\ y' = [y EXCEPT ![self] = defaultInitValue]
             /\ range' = [range EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "D1"]
             /\ UNCHANGED << q, x, i >>

deqdone(self) == /\ pc[self] = "deqdone"
                 /\ done' = [done EXCEPT ![self] = TRUE]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << op, arg, rval, q, stack, x, i, j, y, range >>

con(self) == deq(self) \/ deqdone(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: Enq(self) \/ Deq(self))
           \/ (\E self \in Producers: prod(self))
           \/ (\E self \in Consumers: con(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Thu Nov 08 17:28:50 PST 2018 by lhochstein
\* Created Wed Oct 24 18:53:25 PDT 2018 by lhochstein
