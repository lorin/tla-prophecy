------------------------------ MODULE QueueRepIds ----------------------------
(***************************************************************************)
(*                                                                         *)
(* Queue representation type (REP) from Herlihy & Wing 1990.               *)
(* Includes Ids to support refinemnet mapping.                             *)
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
   
    (***
     * We need to assign a unique id to each element to
     * support the refinement mapping.
     *)

    ids = <<>>; \* function that maps index to id
    nextId = 0;
    
define
    Add(f, k, v) == [x \in DOMAIN f \union {k} |-> IF x=k THEN v ELSE f[x]]
    Del(f, k) == [x \in DOMAIN f \ {k} | f[k]]
end define;


(***********************************)
(* Enq(x: Values, id: Nat)         *)
(***********************************)
procedure Enq(x, id)
variable i;
begin
E1: x := x+1 || i := x; (* Allocate a new slot *)
E2: q.items[i] := x;    (* Fill it *)
    ids := Add(ids, i, id);
E3: return;
end procedure;

(***********************************)
(* Deq() -> rval[self] : Values    *)
(***********************************)
procedure Deq()
variables j, y, range, idd;
begin
D1: while(TRUE) do
D2:   range := q.back-1;
D3:   j := 1;
D4:   while(j<=range) do
D5:   q.items[j] := null || y := q.items[j];
D6:   if(y /= null) then
D7:       rval[self] := y;
          idd := ids[j];
          ids := Del(ids, j);
D8:       return;
        end if;
D9:     j:= j+1;
      end while;
    end while;
end procedure;


process prod \in Producers
variable ide;
begin
enq:
    with item \in Values do
        op[self] := "enq";
        arg[self] := itm;
        rval[self] := null;
        done[self] := FALSE;
        ide := nextId || nextId := nextId+1;
        call Enq(item, ide);
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
VARIABLES pc, op, arg, rval, done, q, ids, nextId, stack

(* define statement *)
Add(f, k, v) == [x \in DOMAIN f \union {k} |-> IF x=k THEN v ELSE f[x]]
Del(f, k) == [x \in DOMAIN f \ {k} | f[k]]

VARIABLES x, id, i, j, y, range, idd

vars == << pc, op, arg, rval, done, q, ids, nextId, stack, x, id, i, j, y, 
           range, idd >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ op = [t \in ProcSet |-> ""]
        /\ arg = [t \in ProcSet |-> null]
        /\ rval = [t \in ProcSet |-> null]
        /\ done = [t \in ProcSet |-> TRUE]
        /\ q = [back|->1, items|->[n \in 1..Nmax|->null]]
        /\ ids = <<>>
        /\ nextId = 0
        (* Procedure Enq *)
        /\ x = [ self \in ProcSet |-> defaultInitValue]
        /\ id = [ self \in ProcSet |-> defaultInitValue]
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Deq *)
        /\ j = [ self \in ProcSet |-> defaultInitValue]
        /\ y = [ self \in ProcSet |-> defaultInitValue]
        /\ range = [ self \in ProcSet |-> defaultInitValue]
        (* Process prod *)
        /\ idd = [self \in Producers |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "enq"
                                        [] self \in Consumers -> "deq"]

E1(self) == /\ pc[self] = "E1"
            /\ /\ i' = [i EXCEPT ![self] = x[self]]
               /\ x' = [x EXCEPT ![self] = x[self]+1]
            /\ pc' = [pc EXCEPT ![self] = "E2"]
            /\ UNCHANGED << op, arg, rval, done, q, ids, nextId, stack, id, j, 
                            y, range, idd >>

E2(self) == /\ pc[self] = "E2"
            /\ q' = [q EXCEPT !.items[i[self]] = x[self]]
            /\ ids' = Add(ids, i[self], id[self])
            /\ pc' = [pc EXCEPT ![self] = "E3"]
            /\ UNCHANGED << op, arg, rval, done, nextId, stack, x, id, i, j, y, 
                            range, idd >>

E3(self) == /\ pc[self] = "E3"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
            /\ x' = [x EXCEPT ![self] = Head(stack[self]).x]
            /\ id' = [id EXCEPT ![self] = Head(stack[self]).id]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << op, arg, rval, done, q, ids, nextId, j, y, range, 
                            idd >>

Enq(self) == E1(self) \/ E2(self) \/ E3(self)

D1(self) == /\ pc[self] = "D1"
            /\ pc' = [pc EXCEPT ![self] = "D2"]
            /\ UNCHANGED << op, arg, rval, done, q, ids, nextId, stack, x, id, 
                            i, j, y, range, idd >>

D2(self) == /\ pc[self] = "D2"
            /\ range' = [range EXCEPT ![self] = q.back-1]
            /\ pc' = [pc EXCEPT ![self] = "D3"]
            /\ UNCHANGED << op, arg, rval, done, q, ids, nextId, stack, x, id, 
                            i, j, y, idd >>

D3(self) == /\ pc[self] = "D3"
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "D4"]
            /\ UNCHANGED << op, arg, rval, done, q, ids, nextId, stack, x, id, 
                            i, y, range, idd >>

D4(self) == /\ pc[self] = "D4"
            /\ IF (j[self]<=range[self])
                  THEN /\ pc' = [pc EXCEPT ![self] = "D5"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << op, arg, rval, done, q, ids, nextId, stack, x, id, 
                            i, j, y, range, idd >>

D5(self) == /\ pc[self] = "D5"
            /\ /\ q' = [q EXCEPT !.items[j[self]] = null]
               /\ y' = [y EXCEPT ![self] = q.items[j[self]]]
            /\ pc' = [pc EXCEPT ![self] = "D6"]
            /\ UNCHANGED << op, arg, rval, done, ids, nextId, stack, x, id, i, 
                            j, range, idd >>

D6(self) == /\ pc[self] = "D6"
            /\ IF (y[self] /= null)
                  THEN /\ pc' = [pc EXCEPT ![self] = "D7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D9"]
            /\ UNCHANGED << op, arg, rval, done, q, ids, nextId, stack, x, id, 
                            i, j, y, range, idd >>

D7(self) == /\ pc[self] = "D7"
            /\ rval' = [rval EXCEPT ![self] = y[self]]
            /\ pc' = [pc EXCEPT ![self] = "D8"]
            /\ UNCHANGED << op, arg, done, q, ids, nextId, stack, x, id, i, j, 
                            y, range, idd >>

D8(self) == /\ pc[self] = "D8"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ j' = [j EXCEPT ![self] = Head(stack[self]).j]
            /\ y' = [y EXCEPT ![self] = Head(stack[self]).y]
            /\ range' = [range EXCEPT ![self] = Head(stack[self]).range]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << op, arg, rval, done, q, ids, nextId, x, id, i, idd >>

D9(self) == /\ pc[self] = "D9"
            /\ j' = [j EXCEPT ![self] = j[self]+1]
            /\ pc' = [pc EXCEPT ![self] = "D4"]
            /\ UNCHANGED << op, arg, rval, done, q, ids, nextId, stack, x, id, 
                            i, y, range, idd >>

Deq(self) == D1(self) \/ D2(self) \/ D3(self) \/ D4(self) \/ D5(self)
                \/ D6(self) \/ D7(self) \/ D8(self) \/ D9(self)

enq(self) == /\ pc[self] = "enq"
             /\ \E item \in Values:
                  /\ op' = [op EXCEPT ![self] = "enq"]
                  /\ arg' = [arg EXCEPT ![self] = itm]
                  /\ rval' = [rval EXCEPT ![self] = null]
                  /\ done' = [done EXCEPT ![self] = FALSE]
                  /\ /\ idd' = [idd EXCEPT ![self] = nextId]
                     /\ nextId' = nextId+1
                  /\ /\ id' = [id EXCEPT ![self] = idd'[self]]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enq",
                                                              pc        |->  "enqdone",
                                                              i         |->  i[self],
                                                              x         |->  x[self],
                                                              id        |->  id[self] ] >>
                                                          \o stack[self]]
                     /\ x' = [x EXCEPT ![self] = item]
                  /\ i' = [i EXCEPT ![self] = defaultInitValue]
                  /\ pc' = [pc EXCEPT ![self] = "E1"]
             /\ UNCHANGED << q, ids, j, y, range >>

enqdone(self) == /\ pc[self] = "enqdone"
                 /\ done' = [done EXCEPT ![self] = TRUE]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << op, arg, rval, q, ids, nextId, stack, x, id, 
                                 i, j, y, range, idd >>

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
             /\ UNCHANGED << q, ids, nextId, x, id, i, idd >>

deqdone(self) == /\ pc[self] = "deqdone"
                 /\ done' = [done EXCEPT ![self] = TRUE]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << op, arg, rval, q, ids, nextId, stack, x, id, 
                                 i, j, y, range, idd >>

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
