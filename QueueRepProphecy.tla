(***************************************************************************)
(* Queue qresentation type (REP) from Herlihy & Wing 1990.                 *)
(* Includes prophecy variables.                                            *)
(***************************************************************************)
------------------------------ MODULE QueueRepProphecy -----------------------
EXTENDS Naturals, Sequences

CONSTANTS Values, Producers, Consumers, Nmax

null == CHOOSE x : x \notin Values

Pi == Values

Threads == Producers \union Consumers

(*--algorithm Rep 
variables 
    q = [back|->1, items|->[n \in 1..Nmax|->null]];
    ps = <<>>;

    \* Public variables
    op = [t \in Threads |-> ""];
    arg = [t \in Threads |-> null];
    rval = [t \in Threads |-> null];
    done = [t \in Threads |-> TRUE];

macro INC(x) begin
     x := x+1 || INC_return := x;
end macro

macro STORE(loc, val) begin
    loc := val;
end macro

macro READ(ind) begin
     READ_return := ind;
end macro

macro SWAP(loc, val) begin
     loc := val || SWAP_return := loc;
end macro

\*
\* Enq(x: Values)
\*
procedure Enq(x)
variables 
    i; INC_return;
begin
E1: INC(q.back);
    i := INC_return;       \* Allocate a new slot
    with p \in Pi do
        ps := Append(ps, p);
    end with;
E2: STORE(q.items[i], x);    \* Fill it
E3: return;
end procedure;

\*
\* Deq() -> rval[self] : Values
\*
procedure Deq()
variables j, y, range, READ_return, SWAP_return
begin 
D1: while(TRUE) do
D2:   READ(q.back);
D3:   range := READ_return-1;
D4:   j := 1;
D5:   while(j<=range) do
D6:     SWAP(q.items[j], null);
D7:     y := SWAP_return;
        if(y /= null) then
D8:       await Head(ps) = y;
          ps := Tail(ps);
          rval[self] := y;
D9:       return;
        end if;
D10:    j:= j+1;
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
\* Procedure variable x of procedure Deq at line 63 col 14 changed to x_
CONSTANT defaultInitValue
VARIABLES pc, q, ps, op, arg, rval, done, stack, x, i, INC_return, j, x_, 
          range, READ_return, SWAP_return

vars == << pc, q, ps, op, arg, rval, done, stack, x, i, INC_return, j, x_, 
           range, READ_return, SWAP_return >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ q = [back|->1, items|->[n \in 1..Nmax|->null]]
        /\ ps = <<>>
        /\ op = [t \in Threads |-> ""]
        /\ arg = [t \in Threads |-> null]
        /\ rval = [t \in Threads |-> null]
        /\ done = [t \in Threads |-> TRUE]
        (* Procedure Enq *)
        /\ x = [ self \in ProcSet |-> defaultInitValue]
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        /\ INC_return = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Deq *)
        /\ j = [ self \in ProcSet |-> defaultInitValue]
        /\ x_ = [ self \in ProcSet |-> defaultInitValue]
        /\ range = [ self \in ProcSet |-> defaultInitValue]
        /\ READ_return = [ self \in ProcSet |-> defaultInitValue]
        /\ SWAP_return = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "enq"
                                        [] self \in Consumers -> "deq"]

E1(self) == /\ pc[self] = "E1"
            /\ /\ INC_return' = [INC_return EXCEPT ![self] = q.back]
               /\ q' = [q EXCEPT !.back = (q.back)+1]
            /\ i' = [i EXCEPT ![self] = INC_return'[self]]
            /\ \E p \in Pi:
                 ps' = Append(ps, p)
            /\ pc' = [pc EXCEPT ![self] = "E2"]
            /\ UNCHANGED << op, arg, rval, done, stack, x, j, x_, range, 
                            READ_return, SWAP_return >>

E2(self) == /\ pc[self] = "E2"
            /\ q' = [q EXCEPT !.items[i[self]] = x[self]]
            /\ pc' = [pc EXCEPT ![self] = "E3"]
            /\ UNCHANGED << ps, op, arg, rval, done, stack, x, i, INC_return, 
                            j, x_, range, READ_return, SWAP_return >>

E3(self) == /\ pc[self] = "E3"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
            /\ INC_return' = [INC_return EXCEPT ![self] = Head(stack[self]).INC_return]
            /\ x' = [x EXCEPT ![self] = Head(stack[self]).x]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << q, ps, op, arg, rval, done, j, x_, range, 
                            READ_return, SWAP_return >>

Enq(self) == E1(self) \/ E2(self) \/ E3(self)

D1(self) == /\ pc[self] = "D1"
            /\ pc' = [pc EXCEPT ![self] = "D2"]
            /\ UNCHANGED << q, ps, op, arg, rval, done, stack, x, i, 
                            INC_return, j, x_, range, READ_return, SWAP_return >>

D2(self) == /\ pc[self] = "D2"
            /\ READ_return' = [READ_return EXCEPT ![self] = q.back]
            /\ pc' = [pc EXCEPT ![self] = "D3"]
            /\ UNCHANGED << q, ps, op, arg, rval, done, stack, x, i, 
                            INC_return, j, x_, range, SWAP_return >>

D3(self) == /\ pc[self] = "D3"
            /\ range' = [range EXCEPT ![self] = READ_return[self]-1]
            /\ pc' = [pc EXCEPT ![self] = "D4"]
            /\ UNCHANGED << q, ps, op, arg, rval, done, stack, x, i, 
                            INC_return, j, x_, READ_return, SWAP_return >>

D4(self) == /\ pc[self] = "D4"
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "D5"]
            /\ UNCHANGED << q, ps, op, arg, rval, done, stack, x, i, 
                            INC_return, x_, range, READ_return, SWAP_return >>

D5(self) == /\ pc[self] = "D5"
            /\ IF (j[self]<=range[self])
                  THEN /\ pc' = [pc EXCEPT ![self] = "D6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << q, ps, op, arg, rval, done, stack, x, i, 
                            INC_return, j, x_, range, READ_return, SWAP_return >>

D6(self) == /\ pc[self] = "D6"
            /\ /\ SWAP_return' = [SWAP_return EXCEPT ![self] = q.items[j[self]]]
               /\ q' = [q EXCEPT !.items[j[self]] = null]
            /\ pc' = [pc EXCEPT ![self] = "D7"]
            /\ UNCHANGED << ps, op, arg, rval, done, stack, x, i, INC_return, 
                            j, x_, range, READ_return >>

D7(self) == /\ pc[self] = "D7"
            /\ x_' = [x_ EXCEPT ![self] = SWAP_return[self]]
            /\ IF (x_'[self] /= null)
                  THEN /\ pc' = [pc EXCEPT ![self] = "D8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D10"]
            /\ UNCHANGED << q, ps, op, arg, rval, done, stack, x, i, 
                            INC_return, j, range, READ_return, SWAP_return >>

D8(self) == /\ pc[self] = "D8"
            /\ Head(ps) = x_[self]
            /\ ps' = Tail(ps)
            /\ rval' = [rval EXCEPT ![self] = x_[self]]
            /\ pc' = [pc EXCEPT ![self] = "D9"]
            /\ UNCHANGED << q, op, arg, done, stack, x, i, INC_return, j, x_, 
                            range, READ_return, SWAP_return >>

D9(self) == /\ pc[self] = "D9"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ j' = [j EXCEPT ![self] = Head(stack[self]).j]
            /\ x_' = [x_ EXCEPT ![self] = Head(stack[self]).x_]
            /\ range' = [range EXCEPT ![self] = Head(stack[self]).range]
            /\ READ_return' = [READ_return EXCEPT ![self] = Head(stack[self]).READ_return]
            /\ SWAP_return' = [SWAP_return EXCEPT ![self] = Head(stack[self]).SWAP_return]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << q, ps, op, arg, rval, done, x, i, INC_return >>

D10(self) == /\ pc[self] = "D10"
             /\ j' = [j EXCEPT ![self] = j[self]+1]
             /\ pc' = [pc EXCEPT ![self] = "D5"]
             /\ UNCHANGED << q, ps, op, arg, rval, done, stack, x, i, 
                             INC_return, x_, range, READ_return, SWAP_return >>

Deq(self) == D1(self) \/ D2(self) \/ D3(self) \/ D4(self) \/ D5(self)
                \/ D6(self) \/ D7(self) \/ D8(self) \/ D9(self)
                \/ D10(self)

enq(self) == /\ pc[self] = "enq"
             /\ \E itm \in Values:
                  /\ op' = [op EXCEPT ![self] = "enq"]
                  /\ arg' = [arg EXCEPT ![self] = itm]
                  /\ rval' = [rval EXCEPT ![self] = null]
                  /\ done' = [done EXCEPT ![self] = FALSE]
                  /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enq",
                                                              pc        |->  "enqdone",
                                                              i         |->  i[self],
                                                              INC_return |->  INC_return[self],
                                                              x         |->  x[self] ] >>
                                                          \o stack[self]]
                     /\ x' = [x EXCEPT ![self] = itm]
                  /\ i' = [i EXCEPT ![self] = defaultInitValue]
                  /\ INC_return' = [INC_return EXCEPT ![self] = defaultInitValue]
                  /\ pc' = [pc EXCEPT ![self] = "E1"]
             /\ UNCHANGED << q, ps, j, x_, range, READ_return, SWAP_return >>

enqdone(self) == /\ pc[self] = "enqdone"
                 /\ done' = [done EXCEPT ![self] = TRUE]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << q, ps, op, arg, rval, stack, x, i, INC_return, 
                                 j, x_, range, READ_return, SWAP_return >>

prod(self) == enq(self) \/ enqdone(self)

deq(self) == /\ pc[self] = "deq"
             /\ op' = [op EXCEPT ![self] = "deq"]
             /\ arg' = [arg EXCEPT ![self] = null]
             /\ rval' = [rval EXCEPT ![self] = null]
             /\ done' = [done EXCEPT ![self] = FALSE]
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Deq",
                                                      pc        |->  "deqdone",
                                                      j         |->  j[self],
                                                      x_        |->  x_[self],
                                                      range     |->  range[self],
                                                      READ_return |->  READ_return[self],
                                                      SWAP_return |->  SWAP_return[self] ] >>
                                                  \o stack[self]]
             /\ j' = [j EXCEPT ![self] = defaultInitValue]
             /\ x_' = [x_ EXCEPT ![self] = defaultInitValue]
             /\ range' = [range EXCEPT ![self] = defaultInitValue]
             /\ READ_return' = [READ_return EXCEPT ![self] = defaultInitValue]
             /\ SWAP_return' = [SWAP_return EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "D1"]
             /\ UNCHANGED << q, ps, x, i, INC_return >>

deqdone(self) == /\ pc[self] = "deqdone"
                 /\ done' = [done EXCEPT ![self] = TRUE]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << q, ps, op, arg, rval, stack, x, i, INC_return, 
                                 j, x_, range, READ_return, SWAP_return >>

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

TypeOk == /\ queue \in [back: Nat, items: [1..Nmax -> Values \union {null}]]
          /\ ps \in Seq(Pi)
          (*
          /\ x_ \in [Producers->Values \union {defaultInitValue}]
          /\ i_ \in [Producers->Nat \union {defaultInitValue}]
          /\ INC_return \in [Producers->Nat \union {defaultInitValue}]
          *)

up == [t \in Threads |-> CASE t \in Producers -> pc[t] \in {"enq","E2", "E3", "enqdone"}
                           [] t \in Consumers -> pc[t] \in {"deq", "D9", "D10", "deqdone"}]


LQ == INSTANCE LinearizableQueue WITH 
    none <- null,
    d <- ps

Refinement == LQ!Spec

Alias == [
    pc |-> pc,
    op |-> op,
    arg |-> arg,
    rval |-> rval,
    done |-> done,
    up |-> up,
    d |-> ps,
    queue |-> queue,
    ps |-> ps,
    x_ |-> x_,
    i_ |-> i_,
    INC_return |-> INC_return,
    i |-> i,
    x |-> x,
    range |-> range,
    SWAP_return |-> SWAP_return,
    READ_return |-> READ_return
]

=============================================================================
\* Modification History
\* Last modified Thu Nov 08 17:28:50 PST 2018 by lhochstein
\* Created Wed Oct 24 18:53:25 PDT 2018 by lhochstein
