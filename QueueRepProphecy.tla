(***************************************************************************)
(*                                                                         *)
(* Queue qresentation type (REP) from Herlihy & Wing 1990.                 *)
(* Includes prophecy variables.                                            *)
(***************************************************************************)
------------------------------ MODULE QueueRepProphecy -----------------------
EXTENDS Naturals, Sequences

CONSTANTS item, producer, consumer, Nmax

null == CHOOSE x : x \notin item

Pi == item

threads == producer \union consumer

(*--algorithm Rep 
variables 
    q = [back|->1, items|->[n \in 1..Nmax|->null]];
    ps = <<>>;
    \* Public variables
    op = [t \in threads |-> ""];
    arg = [t \in threads |-> null];
    rval = [t \in threads |-> null];
    done = [t \in threads |-> TRUE];

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
\* Enq(q: queue, x: item)
\*
procedure Enq(q, x)
variables 
    i; 
    INC_return;
begin
E1: INC(q.back);
    i := INC_return;       \* Allocate a new slot
    with p \in Pi do
        ps := Append(ps, p);
    end with;
E2: STORE(q.items[i], x);    \* Fill it
    return;
end procedure;

\*
\* Deq(q: queue) -> rval[self] : item
\*
procedure Deq(q)
variables i, x, range, READ_return, SWAP_return
begin 
D1: while(TRUE) do
D2:   READ(q.back);
D3:   range := READ_return-1;
D4:   i := 1;
D5:   while(i<=range) do
D6:     SWAP(q.items[i], null);
D7:     x := SWAP_return;
        if(x /= null) then
D8:       await Head(ps) = x;
          ps := Tail(ps);
          rval[self] := x;
D9:       return;
        end if;
D10:    i:= i+1;
      end while;
    end while;
end procedure;


process prod \in producer
begin 
enq:
    with itm \in item
        op[self] := "enq";
        arg[self] := itm;
        rval[self] := null;
        done[self] := FALSE;
        call Enq(q, itm);
    end with
enqdone:
    done[self] := TRUE;
end process;

process con \in consumer
deq:
    op[self] := "deq";
    arg[self] := null;
    rval[self] := null;

    call Deq(q);
deqdone:
    done[self] := TRUE;

end process;

end algorithm;*)
\* BEGIN TRANSLATION
\* Process variable x of process prod at line 39 col 11 changed to x_
\* Process variable i of process prod at line 40 col 11 changed to i_
CONSTANT defaultInitValue
VARIABLES pc, q, ps, x_, i_, INC_return, p, i, x, range, READ_return, 
          SWAP_return, Deq_return

vars == << pc, q, ps, x_, i_, INC_return, p, i, x, range, READ_return, 
           SWAP_return, Deq_return >>

ProcSet == (producer) \cup (consumer)

Init == (* Global variables *)
        /\ q = [back|->1, items|->[n \in 1..Nmax|->null]]
        /\ ps = <<>>
        (* Process prod *)
        /\ x_ \in [producer -> item]
        /\ i_ = [self \in producer |-> defaultInitValue]
        /\ INC_return = [self \in producer |-> defaultInitValue]
        /\ p \in [producer -> Pi]
        (* Process con *)
        /\ i = [self \in consumer |-> defaultInitValue]
        /\ x = [self \in consumer |-> defaultInitValue]
        /\ range = [self \in consumer |-> defaultInitValue]
        /\ READ_return = [self \in consumer |-> defaultInitValue]
        /\ SWAP_return = [self \in consumer |-> defaultInitValue]
        /\ Deq_return = [self \in consumer |-> null]
        /\ pc = [self \in ProcSet |-> CASE self \in producer -> "E1"
                                        [] self \in consumer -> "D1"]

E1(self) == /\ pc[self] = "E1"
            /\ /\ INC_return' = [INC_return EXCEPT ![self] = q.back]
               /\ q' = [q EXCEPT !.back = (q.back)+1]
            /\ i_' = [i_ EXCEPT ![self] = INC_return'[self]]
            /\ ps' = Append(ps, p[self])
            /\ pc' = [pc EXCEPT ![self] = "E2"]
            /\ UNCHANGED << x_, p, i, x, range, READ_return, SWAP_return, 
                            Deq_return >>

E2(self) == /\ pc[self] = "E2"
            /\ q' = [q EXCEPT !.items[i_[self]] = x_[self]]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << ps, x_, i_, INC_return, p, i, x, range, 
                            READ_return, SWAP_return, Deq_return >>

prod(self) == E1(self) \/ E2(self)

D1(self) == /\ pc[self] = "D1"
            /\ pc' = [pc EXCEPT ![self] = "D2"]
            /\ UNCHANGED << q, ps, x_, i_, INC_return, p, i, x, range, 
                            READ_return, SWAP_return, Deq_return >>

D2(self) == /\ pc[self] = "D2"
            /\ READ_return' = [READ_return EXCEPT ![self] = q.back]
            /\ pc' = [pc EXCEPT ![self] = "D3"]
            /\ UNCHANGED << q, ps, x_, i_, INC_return, p, i, x, range, 
                            SWAP_return, Deq_return >>

D3(self) == /\ pc[self] = "D3"
            /\ range' = [range EXCEPT ![self] = READ_return[self]-1]
            /\ pc' = [pc EXCEPT ![self] = "D4"]
            /\ UNCHANGED << q, ps, x_, i_, INC_return, p, i, x, READ_return, 
                            SWAP_return, Deq_return >>

D4(self) == /\ pc[self] = "D4"
            /\ i' = [i EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "D5"]
            /\ UNCHANGED << q, ps, x_, i_, INC_return, p, x, range, 
                            READ_return, SWAP_return, Deq_return >>

D5(self) == /\ pc[self] = "D5"
            /\ IF (i[self]<=range[self])
                  THEN /\ pc' = [pc EXCEPT ![self] = "D6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << q, ps, x_, i_, INC_return, p, i, x, range, 
                            READ_return, SWAP_return, Deq_return >>

D6(self) == /\ pc[self] = "D6"
            /\ /\ SWAP_return' = [SWAP_return EXCEPT ![self] = q.items[i[self]]]
               /\ q' = [q EXCEPT !.items[i[self]] = null]
            /\ pc' = [pc EXCEPT ![self] = "D7"]
            /\ UNCHANGED << ps, x_, i_, INC_return, p, i, x, range, 
                            READ_return, Deq_return >>

D7(self) == /\ pc[self] = "D7"
            /\ x' = [x EXCEPT ![self] = SWAP_return[self]]
            /\ IF (x'[self] /= null)
                  THEN /\ pc' = [pc EXCEPT ![self] = "D8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D10"]
            /\ UNCHANGED << q, ps, x_, i_, INC_return, p, i, range, 
                            READ_return, SWAP_return, Deq_return >>

D8(self) == /\ pc[self] = "D8"
            /\ Head(ps) = x[self]
            /\ ps' = Tail(ps)
            /\ Deq_return' = [Deq_return EXCEPT ![self] = x[self]]
            /\ pc' = [pc EXCEPT ![self] = "D9"]
            /\ UNCHANGED << q, x_, i_, INC_return, p, i, x, range, READ_return, 
                            SWAP_return >>

D9(self) == /\ pc[self] = "D9"
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << q, ps, x_, i_, INC_return, p, i, x, range, 
                            READ_return, SWAP_return, Deq_return >>

D10(self) == /\ pc[self] = "D10"
             /\ i' = [i EXCEPT ![self] = i[self]+1]
             /\ pc' = [pc EXCEPT ![self] = "D5"]
             /\ UNCHANGED << q, ps, x_, i_, INC_return, p, x, range, 
                             READ_return, SWAP_return, Deq_return >>

con(self) == D1(self) \/ D2(self) \/ D3(self) \/ D4(self) \/ D5(self)
                \/ D6(self) \/ D7(self) \/ D8(self) \/ D9(self)
                \/ D10(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in producer: prod(self))
           \/ (\E self \in consumer: con(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

NotDone == ~(\A self \in ProcSet: pc[self] = "Done")

TypeOk == /\ q \in [back: Nat, items: [1..Nmax -> item \union {null}]]
          /\ ps \in Seq(Pi)
          /\ x_ \in [producer->item]
          /\ i_ \in [producer->Nat \union {defaultInitValue}]
          /\ INC_return \in [producer->Nat \union {defaultInitValue}]
          /\ p \in [producer->Pi]

(*

pcBar == [c \in producer \union consumer |->
    CASE pc[c] \in {"P1", "E1"} -> "E"
      [] pc[c] \in {"C1", "D1", "D2", "D3", "D4", "D5", "D6", "D7", "D8", "D10"} -> "D"
      [] pc[c] \in {"E2", "E3", "D9", "Done"} -> "Done"
]
itemsBar == ps
xBar == p
retValBar == [c \in consumer |-> IF pc[c] \in {"D9", "Done"} THEN Deq_return[c] ELSE null]

Mapping ==
    INSTANCE Queue WITH
        pc <- pcBar,
        items <- itemsBar,
        x <- xBar,
        retVal <- retValBar,
        Val <- item,
        Producers <- producer,
        Consumers <- consumer
*)

tmpBar == Deq_return
rvalBar == null
rval_Bar == null
pcBar == null

Mapping ==
    INSTANCE LinQueue WITH
        tmp <- tmpBar,
        rval <- rvalBar,
        rval_ <- rval_Bar,
        pc <- pcBar



Refinement == Mapping!Spec

Alias == [
    q |-> q,
    ps |-> ps,
    x_ |-> x_,
    i_ |-> i_,
    INC_return |-> INC_return,
    p |-> p,
    i |-> i,
    x |-> x,
    pc |-> pc,
    tmpBar |-> tmpBar,
    pcBar |-> pcBar,
    rvalBar |-> rvalBar,
    rval_Bar |-> rval_Bar,
    range |-> range,
    SWAP_return |-> SWAP_return,
    Deq_return |-> Deq_return,
    READ_return |-> READ_return
]

=============================================================================
\* Modification History
\* Last modified Thu Nov 08 17:28:50 PST 2018 by lhochstein
\* Created Wed Oct 24 18:53:25 PDT 2018 by lhochstein
