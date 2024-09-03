(***************************************************************************)
(*                                                                         *)
(* Queue qresentation type (REP) from Herlihy & Wing 1990.                 *)
(* Includes prophecy variables.                                            *)
(***************************************************************************)
------------------------------ MODULE HWQueue -----------------------
EXTENDS Naturals, Sequences

CONSTANTS Values, Producers, Consumers, Nmax

null == CHOOSE x : x \notin Values

Threads == Producers \union Consumers

(*--algorithm Rep 
variables 
    queue = [back|->1, items|->[n \in 1..Nmax|->null]];
    enq = [p \in Producers |-> Values];
    deq \in [Consumers -> Data];

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
\* Enq(q: queue, x: Values)
\*
procedure Enq(q, x)
variables 
    i; INC_return;
begin
E1: INC(q.back);
    i := INC_return;       \* Allocate a new slot
E2: STORE(q.items[i], x);    \* Fill it
E3: return;
end procedure;

\*
\* Deq(q: Queues) : Values
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
D8:       return;
        end if;
D9:    i:= i+1;
      end while;
    end while;
end procedure;


process prod \in Producers
begin 
enq:
    with itm \in Values do
        call Enq(queue, itm);
    end with;
enqdone:
    goto enq;
end process;

process con \in Consumers
begin
deq:
    call Deq(queue);
deqdone:
    goto deq;
end process;

end algorithm;*)
\* BEGIN TRANSLATION
\* Label enq of process prod at line 75 col 5 changed to enq_
\* Label deq of process con at line 85 col 5 changed to deq_
\* Procedure variable i of procedure Enq at line 42 col 5 changed to i_
\* Procedure variable x of procedure Deq at line 54 col 14 changed to x_
\* Parameter q of procedure Enq at line 40 col 15 changed to q_
CONSTANT defaultInitValue
VARIABLES pc, queue, enq, deq, stack, q_, x, i_, INC_return, q, i, x_, range, 
          READ_return, SWAP_return

vars == << pc, queue, enq, deq, stack, q_, x, i_, INC_return, q, i, x_, range, 
           READ_return, SWAP_return >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ queue = [back|->1, items|->[n \in 1..Nmax|->null]]
        /\ enq = [p \in Producers |-> Values]
        /\ deq \in [Consumers -> Data]
        (* Procedure Enq *)
        /\ q_ = [ self \in ProcSet |-> defaultInitValue]
        /\ x = [ self \in ProcSet |-> defaultInitValue]
        /\ i_ = [ self \in ProcSet |-> defaultInitValue]
        /\ INC_return = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Deq *)
        /\ q = [ self \in ProcSet |-> defaultInitValue]
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        /\ x_ = [ self \in ProcSet |-> defaultInitValue]
        /\ range = [ self \in ProcSet |-> defaultInitValue]
        /\ READ_return = [ self \in ProcSet |-> defaultInitValue]
        /\ SWAP_return = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "enq_"
                                        [] self \in Consumers -> "deq_"]

E1(self) == /\ pc[self] = "E1"
            /\ /\ INC_return' = [INC_return EXCEPT ![self] = q_[self].back]
               /\ q_' = [q_ EXCEPT ![self].back = (q_[self].back)+1]
            /\ i_' = [i_ EXCEPT ![self] = INC_return'[self]]
            /\ pc' = [pc EXCEPT ![self] = "E2"]
            /\ UNCHANGED << queue, enq, deq, stack, x, q, i, x_, range, 
                            READ_return, SWAP_return >>

E2(self) == /\ pc[self] = "E2"
            /\ q_' = [q_ EXCEPT ![self].items[i_[self]] = x[self]]
            /\ pc' = [pc EXCEPT ![self] = "E3"]
            /\ UNCHANGED << queue, enq, deq, stack, x, i_, INC_return, q, i, 
                            x_, range, READ_return, SWAP_return >>

E3(self) == /\ pc[self] = "E3"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ i_' = [i_ EXCEPT ![self] = Head(stack[self]).i_]
            /\ INC_return' = [INC_return EXCEPT ![self] = Head(stack[self]).INC_return]
            /\ q_' = [q_ EXCEPT ![self] = Head(stack[self]).q_]
            /\ x' = [x EXCEPT ![self] = Head(stack[self]).x]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << queue, enq, deq, q, i, x_, range, READ_return, 
                            SWAP_return >>

Enq(self) == E1(self) \/ E2(self) \/ E3(self)

D1(self) == /\ pc[self] = "D1"
            /\ pc' = [pc EXCEPT ![self] = "D2"]
            /\ UNCHANGED << queue, enq, deq, stack, q_, x, i_, INC_return, q, 
                            i, x_, range, READ_return, SWAP_return >>

D2(self) == /\ pc[self] = "D2"
            /\ READ_return' = [READ_return EXCEPT ![self] = q[self].back]
            /\ pc' = [pc EXCEPT ![self] = "D3"]
            /\ UNCHANGED << queue, enq, deq, stack, q_, x, i_, INC_return, q, 
                            i, x_, range, SWAP_return >>

D3(self) == /\ pc[self] = "D3"
            /\ range' = [range EXCEPT ![self] = READ_return[self]-1]
            /\ pc' = [pc EXCEPT ![self] = "D4"]
            /\ UNCHANGED << queue, enq, deq, stack, q_, x, i_, INC_return, q, 
                            i, x_, READ_return, SWAP_return >>

D4(self) == /\ pc[self] = "D4"
            /\ i' = [i EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "D5"]
            /\ UNCHANGED << queue, enq, deq, stack, q_, x, i_, INC_return, q, 
                            x_, range, READ_return, SWAP_return >>

D5(self) == /\ pc[self] = "D5"
            /\ IF (i[self]<=range[self])
                  THEN /\ pc' = [pc EXCEPT ![self] = "D6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << queue, enq, deq, stack, q_, x, i_, INC_return, q, 
                            i, x_, range, READ_return, SWAP_return >>

D6(self) == /\ pc[self] = "D6"
            /\ /\ SWAP_return' = [SWAP_return EXCEPT ![self] = q[self].items[i[self]]]
               /\ q' = [q EXCEPT ![self].items[i[self]] = null]
            /\ pc' = [pc EXCEPT ![self] = "D7"]
            /\ UNCHANGED << queue, enq, deq, stack, q_, x, i_, INC_return, i, 
                            x_, range, READ_return >>

D7(self) == /\ pc[self] = "D7"
            /\ x_' = [x_ EXCEPT ![self] = SWAP_return[self]]
            /\ IF (x_'[self] /= null)
                  THEN /\ pc' = [pc EXCEPT ![self] = "D8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D9"]
            /\ UNCHANGED << queue, enq, deq, stack, q_, x, i_, INC_return, q, 
                            i, range, READ_return, SWAP_return >>

D8(self) == /\ pc[self] = "D8"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
            /\ x_' = [x_ EXCEPT ![self] = Head(stack[self]).x_]
            /\ range' = [range EXCEPT ![self] = Head(stack[self]).range]
            /\ READ_return' = [READ_return EXCEPT ![self] = Head(stack[self]).READ_return]
            /\ SWAP_return' = [SWAP_return EXCEPT ![self] = Head(stack[self]).SWAP_return]
            /\ q' = [q EXCEPT ![self] = Head(stack[self]).q]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << queue, enq, deq, q_, x, i_, INC_return >>

D9(self) == /\ pc[self] = "D9"
            /\ i' = [i EXCEPT ![self] = i[self]+1]
            /\ pc' = [pc EXCEPT ![self] = "D5"]
            /\ UNCHANGED << queue, enq, deq, stack, q_, x, i_, INC_return, q, 
                            x_, range, READ_return, SWAP_return >>

Deq(self) == D1(self) \/ D2(self) \/ D3(self) \/ D4(self) \/ D5(self)
                \/ D6(self) \/ D7(self) \/ D8(self) \/ D9(self)

enq_(self) == /\ pc[self] = "enq_"
              /\ \E itm \in Values:
                   /\ /\ q_' = [q_ EXCEPT ![self] = queue]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enq",
                                                               pc        |->  "enqdone",
                                                               i_        |->  i_[self],
                                                               INC_return |->  INC_return[self],
                                                               q_        |->  q_[self],
                                                               x         |->  x[self] ] >>
                                                           \o stack[self]]
                      /\ x' = [x EXCEPT ![self] = itm]
                   /\ i_' = [i_ EXCEPT ![self] = defaultInitValue]
                   /\ INC_return' = [INC_return EXCEPT ![self] = defaultInitValue]
                   /\ pc' = [pc EXCEPT ![self] = "E1"]
              /\ UNCHANGED << queue, enq, deq, q, i, x_, range, READ_return, 
                              SWAP_return >>

enqdone(self) == /\ pc[self] = "enqdone"
                 /\ pc' = [pc EXCEPT ![self] = "enq_"]
                 /\ UNCHANGED << queue, enq, deq, stack, q_, x, i_, INC_return, 
                                 q, i, x_, range, READ_return, SWAP_return >>

prod(self) == enq_(self) \/ enqdone(self)

deq_(self) == /\ pc[self] = "deq_"
              /\ /\ q' = [q EXCEPT ![self] = queue]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Deq",
                                                          pc        |->  "deqdone",
                                                          i         |->  i[self],
                                                          x_        |->  x_[self],
                                                          range     |->  range[self],
                                                          READ_return |->  READ_return[self],
                                                          SWAP_return |->  SWAP_return[self],
                                                          q         |->  q[self] ] >>
                                                      \o stack[self]]
              /\ i' = [i EXCEPT ![self] = defaultInitValue]
              /\ x_' = [x_ EXCEPT ![self] = defaultInitValue]
              /\ range' = [range EXCEPT ![self] = defaultInitValue]
              /\ READ_return' = [READ_return EXCEPT ![self] = defaultInitValue]
              /\ SWAP_return' = [SWAP_return EXCEPT ![self] = defaultInitValue]
              /\ pc' = [pc EXCEPT ![self] = "D1"]
              /\ UNCHANGED << queue, enq, deq, q_, x, i_, INC_return >>

deqdone(self) == /\ pc[self] = "deqdone"
                 /\ pc' = [pc EXCEPT ![self] = "deq_"]
                 /\ UNCHANGED << queue, enq, deq, stack, q_, x, i_, INC_return, 
                                 q, i, x_, range, READ_return, SWAP_return >>

con(self) == deq_(self) \/ deqdone(self)

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

(*
Mapping == INSTANCE IPOFifo WITH 


Refinement == Mapping!Spec
*)

Alias == [
    pc |-> pc,
    queue |-> queue,
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
