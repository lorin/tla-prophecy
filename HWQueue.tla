------------------------------ MODULE HWQueue -----------------------
(***************************************************************************)
(* Queue qresentation type (REP) from Herlihy & Wing 1990.                 *)
(* Includes prophecy variables.                                            *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS Values, Producers, Consumers, Nmax, Busy, Done

null == CHOOSE x : x \notin Values

Threads == Producers \union Consumers

(*--algorithm Rep 
variables 
    queue = [back|->1, items|->[n \in 1..Nmax|->null]];
    ids = {};
    nextId = 0;

define
    GetId(ind) == (CHOOSE idd \in ids : idd[1]=ind)[2]
end define;

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
\* Enq(q: queue, x: Values, id: Nat)
\*
procedure Enq(q, x, id)
variables 
    i; INC_return;
begin
E1: INC(q.back);
    i := INC_return;       \* Allocate a new slot
E2: STORE(q.items[i], x);    \* Fill it
    ids := ids \union {<<i, id>>};
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
D8:     if(x /= null) then
D9:       deq := x;
          ids := ids \ {<<i, GetId(i)>>};
          return;
        end if;
D10:    i := i+1;
      end while;
    end while;
end procedure;


process prod \in Producers
variable enq = Done; id;
begin 
enq:
    with itm \in Values do
        enq := itm;
        id := nextId;
        nextId := nextId+1;
        call Enq(queue, itm, id);
    end with;
enqdone:
    enq := Done;
    goto enq;
end process;

process con \in Consumers
variable deq \in Values;
begin
deq:
    deq := Busy;
    call Deq(queue);
deqdone:
    goto deq;
end process;

end algorithm;*)
\* BEGIN TRANSLATION
\* Label enq of process prod at line 83 col 5 changed to enq_
\* Label deq of process con at line 98 col 5 changed to deq_
\* Process variable id of process prod at line 80 col 22 changed to id_
\* Procedure variable i of procedure Enq at line 46 col 5 changed to i_
\* Procedure variable x of procedure Deq at line 59 col 14 changed to x_
\* Parameter q of procedure Enq at line 44 col 15 changed to q_
CONSTANT defaultInitValue
VARIABLES pc, queue, ids, nextId, stack

(* define statement *)
GetId(ind) == (CHOOSE idd \in ids : idd[1]=ind)[2]

VARIABLES q_, x, id, i_, INC_return, q, i, x_, range, READ_return, 
          SWAP_return, enq, id_, deq

vars == << pc, queue, ids, nextId, stack, q_, x, id, i_, INC_return, q, i, x_, 
           range, READ_return, SWAP_return, enq, id_, deq >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ queue = [back|->1, items|->[n \in 1..Nmax|->null]]
        /\ ids = {}
        /\ nextId = 0
        (* Procedure Enq *)
        /\ q_ = [ self \in ProcSet |-> defaultInitValue]
        /\ x = [ self \in ProcSet |-> defaultInitValue]
        /\ id = [ self \in ProcSet |-> defaultInitValue]
        /\ i_ = [ self \in ProcSet |-> defaultInitValue]
        /\ INC_return = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Deq *)
        /\ q = [ self \in ProcSet |-> defaultInitValue]
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        /\ x_ = [ self \in ProcSet |-> defaultInitValue]
        /\ range = [ self \in ProcSet |-> defaultInitValue]
        /\ READ_return = [ self \in ProcSet |-> defaultInitValue]
        /\ SWAP_return = [ self \in ProcSet |-> defaultInitValue]
        (* Process prod *)
        /\ enq = [self \in Producers |-> Done]
        /\ id_ = [self \in Producers |-> defaultInitValue]
        (* Process con *)
        /\ deq \in [Consumers -> Values]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "enq_"
                                        [] self \in Consumers -> "deq_"]

E1(self) == /\ pc[self] = "E1"
            /\ /\ INC_return' = [INC_return EXCEPT ![self] = q_[self].back]
               /\ q_' = [q_ EXCEPT ![self].back = (q_[self].back)+1]
            /\ i_' = [i_ EXCEPT ![self] = INC_return'[self]]
            /\ pc' = [pc EXCEPT ![self] = "E2"]
            /\ UNCHANGED << queue, ids, nextId, stack, x, id, q, i, x_, range, 
                            READ_return, SWAP_return, enq, id_, deq >>

E2(self) == /\ pc[self] = "E2"
            /\ q_' = [q_ EXCEPT ![self].items[i_[self]] = x[self]]
            /\ ids' = (ids \union {<<i_[self], id[self]>>})
            /\ pc' = [pc EXCEPT ![self] = "E3"]
            /\ UNCHANGED << queue, nextId, stack, x, id, i_, INC_return, q, i, 
                            x_, range, READ_return, SWAP_return, enq, id_, deq >>

E3(self) == /\ pc[self] = "E3"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ i_' = [i_ EXCEPT ![self] = Head(stack[self]).i_]
            /\ INC_return' = [INC_return EXCEPT ![self] = Head(stack[self]).INC_return]
            /\ q_' = [q_ EXCEPT ![self] = Head(stack[self]).q_]
            /\ x' = [x EXCEPT ![self] = Head(stack[self]).x]
            /\ id' = [id EXCEPT ![self] = Head(stack[self]).id]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << queue, ids, nextId, q, i, x_, range, READ_return, 
                            SWAP_return, enq, id_, deq >>

Enq(self) == E1(self) \/ E2(self) \/ E3(self)

D1(self) == /\ pc[self] = "D1"
            /\ pc' = [pc EXCEPT ![self] = "D2"]
            /\ UNCHANGED << queue, ids, nextId, stack, q_, x, id, i_, 
                            INC_return, q, i, x_, range, READ_return, 
                            SWAP_return, enq, id_, deq >>

D2(self) == /\ pc[self] = "D2"
            /\ READ_return' = [READ_return EXCEPT ![self] = q[self].back]
            /\ pc' = [pc EXCEPT ![self] = "D3"]
            /\ UNCHANGED << queue, ids, nextId, stack, q_, x, id, i_, 
                            INC_return, q, i, x_, range, SWAP_return, enq, id_, 
                            deq >>

D3(self) == /\ pc[self] = "D3"
            /\ range' = [range EXCEPT ![self] = READ_return[self]-1]
            /\ pc' = [pc EXCEPT ![self] = "D4"]
            /\ UNCHANGED << queue, ids, nextId, stack, q_, x, id, i_, 
                            INC_return, q, i, x_, READ_return, SWAP_return, 
                            enq, id_, deq >>

D4(self) == /\ pc[self] = "D4"
            /\ i' = [i EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "D5"]
            /\ UNCHANGED << queue, ids, nextId, stack, q_, x, id, i_, 
                            INC_return, q, x_, range, READ_return, SWAP_return, 
                            enq, id_, deq >>

D5(self) == /\ pc[self] = "D5"
            /\ IF (i[self]<=range[self])
                  THEN /\ pc' = [pc EXCEPT ![self] = "D6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << queue, ids, nextId, stack, q_, x, id, i_, 
                            INC_return, q, i, x_, range, READ_return, 
                            SWAP_return, enq, id_, deq >>

D6(self) == /\ pc[self] = "D6"
            /\ /\ SWAP_return' = [SWAP_return EXCEPT ![self] = q[self].items[i[self]]]
               /\ q' = [q EXCEPT ![self].items[i[self]] = null]
            /\ pc' = [pc EXCEPT ![self] = "D7"]
            /\ UNCHANGED << queue, ids, nextId, stack, q_, x, id, i_, 
                            INC_return, i, x_, range, READ_return, enq, id_, 
                            deq >>

D7(self) == /\ pc[self] = "D7"
            /\ x_' = [x_ EXCEPT ![self] = SWAP_return[self]]
            /\ pc' = [pc EXCEPT ![self] = "D8"]
            /\ UNCHANGED << queue, ids, nextId, stack, q_, x, id, i_, 
                            INC_return, q, i, range, READ_return, SWAP_return, 
                            enq, id_, deq >>

D8(self) == /\ pc[self] = "D8"
            /\ IF (x_[self] /= null)
                  THEN /\ pc' = [pc EXCEPT ![self] = "D9"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D10"]
            /\ UNCHANGED << queue, ids, nextId, stack, q_, x, id, i_, 
                            INC_return, q, i, x_, range, READ_return, 
                            SWAP_return, enq, id_, deq >>

D9(self) == /\ pc[self] = "D9"
            /\ deq' = [deq EXCEPT ![self] = x_[self]]
            /\ ids' = ids \ {<<i[self], GetId(i[self])>>}
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
            /\ x_' = [x_ EXCEPT ![self] = Head(stack[self]).x_]
            /\ range' = [range EXCEPT ![self] = Head(stack[self]).range]
            /\ READ_return' = [READ_return EXCEPT ![self] = Head(stack[self]).READ_return]
            /\ SWAP_return' = [SWAP_return EXCEPT ![self] = Head(stack[self]).SWAP_return]
            /\ q' = [q EXCEPT ![self] = Head(stack[self]).q]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << queue, nextId, q_, x, id, i_, INC_return, enq, id_ >>

D10(self) == /\ pc[self] = "D10"
             /\ i' = [i EXCEPT ![self] = i[self]+1]
             /\ pc' = [pc EXCEPT ![self] = "D5"]
             /\ UNCHANGED << queue, ids, nextId, stack, q_, x, id, i_, 
                             INC_return, q, x_, range, READ_return, 
                             SWAP_return, enq, id_, deq >>

Deq(self) == D1(self) \/ D2(self) \/ D3(self) \/ D4(self) \/ D5(self)
                \/ D6(self) \/ D7(self) \/ D8(self) \/ D9(self)
                \/ D10(self)

enq_(self) == /\ pc[self] = "enq_"
              /\ \E itm \in Values:
                   /\ enq' = [enq EXCEPT ![self] = itm]
                   /\ id_' = [id_ EXCEPT ![self] = nextId]
                   /\ nextId' = nextId+1
                   /\ /\ id' = [id EXCEPT ![self] = id_'[self]]
                      /\ q_' = [q_ EXCEPT ![self] = queue]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enq",
                                                               pc        |->  "enqdone",
                                                               i_        |->  i_[self],
                                                               INC_return |->  INC_return[self],
                                                               q_        |->  q_[self],
                                                               x         |->  x[self],
                                                               id        |->  id[self] ] >>
                                                           \o stack[self]]
                      /\ x' = [x EXCEPT ![self] = itm]
                   /\ i_' = [i_ EXCEPT ![self] = defaultInitValue]
                   /\ INC_return' = [INC_return EXCEPT ![self] = defaultInitValue]
                   /\ pc' = [pc EXCEPT ![self] = "E1"]
              /\ UNCHANGED << queue, ids, q, i, x_, range, READ_return, 
                              SWAP_return, deq >>

enqdone(self) == /\ pc[self] = "enqdone"
                 /\ enq' = [enq EXCEPT ![self] = Done]
                 /\ pc' = [pc EXCEPT ![self] = "enq_"]
                 /\ UNCHANGED << queue, ids, nextId, stack, q_, x, id, i_, 
                                 INC_return, q, i, x_, range, READ_return, 
                                 SWAP_return, id_, deq >>

prod(self) == enq_(self) \/ enqdone(self)

deq_(self) == /\ pc[self] = "deq_"
              /\ deq' = [deq EXCEPT ![self] = Busy]
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
              /\ UNCHANGED << queue, ids, nextId, q_, x, id, i_, INC_return, 
                              enq, id_ >>

deqdone(self) == /\ pc[self] = "deqdone"
                 /\ pc' = [pc EXCEPT ![self] = "deq_"]
                 /\ UNCHANGED << queue, ids, nextId, stack, q_, x, id, i_, 
                                 INC_return, q, i, x_, range, READ_return, 
                                 SWAP_return, enq, id_, deq >>

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


eltsInArray == LET inds == {j \in 1..Nmax : queue.items # null}
               IN {<<queue.items[j], GetId(j)>> : j \in inds}

\* For states E1 and E2, an id has been chosen but it's not in the array yet
eltsBeingEnqueued == LET pds == {pd \in Producers : pc[pd] \in {"E1","E2"}}
                     IN {<<x[pd], id[pd]>> : pd \in pds}

eltsJustDequeued == LET crs == {cr \in Consumers : pc[cr]="D8" /\ x_[cr] # null }
                    IN {<<x_[cr], GetId(i)>> : cr \in crs}

elts == UNION {eltsInArray, eltsBeingEnqueued, eltsJustDequeued}

adding == [pd \in Producers |-> 
            CASE pc[pd] \in {"E1","E2","E3"} -> <<x[pd], id[pd]>>
              [] pc[pd] = "enqdone" -> <<enq[pd], id_[pd]>>
              [] OTHER -> null ]


before == {}

Mapping == INSTANCE IPOFifo WITH 
    EnQers <- Producers,
    DeQers <- Consumers,
    Data <- Values,
    Ids <- Nat



Refinement == Mapping!Spec

(*
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
*)

=============================================================================
\* Modification History
\* Last modified Thu Nov 08 17:28:50 PST 2018 by lhochstein
\* Created Wed Oct 24 18:53:25 PDT 2018 by lhochstein
