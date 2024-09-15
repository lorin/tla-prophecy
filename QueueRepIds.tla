------------------------------ MODULE QueueRepIds ----------------------------
(***************************************************************************)
(*                                                                         *)
(* Queue representation type (REP) from Herlihy & Wing 1990.               *)
(* Includes Ids to support refinemnet mapping.                             *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS Values, Producers, Consumers, Nmax, Busy, Done, MaxId

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
    nextId = 1;

    (***
     * Set of data items where (D1,D2) is an element if D1 was added to q.items before D2 incremented q.back
     *)
    before = {};

define
    Add(f, k, v) == [x \in DOMAIN f \union {k} |-> IF x=k THEN v ELSE f[x]]
    Del(f, k) == [x \in DOMAIN f \ {k} |-> f[x]]
    eltsInArray == LET inds == {i \in 1..(q.back-1) : q.items[i] # null}
                    IN {<<q.items[i], ids[i]>> : i \in inds}
    queueIsFull == q.back > Nmax
end define;


(***********************************)
(* Enq(x: Values, id: Nat)         *)
(***********************************)
procedure Enq(x, id)
variable i;
begin
E1: await ~queueIsFull; \* Deadlock if the queue fills
    q.back := q.back+1 || i := q.back; (* Allocate a new slot *)
    before := before \union {<<d, <<x, id>>>> : d \in eltsInArray};
E2: q.items[i] := x;                   (* Fill it *)
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

      if(y /= null) then (* this is just for the refinement mapping *)
         idd := ids[j];
         before := before \ {r \in before : LET d == <<y, idd>> IN r[1]=d \/ r[2]=d};
         ids := Del(ids, j);
      end if;

D6:   if(y /= null) then
D7:       rval[self] := y;
D8:       return;
        end if;
D9:     j:= j+1;
      end while;
    end while;
end procedure;


process prod \in Producers
variable ide;
begin
callenq:
    await nextId < MaxId;
    with item \in Values do
        op[self] := "enq";
        arg[self] := item;
        rval[self] := null;
        done[self] := FALSE;
        ide := nextId || nextId := nextId+1;
        call Enq(item, ide);
    end with;
returnenq:
    done[self] := TRUE;
    goto callenq;
end process;

process con \in Consumers
begin
calldeq:
    op[self] := "deq";
    arg[self] := null;
    rval[self] := null;
    done[self] := FALSE;
    call Deq();
returndeq:
    done[self] := TRUE;
    goto calldeq;
end process;

end algorithm;*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES pc, op, arg, rval, done, q, ids, nextId, before, stack

(* define statement *)
Add(f, k, v) == [x \in DOMAIN f \union {k} |-> IF x=k THEN v ELSE f[x]]
Del(f, k) == [x \in DOMAIN f \ {k} |-> f[x]]
eltsInArray == LET inds == {i \in 1..(q.back-1) : q.items[i] # null}
                IN {<<q.items[i], ids[i]>> : i \in inds}
queueIsFull == q.back > Nmax

VARIABLES x, id, i, j, y, range, idd, ide

vars == << pc, op, arg, rval, done, q, ids, nextId, before, stack, x, id, i, 
           j, y, range, idd, ide >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ op = [t \in ProcSet |-> ""]
        /\ arg = [t \in ProcSet |-> null]
        /\ rval = [t \in ProcSet |-> null]
        /\ done = [t \in ProcSet |-> TRUE]
        /\ q = [back|->1, items|->[n \in 1..Nmax|->null]]
        /\ ids = <<>>
        /\ nextId = 1
        /\ before = {}
        (* Procedure Enq *)
        /\ x = [ self \in ProcSet |-> defaultInitValue]
        /\ id = [ self \in ProcSet |-> defaultInitValue]
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Deq *)
        /\ j = [ self \in ProcSet |-> defaultInitValue]
        /\ y = [ self \in ProcSet |-> defaultInitValue]
        /\ range = [ self \in ProcSet |-> defaultInitValue]
        /\ idd = [ self \in ProcSet |-> defaultInitValue]
        (* Process prod *)
        /\ ide = [self \in Producers |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "callenq"
                                        [] self \in Consumers -> "calldeq"]

E1(self) == /\ pc[self] = "E1"
            /\ ~queueIsFull
            /\ /\ i' = [i EXCEPT ![self] = q.back]
               /\ q' = [q EXCEPT !.back = q.back+1]
            /\ before' = (before \union {<<d, <<x[self], id[self]>>>> : d \in eltsInArray})
            /\ pc' = [pc EXCEPT ![self] = "E2"]
            /\ UNCHANGED << op, arg, rval, done, ids, nextId, stack, x, id, j, 
                            y, range, idd, ide >>

E2(self) == /\ pc[self] = "E2"
            /\ q' = [q EXCEPT !.items[i[self]] = x[self]]
            /\ ids' = Add(ids, i[self], id[self])
            /\ pc' = [pc EXCEPT ![self] = "E3"]
            /\ UNCHANGED << op, arg, rval, done, nextId, before, stack, x, id, 
                            i, j, y, range, idd, ide >>

E3(self) == /\ pc[self] = "E3"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
            /\ x' = [x EXCEPT ![self] = Head(stack[self]).x]
            /\ id' = [id EXCEPT ![self] = Head(stack[self]).id]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << op, arg, rval, done, q, ids, nextId, before, j, y, 
                            range, idd, ide >>

Enq(self) == E1(self) \/ E2(self) \/ E3(self)

D1(self) == /\ pc[self] = "D1"
            /\ pc' = [pc EXCEPT ![self] = "D2"]
            /\ UNCHANGED << op, arg, rval, done, q, ids, nextId, before, stack, 
                            x, id, i, j, y, range, idd, ide >>

D2(self) == /\ pc[self] = "D2"
            /\ range' = [range EXCEPT ![self] = q.back-1]
            /\ pc' = [pc EXCEPT ![self] = "D3"]
            /\ UNCHANGED << op, arg, rval, done, q, ids, nextId, before, stack, 
                            x, id, i, j, y, idd, ide >>

D3(self) == /\ pc[self] = "D3"
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "D4"]
            /\ UNCHANGED << op, arg, rval, done, q, ids, nextId, before, stack, 
                            x, id, i, y, range, idd, ide >>

D4(self) == /\ pc[self] = "D4"
            /\ IF (j[self]<=range[self])
                  THEN /\ pc' = [pc EXCEPT ![self] = "D5"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << op, arg, rval, done, q, ids, nextId, before, stack, 
                            x, id, i, j, y, range, idd, ide >>

D5(self) == /\ pc[self] = "D5"
            /\ /\ q' = [q EXCEPT !.items[j[self]] = null]
               /\ y' = [y EXCEPT ![self] = q.items[j[self]]]
            /\ IF (y'[self] /= null)
                  THEN /\ idd' = [idd EXCEPT ![self] = ids[j[self]]]
                       /\ before' = before \ {r \in before : LET d == <<y'[self], idd'[self]>> IN r[1]=d \/ r[2]=d}
                       /\ ids' = Del(ids, j[self])
                  ELSE /\ TRUE
                       /\ UNCHANGED << ids, before, idd >>
            /\ pc' = [pc EXCEPT ![self] = "D6"]
            /\ UNCHANGED << op, arg, rval, done, nextId, stack, x, id, i, j, 
                            range, ide >>

D6(self) == /\ pc[self] = "D6"
            /\ IF (y[self] /= null)
                  THEN /\ pc' = [pc EXCEPT ![self] = "D7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D9"]
            /\ UNCHANGED << op, arg, rval, done, q, ids, nextId, before, stack, 
                            x, id, i, j, y, range, idd, ide >>

D7(self) == /\ pc[self] = "D7"
            /\ rval' = [rval EXCEPT ![self] = y[self]]
            /\ pc' = [pc EXCEPT ![self] = "D8"]
            /\ UNCHANGED << op, arg, done, q, ids, nextId, before, stack, x, 
                            id, i, j, y, range, idd, ide >>

D8(self) == /\ pc[self] = "D8"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ j' = [j EXCEPT ![self] = Head(stack[self]).j]
            /\ y' = [y EXCEPT ![self] = Head(stack[self]).y]
            /\ range' = [range EXCEPT ![self] = Head(stack[self]).range]
            /\ idd' = [idd EXCEPT ![self] = Head(stack[self]).idd]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << op, arg, rval, done, q, ids, nextId, before, x, id, 
                            i, ide >>

D9(self) == /\ pc[self] = "D9"
            /\ j' = [j EXCEPT ![self] = j[self]+1]
            /\ pc' = [pc EXCEPT ![self] = "D4"]
            /\ UNCHANGED << op, arg, rval, done, q, ids, nextId, before, stack, 
                            x, id, i, y, range, idd, ide >>

Deq(self) == D1(self) \/ D2(self) \/ D3(self) \/ D4(self) \/ D5(self)
                \/ D6(self) \/ D7(self) \/ D8(self) \/ D9(self)

callenq(self) == /\ pc[self] = "callenq"
                 /\ nextId < MaxId
                 /\ \E item \in Values:
                      /\ op' = [op EXCEPT ![self] = "enq"]
                      /\ arg' = [arg EXCEPT ![self] = item]
                      /\ rval' = [rval EXCEPT ![self] = null]
                      /\ done' = [done EXCEPT ![self] = FALSE]
                      /\ /\ ide' = [ide EXCEPT ![self] = nextId]
                         /\ nextId' = nextId+1
                      /\ /\ id' = [id EXCEPT ![self] = ide'[self]]
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Enq",
                                                                  pc        |->  "returnenq",
                                                                  i         |->  i[self],
                                                                  x         |->  x[self],
                                                                  id        |->  id[self] ] >>
                                                              \o stack[self]]
                         /\ x' = [x EXCEPT ![self] = item]
                      /\ i' = [i EXCEPT ![self] = defaultInitValue]
                      /\ pc' = [pc EXCEPT ![self] = "E1"]
                 /\ UNCHANGED << q, ids, before, j, y, range, idd >>

returnenq(self) == /\ pc[self] = "returnenq"
                   /\ done' = [done EXCEPT ![self] = TRUE]
                   /\ pc' = [pc EXCEPT ![self] = "callenq"]
                   /\ UNCHANGED << op, arg, rval, q, ids, nextId, before, 
                                   stack, x, id, i, j, y, range, idd, ide >>

prod(self) == callenq(self) \/ returnenq(self)

calldeq(self) == /\ pc[self] = "calldeq"
                 /\ op' = [op EXCEPT ![self] = "deq"]
                 /\ arg' = [arg EXCEPT ![self] = null]
                 /\ rval' = [rval EXCEPT ![self] = null]
                 /\ done' = [done EXCEPT ![self] = FALSE]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Deq",
                                                          pc        |->  "returndeq",
                                                          j         |->  j[self],
                                                          y         |->  y[self],
                                                          range     |->  range[self],
                                                          idd       |->  idd[self] ] >>
                                                      \o stack[self]]
                 /\ j' = [j EXCEPT ![self] = defaultInitValue]
                 /\ y' = [y EXCEPT ![self] = defaultInitValue]
                 /\ range' = [range EXCEPT ![self] = defaultInitValue]
                 /\ idd' = [idd EXCEPT ![self] = defaultInitValue]
                 /\ pc' = [pc EXCEPT ![self] = "D1"]
                 /\ UNCHANGED << q, ids, nextId, before, x, id, i, ide >>

returndeq(self) == /\ pc[self] = "returndeq"
                   /\ done' = [done EXCEPT ![self] = TRUE]
                   /\ pc' = [pc EXCEPT ![self] = "calldeq"]
                   /\ UNCHANGED << op, arg, rval, q, ids, nextId, before, 
                                   stack, x, id, i, j, y, range, idd, ide >>

con(self) == calldeq(self) \/ returndeq(self)

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

BackNeverExceedsOneMoreThanQueueSize == q.back <= Nmax+1

NonElt == CHOOSE NonElt: NonElt \notin (Values \X Nat)

elts == LET producersAboutToWrite == {e \in Producers : pc[e]="E2"}
            eltsNotYetInArray == {<<x[e], id[e]>> : e \in producersAboutToWrite}
        IN eltsInArray \union eltsNotYetInArray

enq == [pd \in Producers |-> IF pc[pd] \in {"E2"} THEN x[pd] ELSE Done]
deq == [cn \in Consumers |-> CASE pc[cn] \in {"D8", "returndeq"} -> rval[cn]
                               [] pc[cn]="D6" /\ y[cn] # null -> y[cn]
                               [] pc[cn]="D6" /\ y[cn] = null -> Busy
                               [] pc[cn]="D7" -> y[cn]
                               [] pc[cn] \in {"D1", "D2", "D3", "D4", "D5", "D9"} -> Busy
                               [] OTHER -> CHOOSE v \in Values : TRUE]

adding == [pd \in Producers |-> IF pc[pd]="E2"
                                THEN <<x[pd], id[pd]>>
                                ELSE NonElt ]

POFifo == INSTANCE POFifo WITH
    EnQers <- Producers,
    DeQers <- Consumers,
    Data <- Values,
    Ids <- 1..MaxId

POFifoSpec == POFifo!Spec

Alias == [
    pc |-> pc,

    enq |-> enq,
    deq |-> deq,
    elts |-> elts,
    before |-> before,
    adding |-> adding,

    i |-> i,
    j |-> j,
    x |-> x,
    y |-> y,

    q |-> q,
    ids |-> ids,
    nextId |-> nextId,
    Data |-> Values,
    Ids |-> 1..MaxId,
    beingAdded |-> {adding[e] : e \in Producers} \ {NonElt}
]

=============================================================================
\* Modification History
\* Last modified Thu Nov 08 17:28:50 PST 2018 by lhochstein
\* Created Wed Oct 24 18:53:25 PDT 2018 by lhochstein
