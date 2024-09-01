---- MODULE LLLQueue ----
EXTENDS Sequences, Naturals

CONSTANTS Values,Producers,Consumers, MaxNode

AllPossibleNodes == 1..MaxNode 
None == 0

NoVal == CHOOSE v : v \notin Values

Threads == Producers \union Consumers

(*--algorithm LLLQueue 
variables 
    nodes = {};
    vals = <<>>;
    next = <<>>;
    prev = <<>>;
    head = None;
    tail = None;
    lock = {};
    \* Public variables
    op = [t \in Threads |-> ""];
    arg = [t \in Threads |-> NoVal];
    rval = [t \in Threads |-> NoVal];
    done = [t \in Threads |-> TRUE];

define
    IsEmpty == head = None
    Add(f,k,v) == [x \in DOMAIN f \union {k} |-> IF x=k THEN v ELSE f[x]]
end define;

macro Node(n, vl, nxt) begin
    nodes := nodes \union {n};
    vals := Add(vals, n, vl);
    next := Add(next, n, tail);
    prev := Add(prev, n, None);
end macro;

macro acquire(lck) begin
    await lck = {};
    lck := {self};
end macro;

macro release(lck) begin
    lck := {};
end macro;

(**********************)
(* Enqueue            *)
(**********************)
procedure enqueue(val)
variable new_tail;
begin
E1:
    acquire(lock);
E2: 
    with n \in AllPossibleNodes \ nodes do
        Node(n, val, nxt);
        new_tail := n;
    end with;
E3:
    if IsEmpty then
        head := new_tail;
    else
        prev[tail] := new_tail;
    end if;
    tail := new_tail;
E4:
    release(lock);
E5:
    return;
end procedure;


(**********************)
(* Dequeue            *)
(**********************)
procedure dequeue()
variables 
    empty = TRUE; 
    val;
begin
D1:
    while empty do
D2:
        acquire(lock);
D3:
        if IsEmpty then
D4:
            release(lock);
        else
            empty := FALSE;
        end if;
    end while;
D5:
    val := vals[head];
    head := prev[head];
    if head = None then
        tail := None;
    else
        next[head] := None;
    end if;
D6:
    release(lock);
D7:
    rval[self] := val;
    return;
end procedure;

process p \in Producers
begin
enq: \* choose a value
    with x \in Values do
        op[self] := "enq";
        arg[self] := x;
        rval[self] := None;
        done[self] := FALSE;
        call enqueue(x);
    end with;
enqdone:
    done[self] := TRUE;
    goto enq;

end process;


process c \in Consumers begin
deq:
    op[self] := "deq";
    arg[self] := None;
    rval[self] := None;
    done[self] := FALSE;
    call dequeue();
deqdone:
    done[self] := TRUE;
    goto deq;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "1801122e" /\ chksum(tla) = "784159dc")
\* Procedure variable val of procedure dequeue at line 82 col 5 changed to val_
CONSTANT defaultInitValue
VARIABLES pc, nodes, vals, next, prev, head, tail, lock, op, arg, rval, done, 
          stack

(* define statement *)
IsEmpty == head = None
Add(f,k,v) == [x \in DOMAIN f \union {k} |-> IF x=k THEN v ELSE f[x]]

VARIABLES val, new_tail, empty, val_

vars == << pc, nodes, vals, next, prev, head, tail, lock, op, arg, rval, done, 
           stack, val, new_tail, empty, val_ >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ nodes = {}
        /\ vals = <<>>
        /\ next = <<>>
        /\ prev = <<>>
        /\ head = None
        /\ tail = None
        /\ lock = {}
        /\ op = [t \in Threads |-> ""]
        /\ arg = [t \in Threads |-> NoVal]
        /\ rval = [t \in Threads |-> NoVal]
        /\ done = [t \in Threads |-> TRUE]
        (* Procedure enqueue *)
        /\ val = [ self \in ProcSet |-> defaultInitValue]
        /\ new_tail = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure dequeue *)
        /\ empty = [ self \in ProcSet |-> TRUE]
        /\ val_ = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "enq"
                                        [] self \in Consumers -> "deq"]

E1(self) == /\ pc[self] = "E1"
            /\ lock = {}
            /\ lock' = {self}
            /\ pc' = [pc EXCEPT ![self] = "E2"]
            /\ UNCHANGED << nodes, vals, next, prev, head, tail, op, arg, rval, 
                            done, stack, val, new_tail, empty, val_ >>

E2(self) == /\ pc[self] = "E2"
            /\ \E n \in AllPossibleNodes \ nodes:
                 /\ nodes' = (nodes \union {n})
                 /\ vals' = Add(vals, n, val[self])
                 /\ next' = Add(next, n, tail)
                 /\ prev' = Add(prev, n, None)
                 /\ new_tail' = [new_tail EXCEPT ![self] = n]
            /\ pc' = [pc EXCEPT ![self] = "E3"]
            /\ UNCHANGED << head, tail, lock, op, arg, rval, done, stack, val, 
                            empty, val_ >>

E3(self) == /\ pc[self] = "E3"
            /\ IF IsEmpty
                  THEN /\ head' = new_tail[self]
                       /\ prev' = prev
                  ELSE /\ prev' = [prev EXCEPT ![tail] = new_tail[self]]
                       /\ head' = head
            /\ tail' = new_tail[self]
            /\ pc' = [pc EXCEPT ![self] = "E4"]
            /\ UNCHANGED << nodes, vals, next, lock, op, arg, rval, done, 
                            stack, val, new_tail, empty, val_ >>

E4(self) == /\ pc[self] = "E4"
            /\ lock' = {}
            /\ pc' = [pc EXCEPT ![self] = "E5"]
            /\ UNCHANGED << nodes, vals, next, prev, head, tail, op, arg, rval, 
                            done, stack, val, new_tail, empty, val_ >>

E5(self) == /\ pc[self] = "E5"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ new_tail' = [new_tail EXCEPT ![self] = Head(stack[self]).new_tail]
            /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << nodes, vals, next, prev, head, tail, lock, op, arg, 
                            rval, done, empty, val_ >>

enqueue(self) == E1(self) \/ E2(self) \/ E3(self) \/ E4(self) \/ E5(self)

D1(self) == /\ pc[self] = "D1"
            /\ IF empty[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "D2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "D5"]
            /\ UNCHANGED << nodes, vals, next, prev, head, tail, lock, op, arg, 
                            rval, done, stack, val, new_tail, empty, val_ >>

D2(self) == /\ pc[self] = "D2"
            /\ lock = {}
            /\ lock' = {self}
            /\ pc' = [pc EXCEPT ![self] = "D3"]
            /\ UNCHANGED << nodes, vals, next, prev, head, tail, op, arg, rval, 
                            done, stack, val, new_tail, empty, val_ >>

D3(self) == /\ pc[self] = "D3"
            /\ IF IsEmpty
                  THEN /\ pc' = [pc EXCEPT ![self] = "D4"]
                       /\ empty' = empty
                  ELSE /\ empty' = [empty EXCEPT ![self] = FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << nodes, vals, next, prev, head, tail, lock, op, arg, 
                            rval, done, stack, val, new_tail, val_ >>

D4(self) == /\ pc[self] = "D4"
            /\ lock' = {}
            /\ pc' = [pc EXCEPT ![self] = "D1"]
            /\ UNCHANGED << nodes, vals, next, prev, head, tail, op, arg, rval, 
                            done, stack, val, new_tail, empty, val_ >>

D5(self) == /\ pc[self] = "D5"
            /\ val_' = [val_ EXCEPT ![self] = vals[head]]
            /\ head' = prev[head]
            /\ IF head' = None
                  THEN /\ tail' = None
                       /\ next' = next
                  ELSE /\ next' = [next EXCEPT ![head'] = None]
                       /\ tail' = tail
            /\ pc' = [pc EXCEPT ![self] = "D6"]
            /\ UNCHANGED << nodes, vals, prev, lock, op, arg, rval, done, 
                            stack, val, new_tail, empty >>

D6(self) == /\ pc[self] = "D6"
            /\ lock' = {}
            /\ pc' = [pc EXCEPT ![self] = "D7"]
            /\ UNCHANGED << nodes, vals, next, prev, head, tail, op, arg, rval, 
                            done, stack, val, new_tail, empty, val_ >>

D7(self) == /\ pc[self] = "D7"
            /\ rval' = [rval EXCEPT ![self] = val_[self]]
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ empty' = [empty EXCEPT ![self] = Head(stack[self]).empty]
            /\ val_' = [val_ EXCEPT ![self] = Head(stack[self]).val_]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << nodes, vals, next, prev, head, tail, lock, op, arg, 
                            done, val, new_tail >>

dequeue(self) == D1(self) \/ D2(self) \/ D3(self) \/ D4(self) \/ D5(self)
                    \/ D6(self) \/ D7(self)

enq(self) == /\ pc[self] = "enq"
             /\ \E x \in Values:
                  /\ op' = [op EXCEPT ![self] = "enq"]
                  /\ arg' = [arg EXCEPT ![self] = x]
                  /\ rval' = [rval EXCEPT ![self] = None]
                  /\ done' = [done EXCEPT ![self] = FALSE]
                  /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "enqueue",
                                                              pc        |->  "enqdone",
                                                              new_tail  |->  new_tail[self],
                                                              val       |->  val[self] ] >>
                                                          \o stack[self]]
                     /\ val' = [val EXCEPT ![self] = x]
                  /\ new_tail' = [new_tail EXCEPT ![self] = defaultInitValue]
                  /\ pc' = [pc EXCEPT ![self] = "E1"]
             /\ UNCHANGED << nodes, vals, next, prev, head, tail, lock, empty, 
                             val_ >>

enqdone(self) == /\ pc[self] = "enqdone"
                 /\ done' = [done EXCEPT ![self] = TRUE]
                 /\ pc' = [pc EXCEPT ![self] = "enq"]
                 /\ UNCHANGED << nodes, vals, next, prev, head, tail, lock, op, 
                                 arg, rval, stack, val, new_tail, empty, val_ >>

p(self) == enq(self) \/ enqdone(self)

deq(self) == /\ pc[self] = "deq"
             /\ op' = [op EXCEPT ![self] = "deq"]
             /\ arg' = [arg EXCEPT ![self] = None]
             /\ rval' = [rval EXCEPT ![self] = None]
             /\ done' = [done EXCEPT ![self] = FALSE]
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "dequeue",
                                                      pc        |->  "deqdone",
                                                      empty     |->  empty[self],
                                                      val_      |->  val_[self] ] >>
                                                  \o stack[self]]
             /\ empty' = [empty EXCEPT ![self] = TRUE]
             /\ val_' = [val_ EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "D1"]
             /\ UNCHANGED << nodes, vals, next, prev, head, tail, lock, val, 
                             new_tail >>

deqdone(self) == /\ pc[self] = "deqdone"
                 /\ done' = [done EXCEPT ![self] = TRUE]
                 /\ pc' = [pc EXCEPT ![self] = "deq"]
                 /\ UNCHANGED << nodes, vals, next, prev, head, tail, lock, op, 
                                 arg, rval, stack, val, new_tail, empty, val_ >>

c(self) == deq(self) \/ deqdone(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: enqueue(self) \/ dequeue(self))
           \/ (\E self \in Producers: p(self))
           \/ (\E self \in Consumers: c(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

TypeOk == /\ nodes \subseteq  AllPossibleNodes
          /\ vals \in [nodes -> Values]
          /\ next \in [nodes -> nodes \union {None}]
          /\ prev \in [nodes -> nodes \union {None}]
          /\ head \in nodes \union {None}
          /\ tail \in nodes \union {None}
          /\ lock \subseteq Threads

\* Only one thread can be in a locked section
CS == LET locked == {"E2","E3","D3","D4","D5","D6"}
      IN \A t1,t2 \in Threads: (pc[t1] \in locked  /\ pc[t2] \in locked) => t1=t2


RECURSIVE Data(_)
Data(n) == IF n = None THEN <<>> ELSE <<vals[n]>> \o Data(prev[n])

LQ == INSTANCE LinearizableQueue WITH 
    none <- NoVal,
    up <- [t \in Threads |-> CASE t \in Producers -> pc[t] \in {"enq","E4","E5","enqdone"}
                               [] t \in Consumers -> pc[t] \in {"deq","D6", "D7","deqdone"}],
    d <- Data(head)

Refinement == LQ!Spec
    
====
