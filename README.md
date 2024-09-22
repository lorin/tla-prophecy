# Reading the Herlihy & Wing Linearizability paper with TLA+, part 2: Prophecy variables

See also [Reading the Herlihy & Wing Linearizability paper with TLA+: Part 1][part-1].

[part-1]: https://github.com/lorin/tla-linearizability

Martin Abadi and Leslie Lamport proposed [refinement mappings] in 1988 as a technique
for proving that a lower-level specification implements a higher-level
specification.

[refinement mappings]: https://www.microsoft.com/en-us/research/publication/the-existence-of-refinement-mappings/

Two years later, in their paper that introduced the concept of [linearizability][herlihy], Herlihy and Wing
provided an example of a linearizable, concurrent queue implementation where
refinement mapping didn't work: it wasn't possible to define a refinement
mapping that proved that the concurrent queue implemented the higher-level
specification of a sequential queue.

[herlihy]: https://cs.brown.edu/~mph/HerlihyW90/p463-herlihy.pdf

Lamport and Abadi later proposed the idea of *prophecy variables*  as a
technique to resolve the problems in refinement mapping revealed by Herlihy and Wing.
Prophecy variables are described in:

* [A science of concurrent programs][science] by Lamport
* [Prophecy Made Simple][simple] by Lamport and Merz
* [Auxiliary Variables in TLA+][aux] by Lamport and Merz

[science]: https://lamport.azurewebsites.net/tla/science.pdf

As it happens, Lamport and Merz note that prophecy variables aren't actually
necessary for defining a refinement mapping for the example provided by Herlihy
and Wing, provided changes are made to the high-level specification:

> This same idea of modifying the high-level specification to avoid adding a
> prophecy variable to the algorithm can be applied to the queue
> example of Herlihy and Wing

However, as an exercise in learning how prophecy variables work, I used prophecy variables to
define a refinement example for the queue example provided by Herlihy and Wing.

[aux]:  http://lamport.azurewebsites.net/pubs/pubs.html#auxiliary
[simple]: https://lamport.azurewebsites.net/pubs/pubs.html#simple

## Concurrent queue from Herlihy & Wing paper

The Herlihy & Wing paper provides an example implementation of a concurrent
queue that is linearizable, and yet, does not admit a refinement mapping
to a sequential queue.

Here's the algorithm from Section 4.2 (p475), using the pseudocode syntax
from the original paper:

```
Enq = proc (q: queue, x: item)
    i: int := INC(q.back) % Allocate a new slot.
    STORE (q.items[i], x) % Fill it.
    end Enq

Deq = proc (q: queue) returns (item)
    while true do
        range: int := READ(q.back) -1
        for i: int in 1 .. range do
            x : item := SWAP(q.items[i], null)
            if x ~= null then return(x) end
            end
        end
    end Deq
```

The queue is represented as a record:

```tla
rep = record [back: int, items: array [item]] 
```

The syntax assumes pass-by-reference, so that the `q` variable can be modified.

The algorithm assumes the presence of the following atomic operations

`INC(x)` atomically increments x and returns the value before incrementing
(works like `x++` in C++ assuming x was passed by reference)

`STORE(var, val)` atomically stores the value `val` into the variable `var`.

`READ(x)` simply returns the value of `x`

`SWAP(x,y)` sets `x` to `y` and returns the value of `x` before being set.

Note that the enqueue operation (`Enq`) is implemented as a sequence of two
atomic operations: `INC` and `STORE`.

Also note that the implementation is non-blocking: there are no locks, mutexes,
critical sections, or other concurrency primitives provided by the system,
other than the atomic `INC`, `STORE`, `READ` and `SWAP` operations.


## Implementing the queue in PlusCal

Translating from the pseudocode to PlusCal is pretty straightforward. 

### The queue

The queue is modeled as a record:

```
q = [back|->1, items|->[n \in 1..Nmax|->null]];
```

### Enq operation

Recall that the enqueue operation from the paper looks like this:

```
Enq = proc (q: queue, x: item)
    i: int := INC(q.back) % Allocate a new slot.
    STORE (q.items[i], x) % Fill it.
    end Enq
```


I needed to model `INC` and `STORE` as atomic operations. In TLA+, an atomic operation is one where there's a single label.
The `||` operator means that the operations happen in parallel, which is a handy way to implement the equivalent of `i = x++`:


```tla
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
```


### Deq operation

Hre's the pseudocode from the paper:

```
Deq = proc (q: queue) returns (item)
    while true do
        range: int := READ(q.back) -1
        for i: int in 1 .. range do
            x : item := SWAP(q.items[i], null)
            if x ~= null then return(x) end
            end
        end
    end Deq
```

And here's my implementation. I used the `rval` variable to hold the return value of the Deq operation.


```tla
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
```

The full spec can be found in [QueueRep.tla](QueueRep.tla)

## Refinement mappings

In Chapter 6 of [A science of concurrent programs][science], Lamport describes a
linearizable queue specification (IFifo) and a more general specification
(IPOFifo) that captures the behavior of the Herlihy & Wing queue, but at a
higher level of abstraction than the pseudocode. Lamport also sketches how to
augment POFifo with history and prophecy variables in order to define a refinement mapping from IPOFifo to IFifo.

This repo contains multiple TLA+ specs, including:

* [Fifo.tla](Fifo.tla) - Lamport's IFifo spec from [A science of concurrent programs][science]
* [POFifo.tla](POFifo.tla) - Lamport's IPOFifo spec [A science of concurrent programs][science]
* [POFifop.tla](POFifop.tla) - Lamports' IPOFifo spec augmented with a prophecy variable, as sketched in [A science of concurrent programs][science]
* [POFifopq.tla](POFifopq.tla) - Lamports' IPOFifo spec augmented with a prophecy variable and history variables to support a refinement mapping to Fifo.tla, as sketched in [A science of concurrent programs][science] . Also contains the refinement maping.
* [HWQueue.tla](HWQueue.tla) - a PlusCal model of the Herlihy & Wing queue
* [HWQueueIds.tla](HWQueueIds.tla) - the HWQueue model augmented with history variables to support a refinement mapping to POFifo, as well as the refinement mapping.


