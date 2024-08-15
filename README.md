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
Prophecy variables are described in detail in the paper [Auxiliary Variables in TLA+][aux]
by Lamport and Mertz.

As it happens, Lamport and Mertz note that prophecy variables aren't actually
necessary for defining a refinement mapping for the example provided by Herlihy
and Wing, provided changes are made to the high-level specification:

> This same idea of modifying the high-level specification to avoid adding a
> prophecy variable to the algorithm can be applied to the queue
> example of Herlihy and Wing

However, as an exercise in learning how prophecy variables work, I used prophecy variables to
define a refinement example for the queue example provided by Herlihy and Wing.

The [Prophecy.tla](Prophecy.tla) module comes from the [zipfile] that
accompanies the Lamport and Merz paper.

[zipfile]: http://lamport.azurewebsites.net/tla/auxiliary/auxiliary.html
[aux]:  http://lamport.azurewebsites.net/pubs/pubs.html#auxiliary

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

```
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
variables rep = [back|->1, items|->[n \in 1..Nmax|->null]];
```

### Enq operation

Recall that the enqueue operation from the paper looks like this:

```
Enq = proc (q: queue, x: item)
    i: int := INC(q.back) % Allocate a new slot.
    STORE (q.items[i], x) % Fill it.
    end Enq
```

I needed to model `INC` and `STORE` as atomic operations, so I used TLA+ macros for those:

```
macro INC(x) { x := x+1 || preINC := x }
macro STORE(loc, val) { loc := val }
```

The `STORE` operation is pretty trivial, but the `INC` requires a little more explanation. 
Because TLA+ macros don't have a concept of returning a value, I use a variable called `preINC` that gets
set to the value that `x` held before incremented.

The PlusCal implementation for enqueue then looks like this:

```
\*
\* Enq(item)
\*
process (producer \in Producers) 
variables
    item \in Val, 
    i, preINC; {

E1:  INC(rep.back);
     i := preINC;
E2:  STORE(rep.items[i], item);

}
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

And here's my implementation. I used the `rVal` variable to hold the return value of the Deq operation,
and the `rInd` variable to hold the return value of the `READ` operation.


```
macro READ(ind) { rInd := ind }
macro SWAP(loc, val) { loc := val || rVal := loc }

\*
\* Deq() -> rVal
\*
process (consumer \in Consumers) 
variables i, x, range, rInd, rVal {
D1: while(TRUE) {
D2:   READ(rep.back);
D3:   range := rInd-1;
D4:   i := 1;
D5:   while(i<=range) {
D6:     SWAP(rep.items[i], null);
D7:     x := rVal;
        if(x /= null) {
D8:       rVal := x;
          p := Tail(p);
D9:       goto "Done"
        };
D10:    i:= i+1
      }
    }
}
```

The full spec can be found in [QueueRep.tla](QueueRep.tla)


## High-level queue specification

Here's simple specification for a queue. It models a set of producer and consumer
processes, where a producer enqueues an item onto the queue, and the consumer dequeues an item,
blocking if the queue is empty.

```
EXTENDS Sequences, Naturals

CONSTANTS Val, null, Producers, Consumers

ASSUME null \notin Val

(*
--algorithm Queue {
    variable items = << >>

    process (producer \in Producers)
    variable x \in Val;
    {
      E: 
          items := <<x>> \o items;
    }

    process (consumer \in Consumers) 
    variable r = null;
    {
        D:
            await items # <<>>;
            r := Head(items);
            items := Tail(items);
    }
}
*)
```

## Refinement mapping

The challenge is to show a refinement mapping from our queue implementation to
this specification. 

The interesting part of the queue implementation is that enqueuing requires two operations:

* allocating a slot for writing (E1)
* writing the data (E2)

We need to decide at which point the enqueueing should take effect. But we
can't know this, because it will vary depending on how the other processes get
scheduled. The paper provides a good example on how it's not possible to choose
a single refinement mapping because whatever you pick, there is a potential
execution trace that will render the refinement mapping invalid.

Herlihy and Wing propose using a set of potential mappings rather than a single
mapping. We implement their abstraction function in
[QueueAbs.tla](QueueAbs.tla) but we don't actually use this function since we
use prophecy variables instead.

## Prophecy variable

We can use prophecy variables to predict the order in which values will get dequeued.

