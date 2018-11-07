# Prophecy variables in TLA+

**Note: work in progress**

Refinement mappings are a technique developed by Leslie Lamport to prove that a
lower-level specification faithfully implements a higher level specification.

Herlihy and Wing demonstrated that refinement mapping doesn't work in general.
Lamport and Abadi later proposed the concept of prophecy variables as a
technique to resolve the problems in refinement mapping revealed by Herlihy and Wing.

In order to learn how prophecy variables work, I used prophecy variables to
define a refinement example for the specific example provided by Herlihy and Wing.

I found the [Prophecy.tla](Prophecy.tla) module from
at [Disalog-ICS-NJU/tlaplus-lamport-projects][prophfile] project. 
This module is documented in the paper [Auxiliary Variables in TLA+][aux] by Lamport and Mertz.

[prophfile]: https://github.com/Disalg-ICS-NJU/tlaplus-lamport-projects/blob/master/learning-tlaplus/Hengfeng-Wei/learning-tlaplus-papers/AuxiliaryVariables-Lamport/auxiliary/Prophecy.tla
[aux]:  http://lamport.azurewebsites.net/pubs/pubs.html#auxiliary

## Queue from Herlihy & Wing paper

From Section 4.2, page 475, here is the algorithm, using the pseudocode syntax
from the original paper

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

The syntax assumes pass-by-reference, so that variables passed as arguments
can be mutated.

The algorithm assumes the presence of the following atomic operations

`INC(x)` atomically increments x and returns the value before incrementing
(works like `x++` in C++ assuming x was passed by reference)

`STORE(var, val)` atomically stores the value `val` into the variable `var`.

`READ(x)` simply returns the value of `x`

`SWAP(x,y)` sets `x` to `y` and returns the value of `x` before being set.

## Prophecizing

We need to prophecize the execution ordering of the producer and consumer
processes.

We can predict the sequence 
