# Herlihy & Wing: Prophecy variables in TLA+

Refinement mappings are a technique developed by Leslie Lamport to prove that a
lower-level specification faithfully implements a higher level specification.

Herlihy and Wing demonstrated that refinement mapping doesn't work in general
by providing an example implementation of a linearizable queue where no refinement
mapping exists.  Lamport and Abadi later proposed the concept of prophecy variables as a
technique to resolve the problems in refinement mapping revealed by Herlihy and Wing.

In the paper [Auxiliary Variables in TLA+][aux], Lamport and Mertz note that:

> This same idea of modifying the high-level specification to avoid adding a
> prophecy variable to the algorithm can be applied to the queue
> example of Herlihy and Wing

However, as an exercise in learning how prophecy variables work, I used prophecy variables to
define a refinement example for the queue example provided by Herlihy and Wing.

I use the [Prophecy.tla](Prophecy.tla) module presented in Lamport and Mertz,
taken from the [Disalog-ICS-NJU/tlaplus-lamport-projects][prophfile] project. 

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

## Implementing the queue in PlusCal

A PlusCal implementation of this queue is straightforward. There are some minor
modifications required because PlusCal doesn't implement pass-by-reference and
procedures don't have a notion of return values.

We can't pass the queue as an argument to the Enq and Deq procedures because
those procedures mutate the queue, and PlusCal is effectively pass-by-value,
which means that the procedure can't mutate the queue. We use a global variable
instead.

We create an `rInd` variable when a procedure or macro returns an integer
(really, Natural) value, and an `rVal` variable when a procedure or macro
returns a value from the set of `Values.


Here's the implementation, using C-syntax for previty:

```
--algorithm Rep {

variables rep = [back|->1, items|->[n \in Nat|->null]];

macro INC(x) { x := x+1 || rInd := x }
macro STORE(loc, val) { loc := val }
macro READ(ind) { rInd := ind }
macro SWAP(loc, val) { loc := val || rVal := loc }

procedure Enq(x) 
variables i, rInd {
E1:  INC(rep.back);
E2:  i := rInd;
E3:  STORE(rep.items[i], x);
E4:  return
}

procedure Deq()
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
D9:       return
        };
D10:    i:= i+1
      }
    }
}

process (p \in Producers) {
P1: with (item \in Values) {
    call Enq(item)
    }
}

process (c \in Consumers) {
C1: call Deq()
}

}
```

## Queue specification

Here's aimple specification for a FIFO: it supports enqueue and dequeueing
values:

```
EXTENDS Sequences

CONSTANT Values

VARIABLE items

Enq(val, q, qp) == qp = Append(q, val)

Deq(val, q, qp) == /\ q /= << >>
                   /\ val = Head(q)
                   /\ qp = Tail(q)
                   
                   
Init == /\ items = << >>

Next == \/ \E v \in Values : /\ Enq(v, items, items')
        \/ \E v \in Values : /\ Deq(v, items, items')
        
Spec == Init /\ [] [Next]_<<items>>
```

The challenge is to show a refinement mapping from our queue implementation to
this specification. Something that will ultimately look like this:

```
SpecP == \* The specification of the concurrent queue, with the prophecy variable
itemsBar == ... \* The refinement mapping

Q == INSTANCE Queue WITH items<-itemsBar

THEOREM SpecP => Q!Spec
```


## Prophecy variable

We need to prophecize the execution ordering of the producer and consumer
processes.

We can do this by predicting the sequence in which the processes execute
their steps.

This is an infinite sequence, where each element is a process identifier.
Using the approach outlined in the Lamport and Mertz paper, we can define
`Dom` and `Pi` as follows:

```
Dom == Nat \ {0}
Pi == ProcSet
```

In some cases, we may end up predicitng a process that has already completed.
To handle this, we'll need to add a new sub-action to our model:


```
Done(self) == /\ pc[self] = "Done"
              /\ UNCHANGED vars
```

## Refinement mapping

