# Reading the Herlihy & Wing Linearizability paper with TLA+, part 2: Prophecy variables

See also [Reading the Herlihy & Wing Linearizability paper with TLA+: Part 1][part-1].

[part-1]: https://github.com/lorin/tla-linearizability

Martin Abadi and Leslie Lamport proposed [refinement mappings] in 1988 as a technique
for proving that a lower-level specification implements a higher-level
specification.

[refinement mappings]: https://www.microsoft.com/en-us/research/publication/the-existence-of-refinement-mappings/

Two years later, in their [landmark paper on linearizability][herlihy], Herlihy and Wing
provided an example of a particular concurrent queue implementation that
demonstrated that it is not always possible to define a refinement mapping. 

[herlihy]: https://cs.brown.edu/~mph/HerlihyW90/p463-herlihy.pdf


Lamport and Abadi later proposed the concept of prophecy variables (a form of
which is described in the paper [Auxiliary Variables in TLA+][aux]) as a
technique to resolve the problems in refinement mapping revealed by Herlihy and Wing.

As it happens, Lamport and Mertz note that prophecy variables aren't actually
necessary for defining a refinement mapping for the example provided by Herlihy
and Wing, as long as you make some changes to the high-level specification:

> This same idea of modifying the high-level specification to avoid adding a
> prophecy variable to the algorithm can be applied to the queue
> example of Herlihy and Wing

However, as an exercise in learning how prophecy variables work, I used prophecy variables to
define a refinement example for the queue example provided by Herlihy and Wing.

I use the [Prophecy.tla](Prophecy.tla) module from the
[Disalog-ICS-NJU/tlaplus-lamport-projects][prophfile] project. This module was
originally documented in the Lamport and Abadi paper.

[prophfile]: https://github.com/Disalg-ICS-NJU/tlaplus-lamport-projects/blob/master/learning-tlaplus/Hengfeng-Wei/learning-tlaplus-papers/AuxiliaryVariables-Lamport/auxiliary/Prophecy.tla
[aux]:  http://lamport.azurewebsites.net/pubs/pubs.html#auxiliary

## Concurrent queue from Herlihy & Wing paper

The Herlihy & Wing paper provides an example implementation of a concurrent
queue that is linearizable.

Here is the algorithm, from Section 4.2, page 475, using the pseudocode syntax
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

PlusCal does not allow macros or procedures to return values, so we use
variables for storing returend values. For the `Enq` procedure, we use the
variable `preINC` to store the value of `INC(x)` before it is incremented.
For the `Deq` proedure, we use the the `rInd` variable when a procedure or macro returns
a natural number (here "Ind" stands for index) value, and an `rVal` variable
when a procedure or macro returns a value from the set of `Values`.


Here's a PlusCal implementation, which can be found in
[QueueRep.tla](QueueRep.tla).

```
--algorithm Rep {

variables rep = [back|->1, items|->[n \in 1..Nmax|->null]];

macro INC(x) { x := x+1 || preINC := x }
macro STORE(loc, val) { loc := val }
macro READ(ind) { rInd := ind }
macro SWAP(loc, val) { loc := val || rVal := loc }

procedure Enq(x)
variables i, preINC {
E1:  INC(rep.back);
     i := preINC;
E2:  STORE(rep.items[i], x);
E3:  return
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

process (producer \in Producers) {
P1: with (item \in Values) {
    call Enq(item)
    }
}

process (consumer \in Consumers) {
C1: call Deq()
}
}
```


## High-level queue specification

Here's simple specification for a FIFO: it supports enqueue and dequeueing
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

## Refinement mapping

The challenge is to show a refinement mapping from our queue implementation to
this specification. Something that will ultimately look like this:

```
SpecP == \* The specification of the concurrent queue, with the prophecy variable
itemsBar == ... \* The refinement mapping

Q == INSTANCE Queue WITH items<-itemsBar

THEOREM SpecP => Q!Spec
```

The interesting part of the queue implementation is that enqueuing requires two operations:

* allocating a slot for writing (E1)
* writing the data (E3)

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

One way to get around the problem that Herlihy and Wing point out is to predict
in advance the order in which the processes will get scheduled. Once you know
that, then you can decide whether enqueues should take effect at label E1 or
E3.

We can do this by choosing as our prophecy variable a sequence of process
identifiers. Using the approach outlined in the Lamport and Mertz paper, we can define
`Dom` and `Pi` as follows.

```
Dom == Nat \ {0}
Pi == ProcSet
```

`[Dom->Pi]` defines the set of all possible schedulings.

In some cases, we may end up predicitng a process that has already completed.
To handle this, we'll need to add a new sub-action to our model:


```
Done(self) == /\ pc[self] = "Done"
              /\ UNCHANGED vars
```

Following Lamport and Mertz, for each sub-action in our low-level specification
we need to define three operators:

* *Pred* operator that uses the prophecy variable to make a prediction
* *PredDom* set that indicates which prophecy variables get discarded after a
  step executes
* *DomInj* operator for ensuring that the prophecy values don't change in
  successive states.

In general, these operators can be different for each subaction in a
specification. In our case, they are the same for every subaction. They are
defined in [QueueRepPP.tla](QueueRepPP.tla):

```
Dom == Nat \ {0}
Pi == ProcSet

INSTANCE Prophecy WITH DomPrime<-Dom'

DomInj == [j \in Nat \ {0,1} |-> j-1]
PredDom == {1}
Pred(p, process) == p[1] = process
```

Lamport and Mertz recommend checking that the prophecy does not restrict any
behaviors that would normally be permitted by the specification.

We can check this by specifying this condition:

```
Condition ==
    /\ \A pr \in Producers: ProphCondition(E1(pr), DomInj, PredDom, LAMBDA p: Pred(p, pr))
    /\ \A pr \in Producers: ProphCondition(E2(pr), DomInj, PredDom, LAMBDA p: Pred(p, pr))
    /\ \A pr \in Producers: ProphCondition(E3(pr), DomInj, PredDom, LAMBDA p: Pred(p, pr))
    /\ \A co \in Consumers: ProphCondition(D1(co), DomInj, PredDom, LAMBDA p: Pred(p, co))
    /\ \A co \in Consumers: ProphCondition(D2(co), DomInj, PredDom, LAMBDA p: Pred(p, co))
    /\ \A co \in Consumers: ProphCondition(D3(co), DomInj, PredDom, LAMBDA p: Pred(p, co))
    /\ \A co \in Consumers: ProphCondition(D4(co), DomInj, PredDom, LAMBDA p: Pred(p, co))
    /\ \A co \in Consumers: ProphCondition(D5(co), DomInj, PredDom, LAMBDA p: Pred(p, co))
    /\ \A co \in Consumers: ProphCondition(D6(co), DomInj, PredDom, LAMBDA p: Pred(p, co))
    /\ \A co \in Consumers: ProphCondition(D7(co), DomInj, PredDom, LAMBDA p: Pred(p, co))
    /\ \A co \in Consumers: ProphCondition(D8(co), DomInj, PredDom, LAMBDA p: Pred(p, co))
    /\ \A co \in Consumers: ProphCondition(D9(co), DomInj, PredDom, LAMBDA p: Pred(p, co))
    /\ \A co \in Consumers: ProphCondition(D10(co), DomInj, PredDom, LAMBDA p: Pred(p, co))
```

And then using TLC to check this:

```
THEOREM Spec => [][Condition]_vars
```

We do this by specifying `Spec` as the temporal formula and `[][Condition]_vars` as a property to check.

## Using prophecy to do refinement mapping


The [QueueRepP.tla](QueueRepP.tla) file contains the specification which creates
a new spec, SpecP, that uses the prophecy variable to do the refinement
mapping.


The most complicated part is the `Orderings` operator. This is an operator
which takes the prophecy variable, and determines the order in which the
producer process's values will be dequeued by effectively executing
(simulating) the specification using the prophecized schedule.

This ordering is stored in the `ordP` variable, which is then used to determine
whether enqueues should take effect at E1 or E2.
