# Prophecy variables in TLA+

Refinement mappings are a technique developed by Leslie Lamport to prove that a
lower-level specification faithfully implements a higher level specification.

Herlihy and Wing demonstrated that refinement mapping doesn't work in general.
Lamport and Abadi later proposed the concept of prophecy variables as a
technique to resolve the problems in refinement mapping revealed by Herlihy and Wing.

In order to learn how prophecy variables work, I used prophecy variables to
define a refinement example for the specific example provided by Herlihy and Wing.

## Queue from Herlihy & Wing paper

We need to prophecize the order that the producer processes will enqueue.

### Prophecy data structure 

Will use a prophecy data structure that looks like this:

```
[ord|-> <<1,2>>, toEnc: <<2>>, toDec: <<1,2>>]
```

The `ord` field encodes the ordering in which the producers values will be
enqueued from the perspective of the refinement.

The `toEnq` field encodes the processes whose values have yet to be
recorded as enqueued in the refinement.


The `toDeq` field encodes the processes whose values have yet to be
recorded as enqueued in the refinement.

### When prophecy will be used

There are three places where we need to take the prophecy variables into
account when determining whether a process is allowed to advance

#### When to "add" to the abstract queue

We need to decide at what point in time a value gets enqueued in the refinement
mapping.

There are two possible points where this an happen:

* `E1: INC(rep.back)`
* `E3: STORE(rep.items[j], x);`

#### Can a producer wrote to rep.items?

A prophecy may prevent this step from being enabled.

```
E3: STORE(rep.items[j], x);
```

### Can a consumer read 

A prophecy may prevent this step from being enabled.

```
D6: SWAP(rep.items[i], null);

```
