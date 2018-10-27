# Prophecy variables in TLA+

Refinement mappings are a technique developed by Leslie Lamport to prove that a
lower-level specification faithfully implements a higher level specification.

Herlihy and Wing demonstrated that refinement mapping doesn't work in general.
Lamport and Abadi later proposed the concept of prophecy variables as a
technique to resolve the problems in refinement mapping revealed by Herlihy and Wing.

This repo illustrates the use of prophecy variables for the specific counterexample
that Herlihy and Wing used to illustrate the problems with refinement mappings.

I wrote this as a personal motivation to learn how to use prophecy variables in
refinement mappings.


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


