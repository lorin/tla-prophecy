# Prophecy variables in TLA+

**Note: work in progress**

Refinement mappings are a technique developed by Leslie Lamport to prove that a
lower-level specification faithfully implements a higher level specification.

Herlihy and Wing demonstrated that refinement mapping doesn't work in general.
Lamport and Abadi later proposed the concept of prophecy variables as a
technique to resolve the problems in refinement mapping revealed by Herlihy and Wing.

In order to learn how prophecy variables work, I used prophecy variables to
define a refinement example for the specific example provided by Herlihy and Wing.

## Queue from Herlihy & Wing paper

We need to prophecize the execution ordering of the producer and consumer
processes.

