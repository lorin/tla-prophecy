"""
Python implementation of the queue from Herlihy & Wing paper on linearizability.

Assumes that each line is executed atomically, which is not actually true for Python.

Original code:

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

"""
class Queue:
    def __init__(q, Nmax=100):
        q.back = 0
        q.items = [None] * Nmax

    def enq(q, x):
        i, q.back = q.back, q.back+1
        q.items[i] = x

    def deq(q):        
        while True:
            rng = q.back
            for i in range(rng):
                x, q.items[i] = q.items[i], None
                if x is not None: return x
