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
    

        




