#!/usr/bin/env python3
"""

A linearizable queue

"""

import random
import time

from threading import Thread, Lock, current_thread

class Node:
    def __init__(self, val, next=None, prev=None):
        self.val = val
        self.next = next
        self.prev = prev

class Queue:
    def __init__(self):
        self.lock = Lock()
        self.head = None
        self.tail = None

    def is_empty(self):
        return self.head is None

    def enqueue(self, val):
        self.lock.acquire()
        new_tail = Node(val=val, next=self.tail)
        if self.is_empty():
            self.head = new_tail
        else:
            self.tail.prev = new_tail
        self.tail = new_tail
        self.lock.release()

    def dequeue(self):
        empty = True
        while empty:
            self.lock.acquire()
            if self.is_empty():
                self.lock.release()
            else:
                empty = False
        val = self.head.val
        self.head = self.head.prev
        if self.head is None:
            self.tail = None
        else:
            self.head.next = None
        self.lock.release()
        return val

def producer(q: Queue, n: int, vals: list[str]):
    time.sleep(random.random())
    tid = current_thread().ident % 100
    for i in range(n):
        x = random.choice(vals)
        print(f"{tid}: enq({x})")
        q.enqueue(x)
        print(f"{tid}: enq() -> ok")


def consumer(q: Queue, n: int):
    time.sleep(random.random())
    tid = current_thread().ident % 100
    for i in range(n):
        print(f"{tid}: deq()")
        x = q.dequeue()
        print(f"{tid}: deq() -> {x}")


def main():
    q = Queue()
    num_producers = 3
    num_consumers = 3
    threads = []
    for i in range(num_producers):
        threads.append(Thread(target=producer,args=[q, 5, ["A", "B", "C"]]))
    for i in range(num_consumers):
        threads.append(Thread(target=consumer,args=[q, 5]))
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join()

main()


