#!/usr/bin/env python3
"""

A linearizable queue

"""

from threading import Thread, Lock

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
            tail.prev = new_tail
        self.tail = new_tail
        self.lock.release()

    def dequeue(self):
        while True:
            self.lock.acquire()
            if self.is_empty():
                self.lock.release()
                continue
            val = self.head.val
            self.head = self.head.prev
            if self.head is None:
                self.tail = None
            else:
                head.next = None
            self.lock.release()
            return val
