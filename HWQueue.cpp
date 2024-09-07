/**
 * C++ implementation of queue from the Herlihy & Wing paper
 * 
 * Outputs data in format that can be parsed by https://github.com/thisismiller/dbdiag
 * See: https://transactional.blog/blog/2022-dbdiag-ophistory
 */

#include <atomic>
#include <cassert>
#include <print>
#include <random>
#include <thread>
#include <vector>

using std::atomic;
using std::printf;
using std::this_thread::get_id;
using std::this_thread::yield;
using std::thread;
using std::vector;


template <typename T>
class Queue {
    atomic<int> back;
    atomic<T *> *items;

public:
    Queue(int sz) : back(0), items(new atomic<T *>[sz]) {}
    ~Queue() { delete[] items; }

    void enq(T *x);
    T *deq();
        
};

template<typename T>
void Queue<T>::enq(T *x) {
    int i = back++;
    items[i] = x;
}

template<typename T>
T *Queue<T>::deq() {
    while (true) {
        int range = back;
        for (int i = 0; i < range; ++i) {
            T *x = std::atomic_exchange(&items[i], nullptr);
            if (x != nullptr) {
                return x;
            }
        }
    }
}

void produce(Queue<char> *queue, char letters[26], int n) {
    std::hash<thread::id> hasher;
    unsigned int id = hasher(get_id()) % 100;


    unsigned seed = std::chrono::system_clock::now().time_since_epoch().count();
    std::default_random_engine generator(seed);
    std::uniform_int_distribution<int> distribution(0, 25);
    char *c;

    for(int i=0; i<n; ++i) {
        int offset = distribution(generator);
        printf("%02u: enq(%c) a\n", id, letters[offset]);
        c = letters + offset;
        queue->enq(c);
        printf("%02u: END a\n", id);
    }
}

void consume(Queue<char> *queue, int n) {
    std::hash<thread::id> hasher;
    unsigned int id = hasher(get_id()) % 100;

    for(int i=0; i<n; ++i) {
                                        yield();
        printf("%02u: deq() a\n", id);  yield();
        char *c = queue->deq();         yield();
        printf("%02u: %c a\n", id, *c); yield();
    }
}

void join_all(vector<thread> &threads) {
    for(auto& t : threads ) {
        t.join();
    }
}

char letters[26]; // defined globally so it never goes out of scope

void start_producers(Queue<char> *queue, int n, int max_iterations) {
    for (char c = 'A'; c <= 'Z'; ++c) {
        letters[c-'A']=c;
    }

    vector<thread> threads;
    for(int i=0;i<n;++i) {
         threads.push_back(thread(produce, queue, letters, max_iterations));
    }

    join_all(threads);
}

void start_consumers(Queue<char> *queue, int n, int max_iterations) {
    vector<thread> threads;
    for(int i=0;i<n;++i) {
         threads.push_back(thread(consume, queue, max_iterations));
    }

    join_all(threads);
}

int main() {
    int producers = 3;
    int consumers = 3;
    int max_iterations = 3;
    Queue<char> queue(producers*max_iterations);

    thread tp = thread(start_producers, &queue, producers, max_iterations);
    thread tc = thread(start_consumers, &queue, consumers, max_iterations);

    tp.join();
    tc.join();

    return 0;
}