/**
 * C++ implementation of queue from the Herlihy & Wing paper
 */

#include <atomic>
#include <print>
#include <random>
#include <string>
#include <thread>
#include <vector>

using std::atomic;
using std::atomic_exchange;
using std::printf;
using std::string;
using std::vector;


template <typename T>
class Queue {
public:
    Queue(int sz) : back(0), items(new atomic<T *>[sz]) {}

    ~Queue() {
        delete[] items;
    }

    void enq(T *x) {
        int i = back++;
        items[i] = x;
    }

    T *deq() {
        while(true) {
            int range = back;
            for(int i=0;i<range;++i) {
                T *x = atomic_exchange(&items[i], nullptr);
                if(x != nullptr) {
                    return x;
                }
            }
        }
    }

private:
    std::atomic<int> back;
    int size;
    std::atomic<T *> *items;
};



void produce(Queue<char> *queue, char letters[26], int n) {
    unsigned seed = std::chrono::system_clock::now().time_since_epoch().count();
    std::default_random_engine generator(seed);
    std::uniform_int_distribution<int> distribution(0, 25);

    for(int i=0; i<n; ++i) {
        int offset = distribution(generator);
        printf("enq(%c)\n", letters[offset]);
        queue->enq(letters+offset);
        printf("enq(%c) -> OK\n", letters[offset]);
    }
}

void consume(Queue<char> *queue, int n) {
    for(int i=0; i<n; ++i) {
        printf("deq()\n");
        char *c = queue->deq();
        printf("deq() -> %c\n", *c);
    }
}

int main() {
    int producers = 3;
    int consumers = 3;
    int max_iterations = 5;

    char letters[26];
    for (char c = 'A'; c <= 'Z'; ++c) {
        letters[c-'A']=c;
    }

    Queue<char> queue(producers*max_iterations);

    produce(&queue, letters, 2);
    consume(&queue, 2);

    return 0;
}