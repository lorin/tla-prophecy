/**
 * C++ implementation of queue from the Herlihy & Wing paper
 */

#include <atomic>
#include <print>
#include <random>
#include <thread>
#include <vector>

using std::atomic;
using std::printf;
using std::thread;
using std::vector;


template <typename T>
class Queue {
private:
    atomic<int> back;
    atomic<T *> *items;

public:
    Queue(int sz) : back(0), items(new atomic<T *>[sz]) {}
    ~Queue() { delete[] items; }

    void enq(T *x);
    T *deq();
        
};

template<typename T>
void Queue<T>::enq(T *x)
{
    int i = back.fetch_add(1);
    std::atomic_store(&items[i], x);
}

template<typename T>
T *Queue<T>::deq()
{
    while (true)
    {
        int range = std::atomic_load(&back);
        for (int i = 0; i < range; ++i)
        {
            T *x = std::atomic_exchange(&items[i], nullptr);
            if (x != nullptr)
            {
                return x;
            }
        }
    }
}

void produce(Queue<char> *queue, char letters[26], int n) {
    std::hash<std::thread::id> hasher;
    unsigned int id = hasher(std::this_thread::get_id()) % 100;


    unsigned seed = std::chrono::system_clock::now().time_since_epoch().count();
    std::default_random_engine generator(seed);
    std::uniform_int_distribution<int> distribution(0, 25);

    for(int i=0; i<n; ++i) {
        int offset = distribution(generator);
        printf("%02u: enq(%c)\n", id, letters[offset]);
        queue->enq(letters+offset);
        printf("%02u: enq(%c) -> OK\n", id, letters[offset]);
    }
}

void consume(Queue<char> *queue, int n) {
    std::hash<std::thread::id> hasher;
    unsigned int id = hasher(std::this_thread::get_id()) % 100;

    for(int i=0; i<n; ++i) {
        printf("%02u: deq()\n", id);
        char *c = queue->deq();
        printf("%02u: deq() -> %c\n", id, *c);
    }
}

int main() {
    int producers = 10;
    int consumers = 10;
    int max_iterations = 10;

    char letters[26];
    for (char c = 'A'; c <= 'Z'; ++c) {
        letters[c-'A']=c;
    }

    Queue<char> queue(producers*max_iterations);
    vector<thread> threads;

    for(int i=0;i<producers;++i) {
         threads.push_back(thread(produce, &queue, letters, max_iterations));
    }
    for(int i=0;i<consumers;++i) {
        threads.push_back(thread(&consume, &queue, max_iterations));
    }

    for (thread& t : threads) {
        t.join();
    }

    return 0;
}