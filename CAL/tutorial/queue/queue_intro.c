#define MAX_NODES 1024

struct queue_t {
    unsigned int head;
    unsigned int tail;
};

static struct queue_t QUEUE;

void init_queue() {
    QUEUE.head = MAX_NODES;
    QUEUE.tail = MAX_NODES;
}

unsigned int get_head() {
    return QUEUE.head;
}

unsigned int get_tail() {
    return QUEUE.tail;
}

void set_head(unsigned int hd) {
    QUEUE.head = hd;
}

void set_tail(unsigned int tl) {
    QUEUE.tail = tl;
}
