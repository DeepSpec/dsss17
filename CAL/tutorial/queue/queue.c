#define MAX_NODES 1024

extern void init_node(unsigned int node, unsigned int data);
extern unsigned int get_next(unsigned int node);
extern unsigned int get_prev(unsigned int node);
extern void set_next(unsigned int node, unsigned int nxt);
extern void set_prev(unsigned int node, unsigned int prv);

extern void init_queue(void);
extern unsigned int get_head(void);
extern unsigned int get_tail(void);
extern void set_head(unsigned int hd);
extern void set_tail(unsigned int tl);

void enqueue(unsigned int node) {
    unsigned int tail;

    tail = get_tail();

    if (tail == MAX_NODES) {
        set_next(node, MAX_NODES);
        set_prev(node, MAX_NODES);
        set_head(node);
        set_tail(node);
    } else {
        set_next(tail, node);
        set_prev(node, tail);
        set_next(node, MAX_NODES);
        set_tail(node);
    }
}

unsigned int dequeue() {
    unsigned int head;
    unsigned int next;
    unsigned int node;

    node = MAX_NODES;
    head = get_head();

    if (head != MAX_NODES) {
        node = head;
        next = get_next(head);

        if (next == MAX_NODES) {
            set_head(MAX_NODES);
            set_tail(MAX_NODES);
        } else {
            set_prev(next, MAX_NODES);
            set_head(next);
        }

        set_next(node, MAX_NODES);
        set_prev(node, MAX_NODES);
    }

    return node;
}
