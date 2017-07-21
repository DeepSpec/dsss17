#define MAX_NODES 1024

struct node_t {
    unsigned int data;
    unsigned int next;
    unsigned int prev;
};

static struct node_t NODE_POOL[MAX_NODES];

void init_node(unsigned int node, unsigned int data) {
    NODE_POOL[node].data = data;
    NODE_POOL[node].next = MAX_NODES;
    NODE_POOL[node].prev = MAX_NODES;
}

unsigned int get_next(unsigned int node) {
    return NODE_POOL[node].next;
}

unsigned int get_prev(unsigned int node) {
    return NODE_POOL[node].prev;
}

void set_next(unsigned int node, unsigned nxt) {
    NODE_POOL[node].next = nxt;
}

void set_prev(unsigned int node, unsigned prv) {
    NODE_POOL[node].prev = prv;
}
