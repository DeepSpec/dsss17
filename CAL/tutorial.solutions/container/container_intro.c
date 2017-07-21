#define NUM_ID 1024
#define MAX_CHILDREN 8

struct container {
    unsigned int quota;
    unsigned int usage;
    unsigned int parent;
    unsigned int nchildren;
    unsigned int used;
};

static struct container CONTAINER_POOL[NUM_ID];

void container_node_init(unsigned int id, unsigned int quota, unsigned int parent) {
    CONTAINER_POOL[id].quota = quota;
    CONTAINER_POOL[id].usage = 0;
    CONTAINER_POOL[id].parent = parent;
    CONTAINER_POOL[id].nchildren = 0;
    CONTAINER_POOL[id].used = 1;
}

unsigned int container_get_quota(unsigned int id) {
    return CONTAINER_POOL[id].quota;
}

unsigned int container_get_usage(unsigned int id) {
    return CONTAINER_POOL[id].usage;
}

unsigned int container_get_parent(unsigned int id) {
    return CONTAINER_POOL[id].parent;
}

unsigned int container_get_nchildren(unsigned int id) {
    return CONTAINER_POOL[id].nchildren;
}

void container_set_usage(unsigned int id, unsigned int usage) {
    CONTAINER_POOL[id].usage = usage;
}

void container_set_nchildren(unsigned int id, unsigned int next_child) {
    CONTAINER_POOL[id].nchildren += 1;
}
