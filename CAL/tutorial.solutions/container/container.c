#define PAGE_SIZE 4096
#define VM_USERLO 0x40000000
#define VM_USERHI 0xF0000000
#define MAX_CHILDREN 8

extern void boot_init(void);
extern void container_node_init(unsigned int id, unsigned int quota, unsigned int parent);
extern unsigned int container_get_quota(unsigned int id);
extern unsigned int container_get_usage(unsigned int id);
extern unsigned int container_get_parent(unsigned int id);
extern unsigned int container_get_nchildren(unsigned int id);
extern void container_set_usage(unsigned int id, unsigned int usage);
extern void container_set_nchildren(unsigned int id, unsigned int nchildren);

void container_init() {
    boot_init();
    container_node_init(0, (VM_USERHI - VM_USERLO) / PAGE_SIZE, 0);
}

unsigned int container_can_consume(unsigned int id, unsigned int n) {
    unsigned int quota = container_get_quota(id);
    unsigned int usage = container_get_usage(id);

    if (n <= quota && usage <= quota - n) {
        return 1;
    }
    else {
        return 0;
    }
}

unsigned int container_alloc(unsigned int id) {
    unsigned int quota = container_get_quota(id);
    unsigned int usage = container_get_usage(id);

    if (usage < quota) {
        container_set_usage(id, usage + 1);
        return 1;
    }
    else {
        return 0;
    }
}

unsigned int container_split(unsigned int id, unsigned int quota) {
    unsigned int nchildren = container_get_nchildren(id);
    unsigned int usage = container_get_usage(id);
    unsigned int child_id = id * MAX_CHILDREN + 1 + nchildren;

    container_node_init(child_id, quota, id);
    container_set_usage(id, usage + quota);
    container_set_nchildren(id, child_id);

    return child_id;
}
