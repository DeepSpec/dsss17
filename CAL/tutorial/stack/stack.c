#define MAX_COUNTER ((unsigned int) 10)

extern unsigned int get_counter(void);
extern unsigned int incr_counter(void);
extern unsigned int decr_counter(void);

static int STACK[MAX_COUNTER];

unsigned int get_size() {
    return get_counter();
}

void push(int x) {
    unsigned int idx = get_counter();
    incr_counter(); // Will be an error if stack is full
    STACK[idx] = x;
}

int pop() {
    unsigned int idx = decr_counter(); // Will be an error if stack is empty
    return STACK[idx];
}
