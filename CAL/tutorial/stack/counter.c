#define MAX_COUNTER ((unsigned int) 10)

static unsigned int COUNTER = 0;

unsigned int get_counter() {
    return COUNTER;
}

unsigned int incr_counter() {
    if (COUNTER < MAX_COUNTER) {
        COUNTER = COUNTER + 1;
        return COUNTER;
    }
    else { /* Error */
        return MAX_COUNTER + 1;
    }
}

unsigned int decr_counter() {
    if (0 < COUNTER) {
        COUNTER = COUNTER - 1;
        return COUNTER;
    }
    else { /* Error */
        return MAX_COUNTER + 1;
    }
}
