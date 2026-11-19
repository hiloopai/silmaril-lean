/* Undefined behaviour (C11 6.5p5): signed overflow in the returned expression. */
int main(void) { return 2147483647 + 1; }
