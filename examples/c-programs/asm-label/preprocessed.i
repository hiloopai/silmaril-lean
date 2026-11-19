int renamed(void) __asm__("actual_symbol");
int renamed(void) { return 7; }
int main(void) { return renamed(); }
