int g = 0;
int f(void) { g = g * 10 + 1; return 0; }
int h(void) { g = g * 10 + 2; return 0; }
int main(void) { int r = f() + h(); return g + r; }
