int square(int n) { return n * n; }
int add(int a, int b) { return a + b; }
int main(void) { return add(square(3), square(4)) - 20; }
