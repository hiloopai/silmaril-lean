int add(int x, int y) { return x + y; }
int id(int x) { return x; }
int main(void) { return add(id(20), id(22)); }
