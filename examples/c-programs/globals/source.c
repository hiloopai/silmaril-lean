int counter = 3;
int bump(void) { counter = counter + 1; return counter; }
int main(void) { bump(); bump(); return counter; }
