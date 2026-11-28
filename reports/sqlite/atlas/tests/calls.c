typedef int (*Fn)(void);
struct Methods { Fn read; };
static int a(void) { return 1; }
static int b(void) { return 2; }
static Fn factory(void) { return a; }

int calls(Fn local, struct Methods *methods, int choose) {
    return a() + (a)() + (*a)() + (&a)() + ((Fn)a)() + local()
         + methods->read() + (choose ? a : b)() + factory()();
}
