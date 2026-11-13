/* A straight-line leaf: declarations with initializers, then a return. */
int add3(int a, int b, int c)
{
  int s = a + b;
  int t = s + c;
  return t;
}
