int main(void) {
  int a[3] = {1, 2, 3};
  int *p = a;
  p = p + 2;
  return *p;
}
