int main(void) {
  int s = 0;
  int i = 0;
  while (i < 5) {
    if (i % 2 == 0) s = s + i;
    i = i + 1;
  }
  return s;
}
