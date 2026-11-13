/* A leaf with a loop. */
int sum_to(int n)
{
  int s = 0;
  int i = 0;
  while (i < n) {
    i = i + 1;
    s = s + i;
  }
  return s;
}
