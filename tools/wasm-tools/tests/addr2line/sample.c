/* A C sample for the addr2line differential test. */
static int square(int x) { return x * x; }

static inline int sum_squares(int n) {
  int s = 0;
  for (int i = 0; i < n; i++) s += square(i);
  return s;
}

int entry(int n) { return sum_squares(n) + square(n); }
