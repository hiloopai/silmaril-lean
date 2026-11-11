// A C++ sample for the addr2line differential test: templates, inlining, lambdas,
// several files through headers, and namespaces.
#include "sample.h"

namespace demo {
template <typename T> static inline T twice(T x) { return helper::scale(x, 2); }

struct Acc {
  int total = 0;
  void add(int v) { total += twice(v); }
};

int run(int n) {
  Acc a;
  auto f = [&](int i) { a.add(i * i); };
  for (int i = 0; i < n; i++) f(i);
  return a.total + helper::scale(n, 3);
}
}  // namespace demo

extern "C" int entry(int n) { return demo::run(n); }
