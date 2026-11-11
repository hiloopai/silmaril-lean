namespace helper {
template <typename T> inline T scale(T x, int k) {
  T r = x;
  for (int i = 1; i < k; i++) r += x;
  return r;
}
}  // namespace helper
