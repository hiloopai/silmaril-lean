#include <typeinfo>
#include <new>
struct S { template<class U> int g(); int m; int f(int); static int sm; using type = int; template<class U> struct In { static int v; }; S* operator->(); };
struct P { int m; };
template<class T> auto dt(T t) -> decltype(t.m) { return t.m; }
template<class T> auto pt(T* t) -> decltype(t->m) { return t->m; }
template<class T> auto sr1(T t) -> decltype(T::sm) { return 0; }
template<class T> auto sr2(T t) -> decltype(typename T::type()) { return 0; }
template<class T> auto sr3(T t) -> decltype(T::template In<int>::v) { return 0; }
template<class T> auto nw1(T t) -> decltype(new T) { return 0; }
template<class T> auto nw2(T t) -> decltype(new T(t)) { return 0; }
template<class T> auto nw3(T t) -> decltype(new T[3]) { return 0; }
template<class T> auto nw4(T t) -> decltype(::new T) { return 0; }
template<class T> auto nw5(T* t) -> decltype(new (t) T()) { return 0; }
template<class T> auto dl1(T* t) -> decltype(delete t) { }
template<class T> auto dl2(T* t) -> decltype(delete[] t) { }
template<class T> auto dl3(T* t) -> decltype(::delete t) { }
template<class... T> auto fl1(T... t) -> decltype((... + t)) { return 0; }
template<class... T> auto fr1(T... t) -> decltype((t + ...)) { return 0; }
template<class... T> auto fL1(T... t) -> decltype((1 + ... + t)) { return 0; }
template<class... T> auto fR1(T... t) -> decltype((t + ... + 1)) { return 0; }
template<class... T> auto fcomma(T... t) -> decltype((t , ...)) { }
template<class T> auto tw1(T t) -> decltype(throw t) { }
template<class T> auto tr1(T t) -> decltype(t ? throw : 0) { return 0; }
template<class T> auto ti1(T t) -> decltype(typeid(T)) { return typeid(T); }
template<class T> auto te1(T t) -> decltype(typeid(t)) { return typeid(t); }
template<class... T> auto szp(T... t) -> decltype(sizeof...(T)) { return 0; }
template<class... T> auto szf(T... t) -> decltype(sizeof...(t)) { return 0; }
template<class T> auto al1(T t) -> decltype(alignof(T)) { return 0; }
template<class T> auto nx1(T t) -> decltype(noexcept(t)) { return 0; }
template<class T> auto sc1(T t) -> decltype(static_cast<int>(t)) { return 0; }
template<class T> auto dc1(T* t) -> decltype(dynamic_cast<S*>(t)) { return 0; }
template<class T> auto cc1(T* t) -> decltype(const_cast<const T*>(t)) { return 0; }
template<class T> auto rc1(T t) -> decltype(reinterpret_cast<char*>(t)) { return 0; }
struct Q{Q(int,int);}; template<class T> auto il1(T t) -> decltype(Q{t, t}) { return Q{1,2}; }
template<class T> auto cvm(T t) -> decltype(Q(t, t)) { return Q(1,2); }
template<class T> auto pinc(T t) -> decltype(++t) { static T y; return y; }
template<class T> auto ponc(T t) -> decltype(t++) { return t; }
template<class T> auto mcall(T t) -> decltype(t.f(1)) { return 0; }
template<class T> auto ds1(T t, int T::*p) -> decltype(t.*p) { static int z; return z; }
template<class T> auto dtt(T t) -> decltype(t.template g<int>()) { return 0; }
template<class T> auto dn(T t) -> decltype(t.~T()) { }
template<class T> auto on(T t) -> decltype(t.operator->()) { return 0; }
template<class T> auto gsn(T t) -> decltype(::dt(t)) { return 0; }
template<class T> auto flt(T t, int (*)[sizeof(T) > 1.5f]) -> int { return 0; }
template<class T> auto dbl(T t, int (*)[sizeof(T) > 2.5]) -> int { return 0; }
template<class T> auto ngd(T t, int (*)[sizeof(T) > -2.5]) -> int { return 0; }
template<class T> auto npt(T t) -> decltype(t == nullptr) { return 0; }
const int& rtmp = 42;
thread_local int tl = 1;
void use() {
  S s; P p; S* ps = &s; int x = 1;
  dt(s); pt(&p); sr1(s); sr2(s); sr3(s); nw1(x); nw2(x); nw3(x); nw4(x); nw5(ps);
  dl1(ps); dl2(ps); dl3(ps); fl1(1,2); fr1(1,2); fL1(1,2); fR1(1,2); fcomma(1,2); tw1(x); tr1(x);
  ti1(x); te1(x); szp(1,2); szf(1,2); al1(x); nx1(x); sc1(x); dc1(ps); cc1(ps); rc1(x); il1(x); cvm(x); pinc(x); ponc(x);
  mcall(s); ds1(p, &P::m); dtt(s); dn(s); on(s); gsn(s); flt(x, nullptr); dbl(x, nullptr); ngd(x,nullptr); npt(ps);
}
