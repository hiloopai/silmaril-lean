module

public import Silmaril.Process.Mt.Csl.Defs

/-!
# POSIX threads as logically atomic primitives

Specifications of the POSIX thread interface (IEEE Std 1003.1-2017, `<pthread.h>` and
`<semaphore.h>`) as **trusted primitives** of the thread-modular system `Silmaril.Process.Mt.Csl`:
each call is one or two atomic steps (`Csl.PrimSpec`) on an abstract state `PSt`, the
**linearization points**. A spec has two parts:

* `fault t args m`: calling the function here is **undefined behaviour** in POSIX (the caller's
  obligation, a precondition): unlocking a normal mutex one does not hold, using an
  uninitialised semaphore, ending a `pthread_once` one did not start;
* `step t args m r m'`: the atomic step from abstract state `m` to `m'` returning `r`. A POSIX
  error is an ordinary result (`EBUSY`, `EDEADLK`, `EPERM`, …) with no state change. **No step**
  means the call blocks (a held lock, an empty semaphore, a thread that has not exited).

Every spec is stated over `PSt`; `PrimSpec.lift` moves it to any memory with a lens onto a `PSt`
(such as the simple model's memory, `Pthread/Simple`), and `prims` makes the whole interface a
`Csl.Prims` table, so that at the top level **the pthread functions are the trusted primitives**.
That glibc's code implements them under a memory model is a separate obligation
(`Pthread/Glibc`).

## The abstract state (`PSt`)

| field | object | value |
|---|---|---|
| `thr` | threads (`pthread_t` is the thread id) | running or exited with a value; detached |
| `jret` | per thread: the value its last `pthread_join` collected | |
| `mtx` | mutexes, by address | kind (normal, recursive, errorcheck), owner, depth |
| `cnd` | condition variables | the waiting threads |
| `rw` | read-write locks | the writer, the readers (with repetition) |
| `once` | `pthread_once_t` controls | not started, running in thread `t`, done |
| `keys`, `dtor`, `tls` | thread-specific data | allocated keys, destructors, per-thread values |
| `spin` | spin locks | uninitialised, free, held by `t` |
| `bar` | barriers | the count (`0`: uninitialised), the threads waiting |
| `sem` | semaphores | uninitialised or a value |

Statically initialised objects (`PTHREAD_MUTEX_INITIALIZER`, `PTHREAD_COND_INITIALIZER`,
`PTHREAD_RWLOCK_INITIALIZER`, `PTHREAD_ONCE_INIT`) are the defaults: a free normal mutex, no
waiters, a free read-write lock, a control not started. Spin locks, barriers and semaphores
have no static initialiser and start uninitialised.

## The calls and their linearization points

| C function | primitive(s) | linearization point |
|---|---|---|
| `pthread_self()` | `self` | the call |
| `pthread_create(&u, NULL, f, a)` | `Csl.TIsa.spawn` with `createRel` | the new thread becomes visible |
| `pthread_join(u, &v)` | `join [u]`, then `joined` reads the value | `u` has exited (blocks before) |
| `pthread_detach(u)` | `detach [u]` | the call |
| `pthread_exit(v)` / return from the start routine | `exit [v]` | the call |
| `pthread_mutex_init(m, attr)` | `mutexInit k [m]` | the call |
| `pthread_mutex_lock/trylock/unlock(m)` | `mutexLock`, `mutexTrylock`, `mutexUnlock` `[m]` | acquisition / release |
| `pthread_cond_wait(c, m)` | `condWait [c, m]`, then (if `0`) `condResume [c, m]` | 1: release `m` and enqueue; 2: reacquire `m` |
| `pthread_cond_signal/broadcast(c)` | `condSignal`, `condBroadcast` `[c]` | the call |
| `pthread_rwlock_rdlock/wrlock/tryrdlock/trywrlock/unlock(l)` | `rwRdlock` … `rwUnlock` `[l]` | acquisition / release |
| `pthread_once(o, f)` | `onceBegin [o]`; if `1`: call `f`, then `onceEnd [o]` | 1: claim (or see done); 2: done |
| `pthread_key_create(&k, d)` | `keyCreate [d]` (result: the key, or `keysMax` for `EAGAIN`) | the call |
| `pthread_key_delete(k)`, `pthread_getspecific(k)`, `pthread_setspecific(k, v)` | `keyDelete`, `getspecific`, `setspecific` | the call |
| `pthread_spin_init/lock/trylock/unlock/destroy(s)` | `spinInit` … `spinDestroy` `[s]` | acquisition / release |
| `pthread_barrier_init(b, NULL, n)`, `pthread_barrier_destroy(b)` | `barInit [b, n]`, `barDestroy [b]` | the call |
| `pthread_barrier_wait(b)` | `barArrive [b]`; if `0`: `barDepart [b]` | 1: arrive (the last one releases all, gets `SERIAL`); 2: leave |
| `sem_init(s, 0, v)`, `sem_wait/trywait/post/getvalue(s)` | `semInit [s, v]`, `semWait` … `semGetvalue` `[s]` | the call |

**Spurious wake-ups.** `condResume` is enabled whenever the mutex is free, whether or not a
signal removed the thread from the waiters: POSIX allows `pthread_cond_wait` to return without
a signal. For safety the waiter set does not matter; it is kept for liveness statements
(`condSignal` wakes some waiter when there is one).

**Error returns.** `sem_*` return `-1` and set `errno`; here the result is the error number
(`0` on success), as for the `pthread_*` functions. `PTHREAD_BARRIER_SERIAL_THREAD` is
`serialThread` (the `int` `-1` as 32 bits).

## Not modelled

Thread attributes (`pthread_attr_*`: detached creation, stack size), cancellation and
cleanup handlers, signals (`EINTR`), timed and robust/priority-inheritance variants,
process-shared objects, `pthread_atfork`, and the running of TLS destructors at thread exit
(user code; `Pthread/Simple` runs them explicitly). Recursive-depth overflow (`EAGAIN` at
`2 ^ 32 - 1` in glibc) and `SEM_VALUE_MAX` overflow of `sem_post` are modelled; key exhaustion
at `PTHREAD_KEYS_MAX = 1024` is modelled. Two threads joining the same thread concurrently is
undefined in POSIX but not detected here (the second join blocks forever).
-/

@[expose] public section

namespace Silmaril.Process.Mt.Pthread

open Silmaril.Process.Mt.Csl

/-! ## Error numbers (Linux x86-64) and limits -/

def EPERM : Nat := 1
def EAGAIN : Nat := 11
def EBUSY : Nat := 16
def EINVAL : Nat := 22
def EDEADLK : Nat := 35
def EOVERFLOW : Nat := 75

/-- `PTHREAD_BARRIER_SERIAL_THREAD`: the `int` `-1`, as 32 bits. -/
def serialThread : Nat := 2 ^ 32 - 1

/-- `PTHREAD_KEYS_MAX` (glibc). -/
def keysMax : Nat := 1024

/-- `SEM_VALUE_MAX` (glibc: `INT_MAX`). -/
def semMax : Nat := 2 ^ 31 - 1

/-- The largest recursion depth of a recursive mutex (glibc: the 32-bit `__count`). -/
def depthMax : Nat := 2 ^ 32 - 1

/-! ## The abstract state -/

/-- Mutex kinds. -/
inductive Kind where
  | normal
  | recursive
  | errorcheck
  deriving DecidableEq, Repr

/-- A mutex: kind, owner, recursion depth (`0` iff free). -/
structure MutexSt where
  kind : Kind := .normal
  owner : Option Nat := none
  depth : Nat := 0
  deriving DecidableEq, Repr

/-- A read-write lock: the writer, the readers (one entry per read lock held). -/
structure RwSt where
  writer : Option Nat := none
  readers : List Nat := []
  deriving DecidableEq, Repr

/-- A `pthread_once_t` control. -/
inductive OnceSt where
  | init
  | running (t : Nat)
  | done
  deriving DecidableEq, Repr

/-- A spin lock. -/
inductive SpinSt where
  | uninit
  | free
  | held (t : Nat)
  deriving DecidableEq, Repr

/-- A barrier: its count (`0`: uninitialised) and the threads waiting at it. -/
structure BarSt where
  count : Nat := 0
  waiting : List Nat := []
  deriving DecidableEq, Repr

/-- A thread's life. -/
inductive Life where
  | running
  | exited (v : Nat)
  deriving DecidableEq, Repr

/-- A thread-table entry. -/
structure ThrSt where
  life : Life := .running
  detached : Bool := false
  deriving DecidableEq, Repr

/-- **The abstract pthread state.** -/
structure PSt where
  thr : Nat → Option ThrSt
  jret : Nat → Nat := fun _ => 0
  mtx : Nat → MutexSt := fun _ => {}
  cnd : Nat → List Nat := fun _ => []
  rw : Nat → RwSt := fun _ => {}
  once : Nat → OnceSt := fun _ => .init
  keys : Nat → Bool := fun _ => false
  dtor : Nat → Nat := fun _ => 0
  tls : Nat → Nat → Nat := fun _ _ => 0
  spin : Nat → SpinSt := fun _ => .uninit
  bar : Nat → BarSt := fun _ => {}
  sem : Nat → Option Nat := fun _ => none

/-- Update one entry of a function. -/
def set {α : Type} (f : Nat → α) (a : Nat) (x : α) : Nat → α := fun b => if b = a then x else f b

/-- The state of a process whose only thread is `t₀` (all objects at their defaults). -/
def PSt.init (t₀ : Nat) : PSt := { thr := fun t => if t = t₀ then some {} else none }

/-- Argument `i` (`0` if absent). -/
def arg (args : List Nat) (i : Nat) : Nat := args.getD i 0

/-! ## Mutexes -/

/-- Take a mutex: owner `t`, depth `1`. -/
def MutexSt.take (s : MutexSt) (t : Nat) : MutexSt := { s with owner := some t, depth := 1 }

/-- Release one level of a mutex held by its owner. -/
def MutexSt.drop (s : MutexSt) : MutexSt :=
  if s.depth ≤ 1 then { s with owner := none, depth := 0 } else { s with depth := s.depth - 1 }

/-- `pthread_mutex_init(m, attr)` with kind `k`: re-initialising a held mutex is undefined. -/
def mutexInit (k : Kind) : PrimSpec PSt where
  fault _ args m := (m.mtx (arg args 0)).owner ≠ none
  step _ args m r m' := r = 0 ∧ m' = { m with mtx := set m.mtx (arg args 0) { kind := k } }

/-- `pthread_mutex_destroy(m)`: destroying a held mutex is undefined. -/
def mutexDestroy : PrimSpec PSt where
  fault _ args m := (m.mtx (arg args 0)).owner ≠ none
  step _ args m r m' := r = 0 ∧ m' = { m with mtx := set m.mtx (arg args 0) {} }

/-- `pthread_mutex_lock(m)`. A free mutex is taken. Its owner relocking: a recursive mutex
deepens (`EAGAIN` at `depthMax`), an error-checking one returns `EDEADLK`, a normal one
**deadlocks** (no step, as POSIX requires: "attempting to relock the mutex causes deadlock").
Held by another thread: blocks. -/
def mutexLock : PrimSpec PSt where
  fault _ _ _ := False
  step t args m r m' :=
    let a := arg args 0
    let s := m.mtx a
    (s.owner = none ∧ r = 0 ∧ m' = { m with mtx := set m.mtx a (s.take t) }) ∨
    (s.owner = some t ∧ s.kind = .recursive ∧ s.depth < depthMax ∧ r = 0 ∧
      m' = { m with mtx := set m.mtx a { s with depth := s.depth + 1 } }) ∨
    (s.owner = some t ∧ s.kind = .recursive ∧ depthMax ≤ s.depth ∧ r = EAGAIN ∧ m' = m) ∨
    (s.owner = some t ∧ s.kind = .errorcheck ∧ r = EDEADLK ∧ m' = m)

/-- `pthread_mutex_trylock(m)`: as `mutexLock`, but `EBUSY` instead of blocking or
deadlocking (also for an error-checking or normal mutex the caller holds). -/
def mutexTrylock : PrimSpec PSt where
  fault _ _ _ := False
  step t args m r m' :=
    let a := arg args 0
    let s := m.mtx a
    (s.owner = none ∧ r = 0 ∧ m' = { m with mtx := set m.mtx a (s.take t) }) ∨
    (s.owner = some t ∧ s.kind = .recursive ∧ s.depth < depthMax ∧ r = 0 ∧
      m' = { m with mtx := set m.mtx a { s with depth := s.depth + 1 } }) ∨
    (s.owner = some t ∧ s.kind = .recursive ∧ depthMax ≤ s.depth ∧ r = EAGAIN ∧ m' = m) ∨
    (s.owner.isSome ∧ ¬ (s.owner = some t ∧ s.kind = .recursive) ∧ r = EBUSY ∧ m' = m)

/-- `pthread_mutex_unlock(m)`. The owner releases one level. A non-owner: `EPERM` for the
recursive and error-checking kinds, undefined for the normal kind. -/
def mutexUnlock : PrimSpec PSt where
  fault t args m := (m.mtx (arg args 0)).kind = .normal ∧ (m.mtx (arg args 0)).owner ≠ some t
  step t args m r m' :=
    let a := arg args 0
    let s := m.mtx a
    (s.owner = some t ∧ r = 0 ∧ m' = { m with mtx := set m.mtx a s.drop }) ∨
    (s.owner ≠ some t ∧ s.kind ≠ .normal ∧ r = EPERM ∧ m' = m)

/-! ## Condition variables -/

/-- Remove one occurrence. -/
def erase (l : List Nat) (x : Nat) : List Nat := l.erase x

/-- `pthread_cond_wait(c, m)`, first half: **release `m` and join the waiters of `c`**,
atomically. The caller must hold `m` exactly once (a recursive mutex held deeper would not be
released; undefined here). A non-owner: `EPERM` for the error-checking and recursive kinds
(glibc's `__pthread_mutex_unlock_usercnt` error, returned by `pthread_cond_wait`), undefined
for the normal kind. -/
def condWait : PrimSpec PSt where
  fault t args m :=
    let s := m.mtx (arg args 1)
    (s.owner ≠ some t ∧ s.kind = .normal) ∨ (s.owner = some t ∧ s.depth ≠ 1)
  step t args m r m' :=
    let c := arg args 0
    let a := arg args 1
    let s := m.mtx a
    (s.owner = some t ∧ s.depth = 1 ∧ r = 0 ∧
      m' = { m with mtx := set m.mtx a s.drop, cnd := set m.cnd c (t :: m.cnd c) }) ∨
    (s.owner ≠ some t ∧ s.kind ≠ .normal ∧ r = EPERM ∧ m' = m)

/-- `pthread_cond_wait(c, m)`, second half: **wake up and reacquire `m`**, enabled whenever `m`
is free (woken by a signal, or spuriously); leaves the waiters of `c`. -/
def condResume : PrimSpec PSt where
  fault _ _ _ := False
  step t args m r m' :=
    let c := arg args 0
    let a := arg args 1
    let s := m.mtx a
    s.owner = none ∧ r = 0 ∧
      m' = { m with mtx := set m.mtx a (s.take t), cnd := set m.cnd c (erase (m.cnd c) t) }

/-- `pthread_cond_signal(c)`: wake at least one waiter if there is one. -/
def condSignal : PrimSpec PSt where
  fault _ _ _ := False
  step _ args m r m' :=
    let c := arg args 0
    r = 0 ∧ ((m.cnd c = [] ∧ m' = m) ∨
      ∃ w ∈ m.cnd c, m' = { m with cnd := set m.cnd c (erase (m.cnd c) w) })

/-- `pthread_cond_broadcast(c)`: wake every waiter. -/
def condBroadcast : PrimSpec PSt where
  fault _ _ _ := False
  step _ args m r m' := r = 0 ∧ m' = { m with cnd := set m.cnd (arg args 0) [] }

/-! ## Read-write locks (glibc's default: readers preferred) -/

/-- `pthread_rwlock_rdlock(l)`: no writer: one more read lock (also for a thread that
already reads); the caller writes: `EDEADLK`; another writer: blocks. -/
def rwRdlock : PrimSpec PSt where
  fault _ _ _ := False
  step t args m r m' :=
    let l := arg args 0
    let s := m.rw l
    (s.writer = none ∧ r = 0 ∧ m' = { m with rw := set m.rw l { s with readers := t :: s.readers } }) ∨
    (s.writer = some t ∧ r = EDEADLK ∧ m' = m)

/-- `pthread_rwlock_tryrdlock(l)`: `EBUSY` instead of blocking. -/
def rwTryRdlock : PrimSpec PSt where
  fault _ _ _ := False
  step t args m r m' :=
    let l := arg args 0
    let s := m.rw l
    (s.writer = none ∧ r = 0 ∧ m' = { m with rw := set m.rw l { s with readers := t :: s.readers } }) ∨
    (s.writer.isSome ∧ r = EBUSY ∧ m' = m)

/-- `pthread_rwlock_wrlock(l)`: free: the caller writes; the caller writes already:
`EDEADLK`; otherwise blocks (a caller that reads deadlocks, as in glibc). -/
def rwWrlock : PrimSpec PSt where
  fault _ _ _ := False
  step t args m r m' :=
    let l := arg args 0
    let s := m.rw l
    (s.writer = none ∧ s.readers = [] ∧ r = 0 ∧ m' = { m with rw := set m.rw l { s with writer := some t } }) ∨
    (s.writer = some t ∧ r = EDEADLK ∧ m' = m)

/-- `pthread_rwlock_trywrlock(l)`: `EBUSY` unless free. -/
def rwTryWrlock : PrimSpec PSt where
  fault _ _ _ := False
  step t args m r m' :=
    let l := arg args 0
    let s := m.rw l
    (s.writer = none ∧ s.readers = [] ∧ r = 0 ∧ m' = { m with rw := set m.rw l { s with writer := some t } }) ∨
    ((s.writer.isSome ∨ s.readers ≠ []) ∧ r = EBUSY ∧ m' = m)

/-- `pthread_rwlock_unlock(l)`: the writer releases, or a reader drops one read lock;
undefined if the caller holds neither. -/
def rwUnlock : PrimSpec PSt where
  fault t args m := (m.rw (arg args 0)).writer ≠ some t ∧ t ∉ (m.rw (arg args 0)).readers
  step t args m r m' :=
    let l := arg args 0
    let s := m.rw l
    r = 0 ∧
    ((s.writer = some t ∧ m' = { m with rw := set m.rw l { s with writer := none } }) ∨
     (s.writer ≠ some t ∧ t ∈ s.readers ∧
       m' = { m with rw := set m.rw l { s with readers := erase s.readers t } }))

/-! ## `pthread_once` -/

/-- `pthread_once(o, f)`, first half: done: returns `0` (skip `f`); not started: the caller
claims it and gets `1` (it must run `f`, then `onceEnd`); running in some thread: blocks (the
caller itself: deadlock, as a recursive `pthread_once` does in glibc). -/
def onceBegin : PrimSpec PSt where
  fault _ _ _ := False
  step t args m r m' :=
    let o := arg args 0
    (m.once o = .done ∧ r = 0 ∧ m' = m) ∨
    (m.once o = .init ∧ r = 1 ∧ m' = { m with once := set m.once o (.running t) })

/-- `pthread_once(o, f)`, second half, after `f` returned: the control is done. Only the
claiming thread may end it. -/
def onceEnd : PrimSpec PSt where
  fault t args m := m.once (arg args 0) ≠ .running t
  step _ args m r m' := r = 0 ∧ m' = { m with once := set m.once (arg args 0) .done }

/-! ## Thread-specific data -/

/-- `pthread_key_create(&k, d)`: a fresh key `k < keysMax`, whose value is `0` (`NULL`) in
every thread, with destructor `d`; the result is the key, or `keysMax` (`EAGAIN`) when all
keys are in use. -/
def keyCreate : PrimSpec PSt where
  fault _ _ _ := False
  step _ args m r m' :=
    (r < keysMax ∧ m.keys r = false ∧
      m' = { m with keys := set m.keys r true, dtor := set m.dtor r (arg args 0),
                    tls := fun u k => if k = r then 0 else m.tls u k }) ∨
    ((∀ k < keysMax, m.keys k = true) ∧ r = keysMax ∧ m' = m)

/-- `pthread_key_delete(k)`: undefined for a key not in use (glibc: `EINVAL`). -/
def keyDelete : PrimSpec PSt where
  fault _ args m := m.keys (arg args 0) = false
  step _ args m r m' := r = 0 ∧ m' = { m with keys := set m.keys (arg args 0) false }

/-- `pthread_getspecific(k)`: the caller's value; undefined for a key not in use. -/
def getspecific : PrimSpec PSt where
  fault _ args m := m.keys (arg args 0) = false
  step t args m r m' := r = m.tls t (arg args 0) ∧ m' = m

/-- `pthread_setspecific(k, v)`: set the caller's value; undefined for a key not in use
(glibc: `EINVAL`). -/
def setspecific : PrimSpec PSt where
  fault _ args m := m.keys (arg args 0) = false
  step t args m r m' :=
    r = 0 ∧ m' = { m with tls := set m.tls t (set (m.tls t) (arg args 0) (arg args 1)) }

/-! ## Spin locks -/

/-- `pthread_spin_init(s, pshared)`: re-initialising a held lock is undefined. -/
def spinInit : PrimSpec PSt where
  fault _ args m := ∃ u, m.spin (arg args 0) = .held u
  step _ args m r m' := r = 0 ∧ m' = { m with spin := set m.spin (arg args 0) .free }

/-- `pthread_spin_destroy(s)`: destroying a held lock is undefined. -/
def spinDestroy : PrimSpec PSt where
  fault _ args m := ∃ u, m.spin (arg args 0) = .held u
  step _ args m r m' := r = 0 ∧ m' = { m with spin := set m.spin (arg args 0) .uninit }

/-- `pthread_spin_lock(s)`: take a free lock; held by another thread: spins (no step);
uninitialised, or held by the caller: undefined. -/
def spinLock : PrimSpec PSt where
  fault t args m := m.spin (arg args 0) = .uninit ∨ m.spin (arg args 0) = .held t
  step t args m r m' :=
    m.spin (arg args 0) = .free ∧ r = 0 ∧ m' = { m with spin := set m.spin (arg args 0) (.held t) }

/-- `pthread_spin_trylock(s)`: take a free lock, else `EBUSY` (also when the caller holds it). -/
def spinTrylock : PrimSpec PSt where
  fault _ args m := m.spin (arg args 0) = .uninit
  step t args m r m' :=
    (m.spin (arg args 0) = .free ∧ r = 0 ∧ m' = { m with spin := set m.spin (arg args 0) (.held t) }) ∨
    ((∃ u, m.spin (arg args 0) = .held u) ∧ r = EBUSY ∧ m' = m)

/-- `pthread_spin_unlock(s)`: undefined unless the caller holds it. -/
def spinUnlock : PrimSpec PSt where
  fault t args m := m.spin (arg args 0) ≠ .held t
  step _ args m r m' := r = 0 ∧ m' = { m with spin := set m.spin (arg args 0) .free }

/-! ## Barriers -/

/-- `pthread_barrier_init(b, NULL, n)`: `EINVAL` for `n = 0`; re-initialising a barrier in use
is undefined. -/
def barInit : PrimSpec PSt where
  fault _ args m := (m.bar (arg args 0)).waiting ≠ []
  step _ args m r m' :=
    (arg args 1 = 0 ∧ r = EINVAL ∧ m' = m) ∨
    (0 < arg args 1 ∧ r = 0 ∧ m' = { m with bar := set m.bar (arg args 0) { count := arg args 1 } })

/-- `pthread_barrier_destroy(b)`: undefined while threads wait at it. -/
def barDestroy : PrimSpec PSt where
  fault _ args m := (m.bar (arg args 0)).waiting ≠ []
  step _ args m r m' := r = 0 ∧ m' = { m with bar := set m.bar (arg args 0) {} }

/-- `pthread_barrier_wait(b)`, first half: **arrive**. The last of `count` threads releases
everyone (the waiters are cleared) and returns `serialThread`; the others join the waiters and
return `0` (and then `barDepart`). Undefined on an uninitialised barrier. -/
def barArrive : PrimSpec PSt where
  fault t args m := (m.bar (arg args 0)).count = 0 ∨ t ∈ (m.bar (arg args 0)).waiting
  step t args m r m' :=
    let b := arg args 0
    let s := m.bar b
    (s.waiting.length + 1 = s.count ∧ r = serialThread ∧
      m' = { m with bar := set m.bar b { s with waiting := [] } }) ∨
    (s.waiting.length + 1 < s.count ∧ r = 0 ∧
      m' = { m with bar := set m.bar b { s with waiting := t :: s.waiting } })

/-- `pthread_barrier_wait(b)`, second half: **leave**, once released (no longer waiting). -/
def barDepart : PrimSpec PSt where
  fault _ _ _ := False
  step t args m r m' := t ∉ (m.bar (arg args 0)).waiting ∧ r = 0 ∧ m' = m

/-! ## Semaphores -/

/-- `sem_init(s, 0, v)`: `EINVAL` above `SEM_VALUE_MAX`. -/
def semInit : PrimSpec PSt where
  fault _ _ _ := False
  step _ args m r m' :=
    (arg args 1 ≤ semMax ∧ r = 0 ∧ m' = { m with sem := set m.sem (arg args 0) (some (arg args 1)) }) ∨
    (semMax < arg args 1 ∧ r = EINVAL ∧ m' = m)

/-- `sem_wait(s)`: decrement a positive value; at `0`, block. Undefined if uninitialised. -/
def semWait : PrimSpec PSt where
  fault _ args m := m.sem (arg args 0) = none
  step _ args m r m' := ∃ n, m.sem (arg args 0) = some (n + 1) ∧ r = 0 ∧
    m' = { m with sem := set m.sem (arg args 0) (some n) }

/-- `sem_trywait(s)`: `EAGAIN` at `0`. -/
def semTrywait : PrimSpec PSt where
  fault _ args m := m.sem (arg args 0) = none
  step _ args m r m' :=
    (∃ n, m.sem (arg args 0) = some (n + 1) ∧ r = 0 ∧ m' = { m with sem := set m.sem (arg args 0) (some n) }) ∨
    (m.sem (arg args 0) = some 0 ∧ r = EAGAIN ∧ m' = m)

/-- `sem_post(s)`: increment; `EOVERFLOW` at `SEM_VALUE_MAX`. -/
def semPost : PrimSpec PSt where
  fault _ args m := m.sem (arg args 0) = none
  step _ args m r m' :=
    (∃ n, m.sem (arg args 0) = some n ∧ n < semMax ∧ r = 0 ∧
      m' = { m with sem := set m.sem (arg args 0) (some (n + 1)) }) ∨
    (m.sem (arg args 0) = some semMax ∧ r = EOVERFLOW ∧ m' = m)

/-- `sem_getvalue(s, &v)`: the value. -/
def semGetvalue : PrimSpec PSt where
  fault _ args m := m.sem (arg args 0) = none
  step _ args m r m' := m.sem (arg args 0) = some r ∧ m' = m

/-! ## Threads -/

/-- `pthread_self()`. -/
def self : PrimSpec PSt where
  fault _ _ _ := False
  step t _ m r m' := r = t ∧ m' = m

/-- **`pthread_create`**, the atomic part of the `clone`: the fresh thread `u` is running,
joinable, with every thread-specific value `0`. -/
def createRel (u : Nat) (m m' : PSt) : Prop :=
  m.thr u = none ∧ m' = { m with thr := set m.thr u (some {}), tls := set m.tls u (fun _ => 0) }

/-- `pthread_join(u, &v)`: once `u` has exited, collect its value into `jret` (which
`joined` reads) and free its entry; blocks while `u` runs. Joining oneself: `EDEADLK`. Joining a
thread that does not exist (or was joined) or is detached is undefined. -/
def join : PrimSpec PSt where
  fault t args m := arg args 0 ≠ t ∧ ∀ e, m.thr (arg args 0) = some e → e.detached = true
  step t args m r m' :=
    let u := arg args 0
    (u = t ∧ r = EDEADLK ∧ m' = m) ∨
    (u ≠ t ∧ r = 0 ∧ ∃ v, m.thr u = some { life := .exited v, detached := false } ∧
      m' = { m with thr := set m.thr u none, jret := set m.jret t v })

/-- The value the caller's last `pthread_join` collected. -/
def joined : PrimSpec PSt where
  fault _ _ _ := False
  step t _ m r m' := r = m.jret t ∧ m' = m

/-- `pthread_detach(u)`: an exited thread is freed, a running one marked detached; undefined
for a thread that does not exist or is detached already (glibc: `EINVAL`). -/
def detach : PrimSpec PSt where
  fault _ args m := ∀ e, m.thr (arg args 0) = some e → e.detached = true
  step _ args m r m' :=
    let u := arg args 0
    r = 0 ∧ ∃ e, m.thr u = some e ∧ e.detached = false ∧
      ((e.life = .running ∧ m' = { m with thr := set m.thr u (some { e with detached := true }) }) ∨
       ((∃ v, e.life = .exited v) ∧ m' = { m with thr := set m.thr u none }))

/-- `pthread_exit(v)`: the caller has exited with `v` (a detached thread is freed). -/
def exit : PrimSpec PSt where
  fault t _ m := ∀ e, m.thr t = some e → e.life ≠ .running
  step t args m r m' := r = 0 ∧ ∃ e, m.thr t = some e ∧ e.life = .running ∧
    m' = { m with thr := set m.thr t (if e.detached then none else some { e with life := .exited (arg args 0) }) }

/-! ## The interface -/

/-- The pthread primitives. -/
inductive Op where
  | self | join | joined | detach | exit
  | mutexInit (k : Kind) | mutexDestroy | mutexLock | mutexTrylock | mutexUnlock
  | condWait | condResume | condSignal | condBroadcast
  | rwRdlock | rwTryRdlock | rwWrlock | rwTryWrlock | rwUnlock
  | onceBegin | onceEnd
  | keyCreate | keyDelete | getspecific | setspecific
  | spinInit | spinDestroy | spinLock | spinTrylock | spinUnlock
  | barInit | barDestroy | barArrive | barDepart
  | semInit | semWait | semTrywait | semPost | semGetvalue
  deriving DecidableEq, Repr

/-- **The specification of each primitive.** -/
def Op.spec : Op → PrimSpec PSt
  | .self => Pthread.self
  | .join => Pthread.join
  | .joined => Pthread.joined
  | .detach => Pthread.detach
  | .exit => Pthread.exit
  | .mutexInit k => Pthread.mutexInit k
  | .mutexDestroy => Pthread.mutexDestroy
  | .mutexLock => Pthread.mutexLock
  | .mutexTrylock => Pthread.mutexTrylock
  | .mutexUnlock => Pthread.mutexUnlock
  | .condWait => Pthread.condWait
  | .condResume => Pthread.condResume
  | .condSignal => Pthread.condSignal
  | .condBroadcast => Pthread.condBroadcast
  | .rwRdlock => Pthread.rwRdlock
  | .rwTryRdlock => Pthread.rwTryRdlock
  | .rwWrlock => Pthread.rwWrlock
  | .rwTryWrlock => Pthread.rwTryWrlock
  | .rwUnlock => Pthread.rwUnlock
  | .onceBegin => Pthread.onceBegin
  | .onceEnd => Pthread.onceEnd
  | .keyCreate => Pthread.keyCreate
  | .keyDelete => Pthread.keyDelete
  | .getspecific => Pthread.getspecific
  | .setspecific => Pthread.setspecific
  | .spinInit => Pthread.spinInit
  | .spinDestroy => Pthread.spinDestroy
  | .spinLock => Pthread.spinLock
  | .spinTrylock => Pthread.spinTrylock
  | .spinUnlock => Pthread.spinUnlock
  | .barInit => Pthread.barInit
  | .barDestroy => Pthread.barDestroy
  | .barArrive => Pthread.barArrive
  | .barDepart => Pthread.barDepart
  | .semInit => Pthread.semInit
  | .semWait => Pthread.semWait
  | .semTrywait => Pthread.semTrywait
  | .semPost => Pthread.semPost
  | .semGetvalue => Pthread.semGetvalue

/-- A memory with a pthread state inside. -/
structure Lens (M : Type) where
  get : M → PSt
  put : M → PSt → M

/-- **A spec on a memory with a pthread state**: the step changes only the pthread state. -/
def lift {M : Type} (L : Lens M) (sp : PrimSpec PSt) : PrimSpec M where
  fault t args m := sp.fault t args (L.get m)
  step t args m r m' := ∃ p', sp.step t args (L.get m) r p' ∧ m' = L.put m p'

/-- **The pthread interface as trusted primitives** of threads with states `σ`: `call s` says
which pthread function the thread calls with which arguments, `resume s r` continues it with
the result. -/
def prims {σ M : Type} (L : Lens M) (call : σ → Option (Op × List Nat)) (resume : σ → Nat → σ) :
    Prims σ M where
  Prim := Op
  call := call
  resume := resume
  spec o := lift L o.spec

/-! ## Steps of the interface alone -/

/-- One linearization point of any thread: a pthread primitive step or a `pthread_create`. -/
inductive PStep : PSt → PSt → Prop
  | prim {m m' t o args r} (h : (Op.spec o).step t args m r m') : PStep m m'
  | create {m m' u} (h : createRel u m m') : PStep m m'

/-- Reachability by linearization points. -/
abbrev PReach : PSt → PSt → Prop := Star PStep

end Silmaril.Process.Mt.Pthread
