module

public import Silmaril.Process.Mt.Drf.Defs

/-!
# Trusted primitives: abstract atomic specifications, implementations, correctness

Program code is verified against **trusted primitives**: a mutex, a recursive stream lock,
atomics. Each has an abstract, logically atomic specification (`PrimSpec`). A client calls them
as single synchronising steps, so the client is a `Sys` (`Client.withSpec`) and the bridge
(`Silmaril.Process.Mt.Drf.drf_sc`) applies to it. The real process runs the primitives'
**implementations** (`PrimImpl`), instruction by instruction, under TSO or XL
(`Client.withImpl`). Implementations may race internally (the recursive lock's owner check
reads the owner field without synchronisation), so they are not covered by the bridge. Their
correctness is a separate assumption for each memory model: `PrimsCorrect`.

## Definitions

* `PrimSpec`: `step t args rs ws ret`. Called by thread `t` with `args`, the primitive
  atomically reads `rs`, writes `ws` and returns `ret`; when there is no step the call blocks.
  `pre t args m` is the caller's obligation.
* `PrimImpl`: the code of a primitive, run by the calling thread: a start state from the
  arguments, thread-local and synchronising steps, and a return value when finished. A
  synchronising step of an implementation changes only its own thread. `futex` waits and wakes
  are synchronising steps with no memory effect: for safety, a `futex` wait may return at any
  time (spurious wake-ups are allowed by `futex(2)`), and a wake only ends waits.
* `Client`: a thread system whose threads may also call primitive `p` with arguments `args`
  and continuation `k` (the state after the call returns `ret` is `k ret`).
* `Client.withSpec P`: primitive calls are synchronising steps meeting `P p` (the SC/atomic
  semantics of the program).
* `Client.withImpl I`: a call enters the implementation `I p`; its steps are the thread's steps
  until it returns.
* `PrimsCorrect M P I cells β`: for every client that does not touch the primitives' internal
  `cells` itself and calls each primitive only when its precondition holds, every drained,
  quiescent (no thread inside a primitive) configuration reached by the implementation under
  `M` is reached by the specification under `M`, with memory seen through `β` (which hides
  implementation-only values, for example a contended lock word `2` that the specification
  writes as `1`).

## glibc's locks

`lllLock`, `lllUnlock`: glibc's low-level lock (`lll_lock`/`lll_unlock`,
`sysdeps/nptl/lowlevellock.h`): `lock cmpxchg 0 → 1`, else a loop of `xchg 2` and
`futex_wait(2)`; unlock is `xchg 0` and a `futex_wake` if the old value was above `1`.
`ioLock`, `ioUnlock`: the recursive stream lock `_IO_lock_t {int lock; int cnt; void *owner}`
(`sysdeps/nptl/stdio-lock.h`): lock is "if `owner ≠ self` then `lll_lock`, `owner := self`;
`++cnt`", unlock is "if `--cnt = 0` then `owner := NULL`, `lll_unlock`". The owner field is read
with a plain load by threads that do not hold the lock. These are the glibc 2.39 sources as
described in the pull request, not machine code: the link to the bytes of a pinned `libc.so.6`
is not made here. Fields are word cells: a lock at `l` has its word at `l`, `cnt` at `l + 1` and
`owner` at `l + 2`. `self t` is thread `t`'s descriptor address (`THREAD_SELF`), nonzero and
injective.
-/

@[expose] public section

namespace Silmaril.Process.Mt.Drf

/-! ## Primitives -/

/-- **An abstract, logically atomic primitive specification.** -/
structure PrimSpec where
  /-- The caller's obligation: thread, arguments, memory at the call. -/
  pre : Nat → List Nat → Mem → Prop
  /-- One atomic step: thread, arguments, reads, writes, return value. -/
  step : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat) → Nat → Prop

/-- **A primitive implementation**: code run by the calling thread. -/
structure PrimImpl where
  St : Type
  start : Nat → List Nat → St
  loc : Nat → St → Lab → St → Prop
  sync : Nat → St → List (Nat × Nat) → List (Nat × Nat) → St → Prop
  ret : St → Option Nat

/-- **A client**: thread-local and synchronising steps, and primitive calls
`call t s p args k` (thread `t` in state `s` calls primitive `p` with `args`, continuing as
`k ret`). -/
structure Client where
  St : Type
  loc : Nat → St → Lab → St → Prop
  sync : Nat → (Nat → St) → List (Nat × Nat) → List (Nat × Nat) → (Nat → St) → Prop
  call : Nat → St → Nat → List Nat → (Nat → St) → Prop

/-- The cells a label touches. -/
def Lab.addrs : Lab → List Nat
  | .plain rs ws _ => rs.map (·.1) ++ ws.map (·.1)
  | .sfence => []

/-- **The client with atomic primitives**: a primitive call is one synchronising step. -/
def Client.withSpec (cl : Client) (P : Nat → PrimSpec) : Sys where
  St := cl.St
  loc := cl.loc
  sync t ts rs ws ts' := cl.sync t ts rs ws ts' ∨
    ∃ p args k r, cl.call t (ts t) p args k ∧ (P p).step t args rs ws r ∧ ts' = upd ts t (k r)

/-- A thread of the implemented client: in client code, or inside primitive `p` in state `s`,
called from client state `c` with continuation `k`. -/
inductive IState (cl : Client) (I : Nat → PrimImpl) where
  | cl (s : cl.St)
  | inPrim (p : Nat) (s : (I p).St) (c : cl.St) (k : Nat → cl.St)

/-- In client code. -/
def IState.isCl {cl : Client} {I : Nat → PrimImpl} : IState cl I → Bool
  | .cl _ => true
  | .inPrim .. => false

/-- Thread-local steps of the implemented client. -/
inductive ILoc (cl : Client) (I : Nat → PrimImpl) : Nat → IState cl I → Lab → IState cl I → Prop
  | cl {t s l s'} (h : cl.loc t s l s') : ILoc cl I t (.cl s) l (.cl s')
  | call {t s p args k} (h : cl.call t s p args k) :
      ILoc cl I t (.cl s) (.plain [] [] false) (.inPrim p ((I p).start t args) s k)
  | prim {t p s l s' c k} (h : (I p).loc t s l s') :
      ILoc cl I t (.inPrim p s c k) l (.inPrim p s' c k)
  | ret {t p s c k r} (h : (I p).ret s = some r) :
      ILoc cl I t (.inPrim p s c k) (.plain [] [] false) (.cl (k r))

/-- Fill the threads inside primitives with arbitrary client states `fill`: `ts u = .cl (cts u)`
gives `cts u`, a thread inside a primitive gives `fill u`. -/
def IState.fill {cl : Client} {I : Nat → PrimImpl} (ts : Nat → IState cl I)
    (cts fill : Nat → cl.St) : Nat → cl.St :=
  fun u => if (ts u).isCl then cts u else fill u

/-- Synchronising steps of the implemented client. A client synchronising step is taken by a
thread in client code, changes only threads in client code, and may not depend on the states of
threads inside primitives: it must be a client step whatever client states they are given. -/
inductive ISync (cl : Client) (I : Nat → PrimImpl) :
    Nat → (Nat → IState cl I) → List (Nat × Nat) → List (Nat × Nat) → (Nat → IState cl I) → Prop
  | cl {t ts rs ws cts cts'} (ht : (ts t).isCl = true)
      (hcl : ∀ u, (ts u).isCl = true → ts u = .cl (cts u))
      (h : ∀ fill, cl.sync t (IState.fill ts cts fill) rs ws (IState.fill ts cts' fill)) :
      ISync cl I t ts rs ws (fun u => if (ts u).isCl then .cl (cts' u) else ts u)
  | prim {t ts p s c k rs ws s'} (hts : ts t = .inPrim p s c k) (h : (I p).sync t s rs ws s') :
      ISync cl I t ts rs ws (upd ts t (.inPrim p s' c k))

/-- **The client with implemented primitives.** -/
def Client.withImpl (cl : Client) (I : Nat → PrimImpl) : Sys :=
  ⟨IState cl I, ILoc cl I, ISync cl I⟩

/-- The client never touches the cells `cells` itself. -/
def Client.Avoids (cl : Client) (cells : Nat → Prop) : Prop :=
  (∀ t s l s', cl.loc t s l s' → ∀ a ∈ l.addrs, ¬ cells a) ∧
  ∀ t ts rs ws ts', cl.sync t ts rs ws ts' → ∀ p ∈ rs ++ ws, ¬ cells p.1

/-- The client calls primitives only when their preconditions hold, in every configuration the
specification reaches under `M` from `C0` (only synchronising steps touch the
primitive-internal cells, so they are never buffered and memory is what every thread sees). -/
def Client.CallsOk (cl : Client) (P : Nat → PrimSpec) (M : Model) (N : Nat)
    (C0 : Cfg (cl.withSpec P)) : Prop :=
  ∀ C, BReach M (cl.withSpec P) N C0.toB C → ∀ t < N, ∀ p args k,
    cl.call t (C.ts t) p args k → (P p).pre t args C.mem

/-- **Correct implementations under `M`.** For every client avoiding the primitives' internal
cells and respecting their preconditions, every drained configuration that the implementation
reaches under `M` with all threads in client code is, seen through `β`, reached by the
specification under `M`. -/
def PrimsCorrect (M : Model) (P : Nat → PrimSpec) (I : Nat → PrimImpl) (cells : Nat → Prop)
    (β : Mem → Mem) : Prop :=
  ∀ (cl : Client) (N : Nat) (cts0 : Nat → cl.St) (m0 : Mem),
    cl.Avoids cells → cl.CallsOk P M N ⟨cts0, β m0⟩ →
    ∀ (C : BCfg (cl.withImpl I)) (cts : Nat → cl.St),
      BReach M (cl.withImpl I) N (⟨fun u => .cl (cts0 u), m0⟩ : Cfg (cl.withImpl I)).toB C →
      C.Drained → (∀ u, C.ts u = .cl (cts u)) →
      BReach M (cl.withSpec P) N (⟨cts0, β m0⟩ : Cfg (cl.withSpec P)).toB
        ⟨cts, β C.mem, fun _ => []⟩

/-! ## glibc's locks -/

namespace Glibc

/-- Primitive numbers. -/
def mutexLock : Nat := 0
def mutexUnlock : Nat := 1
def recLock : Nat := 2
def recUnlock : Nat := 3

/-- Lock blocks: `locks l` marks a lock at `l` (cells `l`, `l + 1`, `l + 2`). -/
def lockCells (locks : Nat → Bool) (a : Nat) : Prop :=
  locks a = true ∨ (1 ≤ a ∧ locks (a - 1) = true) ∨ (2 ≤ a ∧ locks (a - 2) = true)

/-- Lock blocks do not overlap. -/
def LocksDisjoint (locks : Nat → Bool) : Prop :=
  ∀ l l', locks l = true → locks l' = true → l ≠ l' → l + 3 ≤ l' ∨ l' + 3 ≤ l

/-- The specification's view of memory: a held lock word is `1` (the implementation also uses
`2`, "held, maybe with waiters"). -/
def absMem (locks : Nat → Bool) (m : Mem) : Mem := fun a => if locks a then min (m a) 1 else m a

/-- No step: calls of an unused primitive number block. -/
def blocked : PrimSpec := ⟨fun _ _ _ => False, fun _ _ _ _ _ => False⟩

/-- **Mutex lock**: takes a free word to `1`. -/
def lockSpec (locks : Nat → Bool) : PrimSpec :=
  ⟨fun _ args _ => ∃ l, args = [l] ∧ locks l = true,
    fun _ args rs ws r => ∃ l, args = [l] ∧ rs = [(l, 0)] ∧ ws = [(l, 1)] ∧ r = 0⟩

/-- **Mutex unlock**: frees a held word (the caller's obligation: the word is held). -/
def unlockSpec (locks : Nat → Bool) : PrimSpec :=
  ⟨fun _ args m => ∃ l, args = [l] ∧ locks l = true ∧ m l ≠ 0,
    fun _ args rs ws r => ∃ l v, args = [l] ∧ v ≠ 0 ∧ rs = [(l, v)] ∧ ws = [(l, 0)] ∧ r = 0⟩

/-- **Recursive lock**: the owner increments the count; any other thread takes the free word,
becomes owner and increments the count. -/
def recLockSpec (self : Nat → Nat) (locks : Nat → Bool) : PrimSpec :=
  ⟨fun _ args _ => ∃ l, args = [l] ∧ locks l = true,
    fun t args rs ws r => r = 0 ∧ ∃ l c, args = [l] ∧
      ((rs = [(l + 2, self t), (l + 1, c)] ∧ ws = [(l + 1, c + 1)]) ∨
       (∃ o, o ≠ self t ∧ rs = [(l + 2, o), (l, 0), (l + 1, c)] ∧
         ws = [(l, 1), (l + 2, self t), (l + 1, c + 1)]))⟩

/-- **Recursive unlock** (by the owner, count positive): decrements the count; at zero clears
the owner and frees the word. -/
def recUnlockSpec (self : Nat → Nat) (locks : Nat → Bool) : PrimSpec :=
  ⟨fun t args m => ∃ l, args = [l] ∧ locks l = true ∧ m (l + 2) = self t ∧ 1 ≤ m (l + 1),
    fun t args rs ws r => r = 0 ∧ ∃ l c, args = [l] ∧ 1 ≤ c ∧
      rs = [(l + 2, self t), (l + 1, c)] ∧
      ws = (if c = 1 then [(l + 1, 0), (l + 2, 0), (l, 0)] else [(l + 1, c - 1)])⟩

/-- The mutex alone: primitives `0` (lock) and `1` (unlock). -/
def mutexSpec (locks : Nat → Bool) : Nat → PrimSpec
  | 0 => lockSpec locks
  | 1 => unlockSpec locks
  | _ => blocked

/-- **The abstract specifications**: mutex lock and unlock, recursive lock and unlock. -/
def spec (self : Nat → Nat) (locks : Nat → Bool) : Nat → PrimSpec
  | 0 => lockSpec locks
  | 1 => unlockSpec locks
  | 2 => recLockSpec self locks
  | 3 => recUnlockSpec self locks
  | _ => blocked

/-- Implementation state: program counter and lock address. -/
structure PSt where
  pc : Nat
  l : Nat

/-- The start state: the lock address from the arguments (`pc = 99` blocks on bad arguments). -/
def pstart (args : List Nat) : PSt :=
  match args with
  | [l] => ⟨0, l⟩
  | _ => ⟨99, 0⟩

/-- `lll_lock` (pcs `0`–`2`, done at `3`): `lock cmpxchg 0 → 1`; else loop `xchg 2`,
`futex_wait`. `lll_lock` inside `_IO_lock_lock` runs at pcs `base + 0`–`base + 2` and continues
at `next`. -/
inductive LllLock (base next : Nat) : PSt → List (Nat × Nat) → List (Nat × Nat) → PSt → Prop
  | cas {s : PSt} {v} (h : s.pc = base) :
      LllLock base next s [(s.l, v)] [(s.l, if v = 0 then 1 else v)]
        ⟨if v = 0 then next else base + 1, s.l⟩
  | xchg {s : PSt} {v} (h : s.pc = base + 1) :
      LllLock base next s [(s.l, v)] [(s.l, 2)] ⟨if v = 0 then next else base + 2, s.l⟩
  | wait {s : PSt} (h : s.pc = base + 2) : LllLock base next s [] [] ⟨base + 1, s.l⟩

/-- `lll_unlock` at pcs `base`, `base + 1`, continuing at `next`: `xchg 0`, then `futex_wake`
if the old value was above `1`. -/
inductive LllUnlock (base next : Nat) : PSt → List (Nat × Nat) → List (Nat × Nat) → PSt → Prop
  | xchg {s : PSt} {v} (h : s.pc = base) :
      LllUnlock base next s [(s.l, v)] [(s.l, 0)] ⟨if 1 < v then base + 1 else next, s.l⟩
  | wake {s : PSt} (h : s.pc = base + 1) : LllUnlock base next s [] [] ⟨next, s.l⟩

/-- `_IO_lock_lock`'s plain steps: the owner check (pc `0`), `owner := self` (pc `4`), `++cnt`
(pc `5`); done at `6`. -/
inductive IoLockLoc (self : Nat → Nat) : Nat → PSt → Lab → PSt → Prop
  | own {t} {s : PSt} {o} (h : s.pc = 0) :
      IoLockLoc self t s (.plain [(s.l + 2, o)] [] false) ⟨if o = self t then 5 else 1, s.l⟩
  | setOwn {t} {s : PSt} (h : s.pc = 4) :
      IoLockLoc self t s (.plain [] [(s.l + 2, self t)] false) ⟨5, s.l⟩
  | inc {t} {s : PSt} {c} (h : s.pc = 5) :
      IoLockLoc self t s (.plain [(s.l + 1, c)] [(s.l + 1, c + 1)] false) ⟨6, s.l⟩

/-- `_IO_lock_unlock`'s plain steps: `--cnt` (pc `0`), `owner := NULL` (pc `1`); done at `4`. -/
inductive IoUnlockLoc : Nat → PSt → Lab → PSt → Prop
  | dec {t} {s : PSt} {c} (h : s.pc = 0) :
      IoUnlockLoc t s (.plain [(s.l + 1, c)] [(s.l + 1, c - 1)] false)
        ⟨if c - 1 = 0 then 1 else 4, s.l⟩
  | clrOwn {t} {s : PSt} (h : s.pc = 1) : IoUnlockLoc t s (.plain [] [(s.l + 2, 0)] false) ⟨2, s.l⟩

/-- The mutex's synchronising steps: `lll_lock` (primitive `0`), `lll_unlock` (primitive `1`). -/
inductive MutexSync : Nat → PSt → List (Nat × Nat) → List (Nat × Nat) → PSt → Prop
  | lock {s rs ws s'} (h : LllLock 0 3 s rs ws s') : MutexSync 0 s rs ws s'
  | unlock {s rs ws s'} (h : LllUnlock 0 2 s rs ws s') : MutexSync 1 s rs ws s'

/-- The mutex's return: `lll_lock` at pc `3`, `lll_unlock` at pc `2`. -/
def mutexRet : Nat → PSt → Option Nat
  | 0, s => if s.pc = 3 then some 0 else none
  | 1, s => if s.pc = 2 then some 0 else none
  | _, _ => none

/-- The mutex's implementations (other primitive numbers have no steps). -/
def mutexImpl (p : Nat) : PrimImpl :=
  ⟨PSt, fun _ => pstart, fun _ _ _ _ => False, fun _ => MutexSync p, mutexRet p⟩

/-- All four locks' thread-local steps: `_IO_lock_lock` (`2`) and `_IO_lock_unlock` (`3`). -/
inductive LockLoc (self : Nat → Nat) : Nat → Nat → PSt → Lab → PSt → Prop
  | ioLock {t s l s'} (h : IoLockLoc self t s l s') : LockLoc self 2 t s l s'
  | ioUnlock {t s l s'} (h : IoUnlockLoc t s l s') : LockLoc self 3 t s l s'

/-- All four locks' synchronising steps: `lll_lock` (`0`), `lll_unlock` (`1`), and the
`lll_lock`/`lll_unlock` inside `_IO_lock_lock` (`2`) and `_IO_lock_unlock` (`3`). -/
inductive LockSync : Nat → PSt → List (Nat × Nat) → List (Nat × Nat) → PSt → Prop
  | lock {s rs ws s'} (h : LllLock 0 3 s rs ws s') : LockSync 0 s rs ws s'
  | unlock {s rs ws s'} (h : LllUnlock 0 2 s rs ws s') : LockSync 1 s rs ws s'
  | ioLock {s rs ws s'} (h : LllLock 1 4 s rs ws s') : LockSync 2 s rs ws s'
  | ioUnlock {s rs ws s'} (h : LllUnlock 2 4 s rs ws s') : LockSync 3 s rs ws s'

/-- All four locks' returns. -/
def lockRet : Nat → PSt → Option Nat
  | 0, s => if s.pc = 3 then some 0 else none
  | 1, s => if s.pc = 2 then some 0 else none
  | 2, s => if s.pc = 6 then some 0 else none
  | 3, s => if s.pc = 4 then some 0 else none
  | _, _ => none

/-- **The implementations**: `lll_lock`, `lll_unlock`, `_IO_lock_lock`, `_IO_lock_unlock`. -/
def impl (self : Nat → Nat) (p : Nat) : PrimImpl :=
  ⟨PSt, fun _ => pstart, fun t => LockLoc self p t, fun _ => LockSync p, lockRet p⟩

end Glibc

/-! ## Tasks -/

/-- **glibc's locks are correct under `M`** (a statement; not proved here): for every injective,
nonzero `self` and disjoint lock blocks, the implementations `Glibc.impl` meet the atomic
specifications `Glibc.spec` under `M`.

Proof plan. Simulation of `Client.withImpl` runs by `Client.withSpec` runs. A thread inside a
primitive maps to its caller's state before the linearisation point and to the continuation
after it. Linearisation points: the `cmpxchg` or `xchg` that reads `0` (`lll_lock`), the
`xchg 0` (`lll_unlock`), the owner check that reads `self` (`_IO_lock_lock`, owner path), the
acquiring `lll_lock` step (`_IO_lock_lock`, other path), and `--cnt` (`_IO_lock_unlock`). Client
steps and flushes map one to one: the client avoids the lock cells, and a thread's buffer holds
its own `owner`/`cnt` stores only while it holds the lock. Memory is related through `β` plus
the pending `owner`/`cnt` stores of the holder, which the specification has already made. The
`lll_lock` part needs no TSO reasoning (all its accesses are locked). The recursive lock's racy
owner check is benign under TSO and XL because (i) only the holder stores `self t` into `owner`,
(ii) a thread's own load sees its own newest buffered store (store forwarding), and (iii) a
thread's `owner := NULL` precedes its `xchg 0` in its buffer, which that locked instruction
drains, so no thread reads its own `self` from `owner` unless it holds the lock. -/
def Task.glibcLocks (M : Model) : Prop :=
  ∀ (self : Nat → Nat) (locks : Nat → Bool), (∀ t u, self t = self u → t = u) →
    (∀ t, self t ≠ 0) → Glibc.LocksDisjoint locks →
    PrimsCorrect M (Glibc.spec self locks) (Glibc.impl self) (Glibc.lockCells locks)
      (Glibc.absMem locks)


/-- **glibc's `lll_lock` mutex is correct under `M`**: `lll_lock`/`lll_unlock` meet the atomic
mutex specification. All their memory accesses are locked instructions, so no reasoning about
buffers is needed beyond the client's. Proved for every `M`:
`Silmaril.Process.Mt.Drf.lllMutex_holds`. -/
def Task.lllMutex (M : Model) : Prop :=
  ∀ locks : Nat → Bool, PrimsCorrect M (Glibc.mutexSpec locks) Glibc.mutexImpl
    (fun a => locks a = true) (Glibc.absMem locks)

end Silmaril.Process.Mt.Drf
