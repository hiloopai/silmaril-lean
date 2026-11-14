module

public import Silmaril.Process.Mt.Pthread.Defs
public import Silmaril.Project.Shapes.Mt.Defs
public import Silmaril.X86.MemoryModel.Lattice.Defs

/-!
# glibc's pthreads against the specifications, per memory model

The implementation obligations of the pthread primitives (`Pthread/Defs`): **the code of a
pinned glibc, run under a memory model, implements each specification**. The form is MT-DECOMP's
`silmaril.shapes.mt.primitive` (`Shapes.Mt.Primitive sp X`): a concrete model `X` of the most
general client of `sp` (every thread runs any script of calls; `Csl.TIsa.mgc`), running the
implementation under the memory model, refines the atomic specification (`Csl.Model.Sound`)
for every client invariant.

Memory models are named by the lattice of `Silmaril.X86.MemoryModel.Lattice` (`Name`):
obligations are stated at `tso` (x86-TSO) and `xl` (the loose x86 model). A model that allows
fewer executions inherits them (`CodeModel.sound_mono`, for code models whose runs grow with the
model), so `tso` covers `sc`, and `xl` covers `sc` and `tso`.

## The pin

glibc **2.39-0ubuntu8.9** (Ubuntu 24.04), `/lib/x86_64-linux-gnu/libc.so.6`, `pin` below
(SHA-256 and GNU build id). The symbol addresses (`syms`) are from `nm -D`; the code bytes of the
spin-lock functions (`spinLockBytes`, `spinTrylockBytes`, `spinUnlockBytes`) from
`objdump -d`:

```
pthread_spin_lock (0xa41d0):                    pthread_spin_trylock (0xa41f0):
  a41d0 f3 0f 1e fa  endbr64                      a41f0 f3 0f 1e fa  endbr64
  a41d4 31 c0        xor   %eax,%eax              a41f4 31 c9        xor   %ecx,%ecx
  a41d6 f0 ff 0f     lock decl (%rdi)    [dec]    a41f6 87 0f        xchg  %ecx,(%rdi)   [xchg]
  a41d9 75 05        jne   a41e0                  a41f8 83 f9 01     cmp   $0x1,%ecx
  a41db c3           ret                          a41fb 75 03        jne   a4200
  a41e0 f3 90        pause               [spin]   a41fd 31 c0        xor   %eax,%eax
  a41e2 39 07        cmp   %eax,(%rdi)            a41ff c3           ret
  a41e4 7e fa        jle   a41e0                  a4200 b8 10 00 00 00  mov $0x10,%eax  (EBUSY)
  a41e6 f0 ff 0f     lock decl (%rdi)    [dec]    a4205 c3           ret
  a41e9 75 f5        jne   a41e0
  a41eb c3           ret                        pthread_spin_unlock = pthread_spin_init (0xa4210):
                                                  a4210 f3 0f 1e fa  endbr64
                                                  a4214 c7 07 01 00 00 00  movl $0x1,(%rdi)  [st]
                                                  a421a 31 c0        xor   %eax,%eax
                                                  a421c c3           ret
```

The lock word is 1 when free and at most 0 when held: `lock decl` takes it from 1 to 0
(`ZF`: acquired) or drives it below 0; the spin loop waits, with plain loads, for a positive
word; `trylock` swaps in 0; unlock is a **plain store** of 1 (not a barrier: the hardware run
of `scripts/pthread-hw` shows store buffering across `pthread_spin_unlock`, and none across
`pthread_mutex_unlock`, whose multi-threaded path is `xchg`).

## The spin-lock model (`SConf`, `SStep`)

The most general client of the spin lock: each thread runs a script of calls `[op, s]`
(`1`: `pthread_spin_lock(s)`, `2`: `pthread_spin_trylock(s)`, `3`: `pthread_spin_unlock(s)`).
A thread is between calls (`idle`), or inside `pthread_spin_lock` at a `lock decl` (`dec`) or in
the spin loop (`spin`). **Each step is one memory instruction together with the register-only
instructions and branches after it** (`xor`, `jne`, `cmp`/`jle` on the loaded value, `ret`),
which no other thread can observe. Memory is the lock words (`mem : Nat → Int`, 32-bit
two's-complement words read as integers: a word never goes below `-n` with `n` threads, see
`scripts/pthread-hw` `x2_lockword`); `buf t` is thread `t`'s store buffer (oldest first; the
only plain stores are the unlock's stores of 1, so an entry is the lock address).

* `sc`: the unlock's store writes memory;
* `tso`: it enters the buffer; a flush writes the oldest entry; `lock decl` and `xchg` need an
  empty buffer (locked instructions drain it); the spin loop's load sees the thread's own
  newest buffered store, else memory;
* `xl`: as `tso`. XL differs from x86-TSO only on non-temporal and string stores and on
  tearable (misaligned or line-crossing) accesses; the lock word is an aligned 4-byte
  write-back word, so XL's flush order is FIFO here (`Silmaril.X86.MemoryModel.Xl`).

`gh` is an **auxiliary (ghost) variable**: the abstract state of each spin lock (`SpinSt`),
updated at the linearization points and never read by the code. glibc's spin lock does not
record its owner; POSIX's undefined behaviour (unlocking a lock one does not hold) is a
property of the abstract state, so the model needs it to say when a call is undefined. A
concrete configuration **faults** when some thread's next call (in the abstract view) is
undefined; the model makes no claims after that (no steps from a faulting configuration).

**Linearization points**: a successful `lock decl` (lock), the `xchg` (trylock), and for
unlock the **flush** of its store (under `sc` the store itself). Until its store has left the
buffer, an unlocking thread is, in the abstract view, still inside `pthread_spin_unlock`:
the abstract script of thread `t` is its pending unlocks followed by its concrete script
(`absTh`). This is the TSO placement of a plain-store release: placing it at the store would
make a `trylock` that still reads the old word (and returns `EBUSY`) contradict a lock that
the specification already freed.

`pthread_spin_init` is the same code as `pthread_spin_unlock` (a plain store of 1). Under
`tso` it is not linearizable as an atomic initialisation in the most general client (another
thread can take the lock through the old word while the store is buffered, and the flush then
frees it under the holder); POSIX requires initialisation to happen before other uses, which
the most general client does not express. Initialisation is therefore outside the model: the
start configuration already has its locks initialised.

## The other functions

`Task.glibcObl` states the obligation for every other function of `Pthread/Defs`, over a
`CodeModel` (the concrete model of a function's code under each memory model, supplied by the
MT x86 process model). Stated, not proved.
-/

@[expose] public section

namespace Silmaril.Process.Mt.Pthread.Glibc

open Silmaril.Process.Mt.Csl
open Silmaril.X86.MemoryModel.Lattice (Name)

/-! ## The pin -/

/-- A pinned shared object. -/
structure Pin where
  name : String
  version : String
  sha256 : String
  buildId : String

/-- **The glibc pin.** -/
def pin : Pin where
  name := "libc.so.6"
  version := "2.39-0ubuntu8.9"
  sha256 := "3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf"
  buildId := "a4a7992a8e66555c8141ab2a08a8465ff6e0ea65"

/-- The pthread functions of the pin with their addresses (`nm -D`, default versions). -/
def syms : List (String × Nat) :=
  [("pthread_create", 0x9cca0), ("pthread_join", 0x9e710), ("pthread_detach", 0x9dd50),
   ("pthread_exit", 0x9ddc0), ("pthread_self", 0xa37b0),
   ("pthread_mutex_lock", 0xa00d0), ("pthread_mutex_trylock", 0xa0fd0),
   ("pthread_mutex_unlock", 0xa1b50),
   ("pthread_cond_wait", 0x9b6c0), ("pthread_cond_signal", 0x9b0a0),
   ("pthread_cond_broadcast", 0x9ac40),
   ("pthread_rwlock_rdlock", 0xa27b0), ("pthread_rwlock_wrlock", 0xa3310),
   ("pthread_rwlock_unlock", 0xa3140),
   ("pthread_once", 0xa20a0),
   ("pthread_key_create", 0x9e900), ("pthread_key_delete", 0x9e960),
   ("pthread_getspecific", 0x9e690), ("pthread_setspecific", 0xa3ee0),
   ("pthread_spin_lock", 0xa41d0), ("pthread_spin_trylock", 0xa41f0),
   ("pthread_spin_unlock", 0xa4210), ("pthread_spin_init", 0xa4210),
   ("pthread_barrier_wait", 0x9a710),
   ("sem_wait", 0xa50e0), ("sem_trywait", 0xa5120), ("sem_post", 0xa48c0)]

/-- The bytes of `pthread_spin_lock` (`0xa41d0`–`0xa41ec`, without the padding at `0xa41dc`). -/
def spinLockBytes : List Nat :=
  [0xf3, 0x0f, 0x1e, 0xfa, 0x31, 0xc0, 0xf0, 0xff, 0x0f, 0x75, 0x05, 0xc3] ++
  [0xf3, 0x90, 0x39, 0x07, 0x7e, 0xfa, 0xf0, 0xff, 0x0f, 0x75, 0xf5, 0xc3]

/-- The bytes of `pthread_spin_trylock` (`0xa41f0`–`0xa4206`). -/
def spinTrylockBytes : List Nat :=
  [0xf3, 0x0f, 0x1e, 0xfa, 0x31, 0xc9, 0x87, 0x0f, 0x83, 0xf9, 0x01, 0x75, 0x03, 0x31, 0xc0,
   0xc3, 0xb8, 0x10, 0x00, 0x00, 0x00, 0xc3]

/-- The bytes of `pthread_spin_unlock` and `pthread_spin_init` (`0xa4210`–`0xa421d`). -/
def spinUnlockBytes : List Nat :=
  [0xf3, 0x0f, 0x1e, 0xfa, 0xc7, 0x07, 0x01, 0x00, 0x00, 0x00, 0x31, 0xc0, 0xc3]

/-! ## Memory models of the implementation machines -/

/-- The memory models the implementation machines run under. -/
inductive Pol where
  | sc
  | tso
  | xl
  deriving DecidableEq, Repr

/-- Their names in the lattice. -/
def Pol.name : Pol → Name
  | .sc => .sc
  | .tso => .tso
  | .xl => .xl

/-- Stores are buffered. -/
def Pol.buffered : Pol → Bool
  | .sc => false
  | _ => true

/-! ## The spin lock's most general client -/

/-- The trivial store over pthread states (the most general client has no plain steps). -/
def pstore : Store PSt Unit Unit := ⟨fun _ _ => none⟩

/-- The spin-lock calls of a script entry `[op, s]`: `1` lock, `2` trylock, `3` unlock;
anything else is undefined. -/
def spinOp (args : List Nat) : Option (PrimSpec PSt) :=
  match arg args 0 with
  | 1 => some spinLock
  | 2 => some spinTrylock
  | 3 => some spinUnlock
  | _ => none

/-- **The spin lock's specification as one primitive**: the call `[op, s]` is the spec of
`op` on lock `s` (`Pthread/Defs`). -/
def spinSpec : PrimSpec PSt where
  fault t args m := match spinOp args with
    | some sp => sp.fault t [arg args 1] m
    | none => True
  step t args m r m' := ∃ sp, spinOp args = some sp ∧ sp.step t [arg args 1] m r m'

/-- Where a thread is. -/
inductive Pc where
  | idle
  | dec
  | spin
  deriving DecidableEq, Repr

/-- **A configuration of the spin-lock machine.** -/
structure SConf where
  /-- Thread `t`: its remaining script (with the current call first) and position. -/
  th : Nat → Option (List (List Nat) × Pc)
  /-- The lock words. -/
  mem : Nat → Int
  /-- The store buffers: lock addresses of pending stores of 1, oldest first. -/
  buf : Nat → List Nat
  /-- The abstract lock states (auxiliary). -/
  gh : Nat → SpinSt

/-- The script thread `t` stands for: its pending unlocks, then its script. -/
def absTh (c : SConf) : Nat → Option (List (List Nat)) :=
  fun t => (c.th t).map fun p => (c.buf t).map (fun a => [3, a]) ++ p.1

/-- What thread `t` reads at `a`: its newest buffered store, else memory. -/
def view (c : SConf) (t a : Nat) : Int := if a ∈ c.buf t then 1 else c.mem a

/-- Some thread's next call (in the abstract view) is undefined. -/
def SConf.Fault (c : SConf) : Prop :=
  ∃ t s, absTh c t = some s ∧ ∃ args rest, s = args :: rest ∧ spinSpec.fault t args { thr := fun _ => none, spin := c.gh }

/-- Update thread `t`. -/
def setTh (c : SConf) (t : Nat) (x : List (List Nat) × Pc) : Nat → Option (List (List Nat) × Pc) :=
  Heap.upd c.th t (some x)

/-- **One step of the spin-lock machine under `pol`.** -/
inductive SStep (pol : Pol) : SConf → SConf → Prop
  /-- Enter `pthread_spin_lock` (`endbr64; xor %eax,%eax`). -/
  | enter {c t a rest} (h : c.th t = some ([1, a] :: rest, .idle)) :
      SStep pol c { c with th := setTh c t ([1, a] :: rest, .dec) }
  /-- `lock decl` from 1: acquired, return 0. -/
  | decOk {c t a rest} (h : c.th t = some ([1, a] :: rest, .dec)) (hb : c.buf t = [])
      (hv : c.mem a = 1) :
      SStep pol c { c with th := setTh c t (rest, .idle), mem := Heap.upd c.mem a 0,
                           gh := Heap.upd c.gh a (.held t) }
  /-- `lock decl` otherwise: spin. -/
  | decFail {c t a rest} (h : c.th t = some ([1, a] :: rest, .dec)) (hb : c.buf t = [])
      (hv : c.mem a ≠ 1) :
      SStep pol c { c with th := setTh c t ([1, a] :: rest, .spin), mem := Heap.upd c.mem a (c.mem a - 1) }
  /-- `pause; cmp %eax,(%rdi); jle`: a positive word ends the loop (retry `lock decl`). -/
  | spinRead {c t a rest} (h : c.th t = some ([1, a] :: rest, .spin)) :
      SStep pol c { c with th := setTh c t ([1, a] :: rest, if 0 < view c t a then .dec else .spin) }
  /-- `pthread_spin_trylock`: `xchg` in 0; the old word 1 means acquired (return 0), else
  `EBUSY`. -/
  | xchg {c t a rest} (h : c.th t = some ([2, a] :: rest, .idle)) (hb : c.buf t = []) :
      SStep pol c { c with th := setTh c t (rest, .idle), mem := Heap.upd c.mem a 0,
                           gh := if c.mem a = 1 then Heap.upd c.gh a (.held t) else c.gh }
  /-- `pthread_spin_unlock` under `sc`: the store of 1 writes memory. -/
  | storeSc {c t a rest} (hp : pol.buffered = false) (h : c.th t = some ([3, a] :: rest, .idle)) :
      SStep pol c { c with th := setTh c t (rest, .idle), mem := Heap.upd c.mem a 1,
                           gh := Heap.upd c.gh a .free }
  /-- `pthread_spin_unlock` under `tso`/`xl`: the store of 1 enters the buffer. -/
  | storeBuf {c t a rest} (hp : pol.buffered = true) (h : c.th t = some ([3, a] :: rest, .idle)) :
      SStep pol c { c with th := setTh c t (rest, .idle), buf := Heap.upd c.buf t (c.buf t ++ [a]) }
  /-- A flush of the oldest pending store of thread `t`. -/
  | flush {c t a bs} (hp : pol.buffered = true) (hb : c.buf t = a :: bs) :
      SStep pol c { c with buf := Heap.upd c.buf t bs, mem := Heap.upd c.mem a 1,
                           gh := Heap.upd c.gh a .free }

/-- The lock-word invariant: for an initialised lock, the word is at most 1, and it is 1
exactly when the lock is free. Threads that do not exist have empty buffers; under `sc` every
buffer is empty. -/
def SConf.Inv (pol : Pol) (c : SConf) : Prop :=
  (∀ a, c.gh a ≠ .uninit → c.mem a ≤ 1 ∧ (c.mem a = 1 ↔ c.gh a = .free)) ∧
  (∀ t, c.th t = none → c.buf t = []) ∧
  (pol.buffered = false → ∀ t, c.buf t = [])

/-- **The concrete model** of the spin lock's most general client under `pol`: steps from
configurations that do not fault; a configuration stands for the abstract one whose scripts are
`absTh` and whose spin locks are `gh`. -/
def model (pol : Pol) : Model (TIsa.mgc (S := pstore) spinSpec) where
  Conf := SConf
  step c c' := ¬ c.Fault ∧ SStep pol c c'
  fault c := c.Fault
  abs c C := c.Inv pol ∧ C.th = absTh c ∧ C.mem.spin = c.gh

/-! ## The obligation schema for the other functions -/

/-- **A code model**: for the most general client of `sp`, one configuration type and
abstraction, and the steps of the client running the implementation code under each memory
model of the lattice (supplied by the MT x86 process model running the pinned code). -/
structure CodeModel (sp : PrimSpec PSt) where
  Conf : Type
  step : Name → Conf → Conf → Prop
  fault : Conf → Prop
  abs : Conf → Cfg (TIsa.mgc (S := pstore) sp) → Prop

/-- The model at one memory model. -/
def CodeModel.at {sp : PrimSpec PSt} (X : CodeModel sp) (a : Name) :
    Model (TIsa.mgc (S := pstore) sp) :=
  ⟨X.Conf, X.step a, X.fault, X.abs⟩

/-- The code model's runs grow with the memory model (a model that allows more executions
allows more runs). -/
def CodeModel.Mono {sp : PrimSpec PSt} (X : CodeModel sp) : Prop :=
  ∀ a b, a.le b = true → ∀ c c', X.step a c c' → X.step b c c'

/-- The pthread functions with obligations, and their specifications. Two-step functions
(`pthread_cond_wait`, `pthread_once`, `pthread_barrier_wait`) are one most general client over
both halves: `[0, …]` the first, `[1, …]` the second. -/
inductive Fn where
  | mutexLock | mutexTrylock | mutexUnlock | condWait | condSignal | condBroadcast
  | rwRdlock | rwWrlock | rwUnlock | once | getspecific | setspecific | keyCreate
  | barrierWait | semWait | semTrywait | semPost | join | exit
  deriving DecidableEq, Repr

/-- Two primitives as one: `[0, args…]` is the first, `[1, args…]` the second. -/
def pair (p q : PrimSpec PSt) : PrimSpec PSt where
  fault t args m := (arg args 0 = 0 ∧ p.fault t args.tail m) ∨ (arg args 0 = 1 ∧ q.fault t args.tail m) ∨ 1 < arg args 0
  step t args m r m' := (arg args 0 = 0 ∧ p.step t args.tail m r m') ∨ (arg args 0 = 1 ∧ q.step t args.tail m r m')

/-- The specification of a function. -/
def Fn.spec : Fn → PrimSpec PSt
  | .mutexLock => Pthread.mutexLock
  | .mutexTrylock => Pthread.mutexTrylock
  | .mutexUnlock => Pthread.mutexUnlock
  | .condWait => pair Pthread.condWait Pthread.condResume
  | .condSignal => Pthread.condSignal
  | .condBroadcast => Pthread.condBroadcast
  | .rwRdlock => Pthread.rwRdlock
  | .rwWrlock => Pthread.rwWrlock
  | .rwUnlock => Pthread.rwUnlock
  | .once => pair Pthread.onceBegin Pthread.onceEnd
  | .getspecific => Pthread.getspecific
  | .setspecific => Pthread.setspecific
  | .keyCreate => Pthread.keyCreate
  | .barrierWait => pair Pthread.barArrive Pthread.barDepart
  | .semWait => Pthread.semWait
  | .semTrywait => Pthread.semTrywait
  | .semPost => Pthread.semPost
  | .join => Pthread.join
  | .exit => Pthread.exit

/-- **The glibc obligation** of function `f` at memory model `a`: the code model of the pinned
code (`pin`, `syms`) implements `f`'s specification under `a`. Stated for `a = .tso` and
`a = .xl`; through `CodeModel.sound_mono` they give every model below. -/
def Task.glibcObl (f : Fn) (X : CodeModel f.spec) (a : Name) : Prop :=
  Silmaril.Project.Shapes.Mt.Primitive f.spec (X.at a)

end Silmaril.Process.Mt.Pthread.Glibc
