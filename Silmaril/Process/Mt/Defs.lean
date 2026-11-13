module

public import Silmaril.Process.Memory
public import Silmaril.X86.MemEvent.Defs
public import Mathlib.Logic.Relation

/-!
# A multithreaded process model (first pass)

A process with several threads sharing one address space, generic over three things:

* the **user ISA** `U : UIsa γ` (`Mt/X86` gives the x86 instances): a thread state type and a
  step relation that says what a running thread does next (`UOut`);
* the **memory system** `M : MemSys`: how threads see and update the shared memory. `sc`
  (sequential consistency: one memory) and `tso` (x86-TSO: one FIFO store buffer of byte
  writes per thread) are given here;
* the **trusted primitives** `P : PrimTable γ`: abstract, logically atomic specifications of
  synchronisation primitives (mutexes, recursive locks, atomics, lock-free lists), each run
  as **one** step (`Mt/Prim` has the standard ones);

plus a **base** syscall relation (`Base`) for the system calls the thread layer does not own.

## Threads and configurations

A configuration (`MtCfg`) has a thread table `tid ↦ TRec` (state `run s`, `wait a k`
blocked in `FUTEX_WAIT` on address `a`, or `exited`; and the `clear_child_tid` address), the
memory-system state `ms`, the primitives' abstract state `ps` (lock owners and depths), the
library's ghost state `g`, the **multithreaded-mode bit** `mt` (false until the first
`clone`; glibc's `SINGLE_THREAD_P` and `_IO_FLAGS2_NEED_LOCK` fast paths are read through
it) and the process exit status. A thread's TLS base is part of its state (on x86 the core's
`fsBase`): the kernel layer never reads it.

## What a thread does (`UOut`)

* `step s es m`: a **plain step** (an instruction) that took the thread's memory view to `m`,
  with access list `es` (`some`: the `MemEvent` events of the step; `none`: not known, so a
  memory system must run it as a barrier, synchronised). Under `sc` the events are ignored;
  under `tso` the bytes of the write set go to the thread's store buffer;
* `lib s m g`: a **library-contract step** (as in `Elf.Link.Dyn.Proc`: one call of an
  imported function, from call to return, as its loose contract says): atomic, on the
  shared memory and the library ghost, with the thread synchronised;
* `sys nr args k child`: a system call; `k w` resumes the thread with return value `w`,
  `child` is the state a `clone` child starts in;
* `prim p args k`: a call of trusted primitive `p`, one atomic step of its specification
  (`PrimSpec`), with the thread synchronised;
* `stop`: a fault (undefined behaviour, an unmodelled instruction).

## The kernel layer (`MtStep`)

The arms follow Linux on x86-64, for the calls the thread layer owns:

* `clone` (56) with the flag word of glibc's (`0x3d0f00`) or musl's (`0x7d0f00`)
  `pthread_create`: a fresh tid `t'` (`0 < t' < pidMax`), the child in the ISA's `child`
  state (on x86: the parent's registers with `rax = 0`, the new stack, `fsBase = tls`), the
  tid written as 4 bytes at `ptid` (`CLONE_PARENT_SETTID`), `ctid` recorded
  (`CLONE_CHILD_CLEARTID`), `mt := true`;
* `futex` (202): `FUTEX_WAIT[_PRIVATE]` checks the 4-byte word and blocks in one step, or
  returns `-EAGAIN`; `FUTEX_WAKE[_PRIVATE]` wakes any list of at most `n` waiters and returns
  their number; a waiter may wake spuriously (returns `0`). The address must be 4-aligned;
* `exit` (60): the thread exits; if other threads live and its `clear_child_tid` word is
  writable, the word is set to `0` and at most one waiter on it is woken (Linux
  `mm_release`); when no thread is left, the process exits with the code;
* `exit_group` (231): the process exits; `set_tid_address` (218): records `clear_child_tid`
  and returns the tid; `gettid` (186): returns the tid;
* every other number goes to `base`. `clone3` (435) is reserved and has no step.

System calls, primitives and library steps need the calling thread **synchronised**
(`MemSys.synced`; under `tso`: its store buffer drained), as a locked instruction or a
`syscall` drains it on x86. The memory system's silent steps (store-buffer flushes) are
the `flush` arm. The scheduler is nondeterministic: any thread that can step may.

Requests outside these shapes (other clone flags, other futex ops, unaligned futex words,
unwritable `ptid`) have **no** step: the model makes no claim about them. A thread that
can do nothing, and is not faulting, is blocked (a lock held by another thread, for
example).

## The single-threaded view (`SoloStep`)

One thread, SC memory, no `clone`/`futex`: the single-threaded process. `Mt/Thms` proves it
is the one-thread case of `MtStep` (`solo_step`, `solo_reach`, `solo_must`).

**Trusted** (assumptions a theorem over `MtStep` rests on): the ISA, the base relation, the
primitive specifications (each primitive is assumed to implement its spec, as one atomic
step) and the kernel arms above, written from the Linux man pages (`clone(2)`, `futex(2)`,
`exit(2)`, `set_tid_address(2)`), not checked against the kernel source.
-/

@[expose] public section

namespace Silmaril.Process.Mt

open Silmaril.X86 (Word)
open Silmaril.X86.MemEvent (Event)

/-! ## Byte helpers -/

/-- The `n` low bytes of `w`, little-endian. -/
def le (n : Nat) (w : Word) : List Byte := (List.range n).map fun i => (w >>> (8 * i)).setWidth 8

/-- A little-endian byte list as a number. -/
def decLE : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decLE bs

/-- Replace one entry of a function. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

/-! ## Memory systems -/

/-- **A memory system**: how threads see and update the shared memory. `view s t` is thread
`t`'s view; `user t es s m s'` commits a plain step of `t` that took its view to `m`, with
access list `es`; `synced s t` says `t` has no pending writes, so that atomic steps act on the
shared memory `mem s` and replace it (`put`); `silent` steps are the system's own (store-buffer
flushes). -/
structure MemSys where
  S : Type
  view : S → Nat → Memory
  user : Nat → Option (List Event) → S → Memory → S → Prop
  synced : S → Nat → Prop
  mem : S → Memory
  put : S → Memory → S
  silent : S → S → Prop
  /-- A synchronised thread sees the shared memory. -/
  view_synced : ∀ {s t}, synced s t → view s t = mem s

/-- **Sequential consistency**: one memory, every thread sees it, writes are immediate. -/
def sc : MemSys where
  S := Memory
  view m _ := m
  user _ _ _ m s' := s' = m
  synced _ _ := True
  mem m := m
  put _ m := m
  silent _ _ := False
  view_synced _ := rfl

/-- A pending write: address and bytes. -/
abbrev BufEntry := Nat × List Byte

/-- The TSO memory-system state: the shared memory and one FIFO store buffer per thread
(oldest first). -/
structure TsoS where
  mem : Memory
  buf : Nat → List BufEntry

/-- Apply pending writes to a memory (oldest first). -/
def overlay (m : Memory) (b : List BufEntry) : Memory :=
  b.foldl (fun m e => { m with bytes := Memory.install m.bytes e.1 e.2 }) m

/-- The writes of an access list, with their bytes read from the memory after the step. -/
def writesOf (es : List Event) (m : Memory) : List BufEntry :=
  es.filterMap fun e =>
    if e.kind.writes then some (e.addr, (List.range e.size).map fun i => m.bytes.getD (e.addr + i) 0)
    else none

/-- The access list needs a drained buffer: a locked access or a fence. -/
def barrier (es : List Event) : Bool :=
  es.any fun e => e.locked || match e.kind with | .fence _ => true | _ => false

/-- **x86-TSO** with byte store buffers. A thread sees the shared memory overlaid with its own
buffer. A plain step of a known access list puts the bytes of its write set at the end of the
thread's buffer (in event order); a locked or fencing step, a step with no access list and
every atomic step need an empty buffer and write the shared memory directly. A silent step
writes the oldest entry of some buffer to the shared memory. Mapping changes happen only in
synchronised steps. -/
def tso : MemSys where
  S := TsoS
  view s t := overlay s.mem (s.buf t)
  user t es s m s' :=
    m.regions = s.mem.regions ∧
    match es with
    | some es =>
      if barrier es then s.buf t = [] ∧ s' = { s with mem := m }
      else s' = { s with buf := upd s.buf t (s.buf t ++ writesOf es m) }
    | none => s.buf t = [] ∧ s' = { s with mem := m }
  synced s t := s.buf t = []
  mem s := s.mem
  put s m := { s with mem := m }
  silent s s' := ∃ t e rest, s.buf t = e :: rest ∧
    s' = { mem := { s.mem with bytes := Memory.install s.mem.bytes e.1 e.2 }, buf := upd s.buf t rest }
  view_synced {s t} h := by simp only [h, overlay, List.foldl_nil]

/-! ## Trusted primitives -/

/-- The primitives' abstract state: the owner and depth of each held lock (by address). -/
structure PrimSt where
  locks : Nat → Option (Nat × Nat) := fun _ => none

/-- What a primitive, a library step or the kernel sees of the process: the shared memory,
the primitives' state, the library ghost and the multithreaded-mode bit. -/
structure Sh (γ : Type) where
  mem : Memory
  ps : PrimSt
  g : γ
  mt : Bool

/-- **A trusted primitive**, as an abstract, logically atomic specification, for the calling
thread `tid` with arguments `args`. Outside `pre` the call is a fault (undefined behaviour);
under it, the call is one atomic step to any `post` outcome (a result and a new shared
state); with no outcome the thread is blocked (a held lock). Implementations are not modelled
here: that each implements its spec under a memory model is an explicit assumption,
discharged separately. `post` must keep `mt` (the step rule ignores it). `fp` is the
primitive's memory footprint; the step rule does not enforce it (`PrimSpec.FpOk` states it). -/
structure PrimSpec (γ : Type) where
  pre : Nat → List Word → Sh γ → Prop
  post : Nat → List Word → Sh γ → Word → Sh γ → Prop
  /-- The bytes of memory the primitive may read or write (for race freedom: a plain access of
  another thread to them races with the call). Default: all of memory. -/
  fp : Nat → List Word → Nat → Prop := fun _ _ _ => True

/-- The specification respects its footprint: outside `fp` the call changes no byte (nor the
mapping list), and its precondition depends on memory only through `fp`. Asked of primitives,
not assumed by `MtStep`. -/
def PrimSpec.FpOk {γ : Type} (sp : PrimSpec γ) : Prop :=
  (∀ t args sh ret sh2, sp.post t args sh ret sh2 → sh2.mem.regions = sh.mem.regions ∧
    ∀ a, ¬ sp.fp t args a → sh2.mem.bytes[a]? = sh.mem.bytes[a]?) ∧
  ∀ t args (sh sh' : Sh γ), sh'.ps = sh.ps → sh'.g = sh.g → sh'.mt = sh.mt →
    sh'.mem.regions = sh.mem.regions → (∀ a, sp.fp t args a → sh'.mem.bytes[a]? = sh.mem.bytes[a]?) →
    (sp.pre t args sh ↔ sp.pre t args sh')

/-- The primitives, by number. -/
abbrev PrimTable (γ : Type) := Nat → Option (PrimSpec γ)

/-! ## User ISAs -/

/-- What a running thread does next. -/
inductive UOut (σ γ : Type) where
  /-- A plain step that took the thread's memory view to `m`, with access list `es`. -/
  | step (s : σ) (es : Option (List Event)) (m : Memory)
  /-- A library-contract step: atomic, on the shared memory and the library ghost. -/
  | lib (s : σ) (m : Memory) (g : γ)
  /-- A system call. -/
  | sys (nr : Nat) (args : List Word) (k : Word → σ) (child : σ)
  /-- A call of trusted primitive `p`. -/
  | prim (p : Nat) (args : List Word) (k : Word → σ)
  /-- A fault. -/
  | stop

/-- **A user ISA**: thread states, and what thread `tid` in state `s`, seeing memory `m`, with
library ghost `g`, may do next. `ended g` is the exit status the library ghost records once
the library has ended the process (`Elf.Link.Dyn.Proc`'s `done`), `none` otherwise. -/
structure UIsa (γ : Type) where
  St : Type
  step : Nat → St → Memory → γ → UOut St γ → Prop
  ended : γ → Option Nat := fun _ => none

/-! ## Configurations -/

/-- The scheduling state of a thread. -/
inductive TSt (σ : Type) where
  | run (s : σ)
  /-- Blocked in `FUTEX_WAIT` on address `a`; `k` resumes it. -/
  | wait (a : Nat) (k : Word → σ)
  | exited

/-- A thread-table entry: its state and its `clear_child_tid` address. -/
structure TRec (σ : Type) where
  st : TSt σ
  ctid : Option Nat := none

/-- **A process configuration.** -/
structure MtCfg (σ γ S : Type) where
  th : Nat → Option (TRec σ)
  ms : S
  ps : PrimSt
  g : γ
  /-- Multithreaded mode: false until the first `clone`. -/
  mt : Bool
  status : Option Nat

/-- The configuration's shared state, as primitives and the kernel see it. -/
def MtCfg.sh {σ γ : Type} (M : MemSys) (C : MtCfg σ γ M.S) : Sh γ := ⟨M.mem C.ms, C.ps, C.g, C.mt⟩

/-- The process is running: no exit status, and the library has not ended it. -/
def MtCfg.Live {γ : Type} (U : UIsa γ) {S : Type} (C : MtCfg U.St γ S) : Prop :=
  C.status = none ∧ U.ended C.g = none

/-- The base syscall relation: number, calling thread, arguments, shared memory and ghost;
return value, new memory and ghost. -/
abbrev Base (γ : Type) := Nat → Nat → List Word → Memory → γ → Word → Memory → γ → Prop

/-- The base relation with no calls: every other system call has no step. -/
def Base.none (γ : Type) : Base γ := fun _ _ _ _ _ _ _ _ => False

/-! ## Kernel constants (x86-64 Linux) -/

def nrClone : Nat := 56
def nrExit : Nat := 60
def nrGettid : Nat := 186
def nrFutex : Nat := 202
def nrSetTid : Nat := 218
def nrExitGroup : Nat := 231
def nrClone3 : Nat := 435

/-- The numbers the thread layer owns. -/
def threadNr (n : Nat) : Prop :=
  n = nrClone ∨ n = nrExit ∨ n = nrGettid ∨ n = nrFutex ∨ n = nrSetTid ∨ n = nrExitGroup ∨
    n = nrClone3

instance (n : Nat) : Decidable (threadNr n) := by unfold threadNr; infer_instance

/-- `pthread_create`'s `clone` flag words: musl's (`CLONE_VM | CLONE_FS | CLONE_FILES |
CLONE_SIGHAND | CLONE_THREAD | CLONE_SYSVSEM | CLONE_SETTLS | CLONE_PARENT_SETTID |
CLONE_CHILD_CLEARTID | CLONE_DETACHED`) and glibc's (the same without `CLONE_DETACHED`). -/
def cloneMusl : Nat := 0x7d0f00
def cloneGlibc : Nat := 0x3d0f00

def CloneOk (fl : Word) : Prop := fl.toNat = cloneMusl ∨ fl.toNat = cloneGlibc

/-- `FUTEX_WAIT`, `FUTEX_WAIT_PRIVATE`. -/
def WaitOp (op : Word) : Prop := op.toNat = 0 ∨ op.toNat = 128

/-- `FUTEX_WAKE`, `FUTEX_WAKE_PRIVATE`. -/
def WakeOp (op : Word) : Prop := op.toNat = 1 ∨ op.toNat = 129

instance (fl : Word) : Decidable (CloneOk fl) := by unfold CloneOk; infer_instance
instance (op : Word) : Decidable (WaitOp op) := by unfold WaitOp; infer_instance
instance (op : Word) : Decidable (WakeOp op) := by unfold WakeOp; infer_instance

/-- `-EAGAIN`. -/
def errAgain : Word := 0 - 11

/-- Linux's `PID_MAX_LIMIT` on 64-bit. -/
def pidMax : Nat := 2 ^ 22

/-! ## Thread-table operations -/

def TSt.isExited {σ : Type} : TSt σ → Bool
  | .exited => true
  | _ => false

/-- A live thread: present and not exited. -/
def LiveT {σ : Type} (th : Nat → Option (TRec σ)) (t : Nat) : Prop :=
  ∃ r, th t = some r ∧ r.st.isExited = false

/-- Thread `t` waits on address `a`. -/
def Waiting {σ : Type} (th : Nat → Option (TRec σ)) (a t : Nat) : Prop :=
  ∃ r k, th t = some r ∧ r.st = .wait a k

/-- A waiter resumes with `0`. -/
def TRec.wake {σ : Type} (r : TRec σ) : TRec σ :=
  match r.st with
  | .wait _ k => { r with st := .run (k 0) }
  | _ => r

/-- Wake the threads `ws`. -/
def wakeAll {σ : Type} (th : Nat → Option (TRec σ)) (ws : List Nat) : Nat → Option (TRec σ) :=
  fun t => if t ∈ ws then (th t).map TRec.wake else th t

/-- `ws` is a list of at most `n` distinct waiters on `a`. -/
def Wakes {σ : Type} (th : Nat → Option (TRec σ)) (a n : Nat) (ws : List Nat) : Prop :=
  ws.Nodup ∧ ws.length ≤ n ∧ ∀ t ∈ ws, Waiting th a t

open Classical in
/-- The process status after a thread exit: `code` if no thread is left. -/
noncomputable def lastExit {σ : Type} (th : Nat → Option (TRec σ)) (code : Nat) : Option Nat :=
  if ∃ t, LiveT th t then none else some code

/-- Replace thread `t`'s record. -/
def setTh {σ : Type} (th : Nat → Option (TRec σ)) (t : Nat) (r : TRec σ) : Nat → Option (TRec σ) :=
  upd th t (some r)

/-! ## Process steps -/

section
variable {γ : Type} (U : UIsa γ) (M : MemSys) (P : PrimTable γ) (base : Base γ)

/-- **One step of a multithreaded process.** Every thread rule needs a live process and a
running thread `t`; its next action is `U.step t s (view) g`. -/
inductive MtStep : MtCfg U.St γ M.S → MtCfg U.St γ M.S → Prop
  /-- A plain step, committed through the memory system. -/
  | user {C t r s s' es m ms'} (hl : C.Live U) (ht : C.th t = some r) (hr : r.st = .run s)
      (hs : U.step t s (M.view C.ms t) C.g (.step s' es m)) (hm : M.user t es C.ms m ms') :
      MtStep C { C with th := setTh C.th t { r with st := .run s' }, ms := ms' }
  /-- A library-contract step, atomic. -/
  | lib {C t r s s' m g'} (hl : C.Live U) (ht : C.th t = some r) (hr : r.st = .run s)
      (hy : M.synced C.ms t) (hs : U.step t s (M.view C.ms t) C.g (.lib s' m g')) :
      MtStep C { C with th := setTh C.th t { r with st := .run s' }, ms := M.put C.ms m, g := g' }
  /-- A trusted primitive: one atomic step of its specification. -/
  | prim {C t r s p args k sp ret sh2} (hl : C.Live U) (ht : C.th t = some r) (hr : r.st = .run s)
      (hy : M.synced C.ms t) (hs : U.step t s (M.view C.ms t) C.g (.prim p args k))
      (hp : P p = some sp) (hpre : sp.pre t args (C.sh M))
      (hpost : sp.post t args (C.sh M) ret sh2) :
      MtStep C { C with
        th := setTh C.th t { r with st := .run (k ret) }
        ms := M.put C.ms sh2.mem
        ps := sh2.ps
        g := sh2.g }
  /-- `gettid()`. -/
  | gettid {C t r s args k ch} (hl : C.Live U) (ht : C.th t = some r) (hr : r.st = .run s)
      (hy : M.synced C.ms t) (hs : U.step t s (M.view C.ms t) C.g (.sys nrGettid args k ch)) :
      MtStep C { C with th := setTh C.th t { r with st := .run (k (BitVec.ofNat 64 t)) } }
  /-- `set_tid_address(a)`: record `a`, return the tid. -/
  | setTid {C t r s a args k ch} (hl : C.Live U) (ht : C.th t = some r) (hr : r.st = .run s)
      (hy : M.synced C.ms t) (hs : U.step t s (M.view C.ms t) C.g (.sys nrSetTid (a :: args) k ch)) :
      MtStep C { C with th := setTh C.th t { st := .run (k (BitVec.ofNat 64 t)), ctid := some a.toNat } }
  /-- `futex(a, FUTEX_WAIT, v)` with `*a = v`: block, atomically with the check. -/
  | futexBlock {C t r s a op v args k ch} (hl : C.Live U) (ht : C.th t = some r)
      (hr : r.st = .run s) (hy : M.synced C.ms t)
      (hs : U.step t s (M.view C.ms t) C.g (.sys nrFutex (a :: op :: v :: args) k ch))
      (hop : WaitOp op) (hal : a.toNat % 4 = 0)
      (hw : (M.mem C.ms).readBytes a.toNat 4 = some (le 4 v)) :
      MtStep C { C with th := setTh C.th t { r with st := .wait a.toNat k } }
  /-- `futex(a, FUTEX_WAIT, v)` with `*a ≠ v`: `-EAGAIN`. -/
  | futexAgain {C t r s a op v args k ch w} (hl : C.Live U) (ht : C.th t = some r)
      (hr : r.st = .run s) (hy : M.synced C.ms t)
      (hs : U.step t s (M.view C.ms t) C.g (.sys nrFutex (a :: op :: v :: args) k ch))
      (hop : WaitOp op) (hal : a.toNat % 4 = 0)
      (hw : (M.mem C.ms).readBytes a.toNat 4 = some w) (hne : w ≠ le 4 v) :
      MtStep C { C with th := setTh C.th t { r with st := .run (k errAgain) } }
  /-- `futex(a, FUTEX_WAKE, n)`: wake at most `n` waiters on `a`, return how many. -/
  | futexWake {C t r s a op n args k ch ws} (hl : C.Live U) (ht : C.th t = some r)
      (hr : r.st = .run s) (hy : M.synced C.ms t)
      (hs : U.step t s (M.view C.ms t) C.g (.sys nrFutex (a :: op :: n :: args) k ch))
      (hop : WakeOp op) (hal : a.toNat % 4 = 0) (hws : Wakes C.th a.toNat n.toNat ws) :
      MtStep C { C with
        th := setTh (wakeAll C.th ws) t { r with st := .run (k (BitVec.ofNat 64 ws.length)) } }
  /-- A spurious wake-up: a waiter resumes with `0`. -/
  | spurious {C t r a k} (hl : C.Live U) (ht : C.th t = some r) (hr : r.st = .wait a k) :
      MtStep C { C with th := setTh C.th t { r with st := .run (k 0) } }
  /-- `clone(flags, newsp, ptid, ctid, tls)` with `pthread_create`'s flags: a fresh thread. -/
  | clone {C t r s fl sp ptid ctid tls args k ch t' m'} (hl : C.Live U) (ht : C.th t = some r)
      (hr : r.st = .run s) (hy : M.synced C.ms t)
      (hs : U.step t s (M.view C.ms t) C.g (.sys nrClone (fl :: sp :: ptid :: ctid :: tls :: args) k ch))
      (hf : CloneOk fl) (hfresh : C.th t' = none) (h0 : 0 < t') (hmax : t' < pidMax)
      (hpt : (M.mem C.ms).writeBytes ptid.toNat (le 4 (BitVec.ofNat 64 t')) = some m') :
      MtStep C { C with
        th := setTh (setTh C.th t { r with st := .run (k (BitVec.ofNat 64 t')) }) t'
          { st := .run ch, ctid := some ctid.toNat }
        ms := M.put C.ms m', mt := true }
  /-- `exit(code)` while other threads live, with a writable `clear_child_tid` word: clear
  it, wake at most one waiter on it. -/
  | exitClear {C t r s code args k ch a ws m'} (hl : C.Live U) (ht : C.th t = some r)
      (hr : r.st = .run s) (hy : M.synced C.ms t)
      (hs : U.step t s (M.view C.ms t) C.g (.sys nrExit (code :: args) k ch))
      (hct : r.ctid = some a) (hmap : (M.mem C.ms).writeBytes a (le 4 0) = some m')
      (hlive : ∃ u, LiveT (setTh C.th t { r with st := .exited }) u)
      (hws : Wakes (setTh C.th t { r with st := .exited }) a 1 ws) :
      MtStep C { C with th := wakeAll (setTh C.th t { r with st := .exited }) ws, ms := M.put C.ms m' }
  /-- `exit(code)` otherwise; the process exits when no thread is left. -/
  | exitPlain {C t r s code args k ch} (hl : C.Live U) (ht : C.th t = some r)
      (hr : r.st = .run s) (hy : M.synced C.ms t)
      (hs : U.step t s (M.view C.ms t) C.g (.sys nrExit (code :: args) k ch))
      (hnc : ∀ a, r.ctid = some a → ((M.mem C.ms).writeBytes a (le 4 0)).isSome →
        ¬ ∃ u, LiveT (setTh C.th t { r with st := .exited }) u) :
      MtStep C { C with
        th := setTh C.th t { r with st := .exited }
        status := lastExit (setTh C.th t { r with st := .exited }) (code.toNat % 256) }
  /-- `exit_group(code)`. -/
  | exitGroup {C t r s code args k ch} (hl : C.Live U) (ht : C.th t = some r)
      (hr : r.st = .run s) (hy : M.synced C.ms t)
      (hs : U.step t s (M.view C.ms t) C.g (.sys nrExitGroup (code :: args) k ch)) :
      MtStep C { C with status := some (code.toNat % 256) }
  /-- Any other system call: the base relation. -/
  | base {C t r s nr args k ch ret m' g'} (hl : C.Live U) (ht : C.th t = some r)
      (hr : r.st = .run s) (hy : M.synced C.ms t)
      (hs : U.step t s (M.view C.ms t) C.g (.sys nr args k ch)) (hn : ¬ threadNr nr)
      (hb : base nr t args (M.mem C.ms) C.g ret m' g') :
      MtStep C { C with th := setTh C.th t { r with st := .run (k ret) }, ms := M.put C.ms m', g := g' }
  /-- A silent step of the memory system (a store-buffer flush). -/
  | flush {C ms'} (hf : M.silent C.ms ms') : MtStep C { C with ms := ms' }

/-- Process reachability. -/
abbrev MtReach : MtCfg U.St γ M.S → MtCfg U.St γ M.S → Prop :=
  Relation.ReflTransGen (MtStep U M P base)

/-- **A fault**: in a live process, some running thread's next action is `stop`, or a call
of a primitive that is unknown or outside its precondition. -/
def MtFault (C : MtCfg U.St γ M.S) : Prop :=
  C.Live U ∧ ∃ t r s, C.th t = some r ∧ r.st = .run s ∧
    (U.step t s (M.view C.ms t) C.g .stop ∨
      ∃ p args k, U.step t s (M.view C.ms t) C.g (.prim p args k) ∧
        ∀ sp, P p = some sp → ¬ sp.pre t args (C.sh M))

end

/-- A process with the single running thread `tid` in state `s`. -/
def MtCfg.init {σ γ S : Type} (tid : Nat) (s : σ) (ms : S) (g : γ) : MtCfg σ γ S :=
  ⟨fun t => if t = tid then some { st := .run s } else none, ms, {}, g, false, none⟩

/-! ## Demonic reachability over a step relation with faults -/

/-- **Demonic reachability**: every run from `a` avoids faults, terminates, and reaches `Q`
(the analogue of `RelIsa.Must` for a step relation `S` with a fault predicate `F`; a state
with no successor and no fault is blocked, and satisfies `SMust` vacuously). -/
inductive SMust {α : Type} (S : α → α → Prop) (F : α → Prop) (Q : α → Prop) : α → Prop
  | done {a : α} : Q a → SMust S F Q a
  | step {a : α} : ¬ F a → (∀ b, S a b → SMust S F Q b) → SMust S F Q a

/-! ## The single-threaded view -/

/-- A single-threaded process: its state, memory, primitive state, ghost and exit status. -/
structure SoloCfg (σ γ : Type) where
  st : σ
  mem : Memory
  ps : PrimSt
  g : γ
  status : Option Nat

section
variable {γ : Type} (U : UIsa γ) (P : PrimTable γ) (base : Base γ) (tid : Nat)

/-- The shared state of a single-threaded process (multithreaded mode off). -/
def SoloCfg.sh {σ : Type} (x : SoloCfg σ γ) : Sh γ := ⟨x.mem, x.ps, x.g, false⟩

/-- The single-threaded process is running. -/
def SoloCfg.Live (x : SoloCfg U.St γ) : Prop := x.status = none ∧ U.ended x.g = none

/-- **Steps of a single-threaded process** with thread id `tid`, on one memory: no `clone`,
no `futex`; `set_tid_address` returns the tid and records nothing (with one thread the
`clear_child_tid` write never happens); `exit` ends the process. -/
inductive SoloStep : SoloCfg U.St γ → SoloCfg U.St γ → Prop
  | user {x s' es m} (hl : x.Live U) (hs : U.step tid x.st x.mem x.g (.step s' es m)) :
      SoloStep x { x with st := s', mem := m }
  | lib {x s' m g'} (hl : x.Live U) (hs : U.step tid x.st x.mem x.g (.lib s' m g')) :
      SoloStep x { x with st := s', mem := m, g := g' }
  | prim {x p args k sp ret sh2} (hl : x.Live U) (hs : U.step tid x.st x.mem x.g (.prim p args k))
      (hp : P p = some sp) (hpre : sp.pre tid args x.sh) (hpost : sp.post tid args x.sh ret sh2) :
      SoloStep x { x with st := k ret, mem := sh2.mem, ps := sh2.ps, g := sh2.g }
  | gettid {x args k ch} (hl : x.Live U) (hs : U.step tid x.st x.mem x.g (.sys nrGettid args k ch)) :
      SoloStep x { x with st := k (BitVec.ofNat 64 tid) }
  | setTid {x a args k ch} (hl : x.Live U)
      (hs : U.step tid x.st x.mem x.g (.sys nrSetTid (a :: args) k ch)) :
      SoloStep x { x with st := k (BitVec.ofNat 64 tid) }
  | exit {x code args k ch} (hl : x.Live U)
      (hs : U.step tid x.st x.mem x.g (.sys nrExit (code :: args) k ch)) :
      SoloStep x { x with status := some (code.toNat % 256) }
  | exitGroup {x code args k ch} (hl : x.Live U)
      (hs : U.step tid x.st x.mem x.g (.sys nrExitGroup (code :: args) k ch)) :
      SoloStep x { x with status := some (code.toNat % 256) }
  | base {x nr args k ch ret m' g'} (hl : x.Live U) (hs : U.step tid x.st x.mem x.g (.sys nr args k ch))
      (hn : ¬ threadNr nr) (hb : base nr tid args x.mem x.g ret m' g') :
      SoloStep x { x with st := k ret, mem := m', g := g' }

/-- A fault of the single-threaded process. -/
def SoloFault (x : SoloCfg U.St γ) : Prop :=
  x.Live U ∧ (U.step tid x.st x.mem x.g .stop ∨
    ∃ p args k, U.step tid x.st x.mem x.g (.prim p args k) ∧ ∀ sp, P p = some sp → ¬ sp.pre tid args x.sh)

/-- The state never requests `clone` or `futex`. -/
def NoThreadSys (x : SoloCfg U.St γ) : Prop :=
  ∀ nr args k ch, U.step tid x.st x.mem x.g (.sys nr args k ch) → nr ≠ nrClone ∧ nr ≠ nrFutex

end

/-- The SC process `C` is the single-threaded process `x` with thread id `tid`: one thread,
running `x.st` (or exited, once the process has exited), single-threaded mode, and `x`'s
memory, primitive state, ghost and status. -/
def SoloRel {σ γ : Type} (tid : Nat) (x : SoloCfg σ γ) (C : MtCfg σ γ sc.S) : Prop :=
  C.ms = x.mem ∧ C.ps = x.ps ∧ C.g = x.g ∧ C.mt = false ∧ C.status = x.status ∧
    (∀ t, t ≠ tid → C.th t = none) ∧
    ∃ r, C.th tid = some r ∧ (r.st = .run x.st ∨ (x.status.isSome ∧ r.st = .exited))

end Silmaril.Process.Mt
