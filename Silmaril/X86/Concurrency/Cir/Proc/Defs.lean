module

public import Silmaril.X86.Concurrency.Cir.Csl.Defs

/-!
# Process-level threads for CIR: a multithreaded process model and the lowering of CIR sync

LPS (silmaril's port of
rocq-linux-process-semantics) has one task: `clone` and `futex` are pending arms, and the
bridge proves that a process-safe program never reaches them (`LpsBridge.no_thread_of_psafe`).
This module is an extension: a small multithreaded process model whose kernel
layer handles exactly the thread syscalls, and a refinement showing that CIR's `spawn`, `join`,
`futexWait` and `futexWake` are implemented by them.

## The process model (`PStep`)

The model is generic over a **user ISA** (`UIsa`): a thread state `St` and a step relation
indexed by the thread pointer, with three kinds of actions (`UAct`):

* `tau s'`: a silent step;
* `mem l s'`: a **CIR memory label** `l` (`Lab.plain`: loads, stores, locked RMWs, fences,
  `local` blocks) acting on the shared memory, judged as in the SC machine (`okH`, `updH`);
* `sys nr args k child`: a syscall request; `k w` is the state resumed with return value `w`,
  and `child` the state a `clone` child starts in.

So the process model speaks CIR's labels: a user ISA is anything that can be translated to
CIR labels (x86 through the litmus lowering, or CIR itself, `pIsa`).

A configuration (`PCfg`) has a **thread table** `tid ↦ TRec` (state `run`/`wait a k`/`exited`,
the per-thread **thread pointer** `tp` — the TLS base — and the `clear_child_tid` address),
one **shared** cell heap (the `Heap`; `CLONE_VM`), and the process exit status. The kernel
layer handles:

* `clone` (56) with the flag word of musl's `pthread_create` (`0x7d0f00`, read in musl 1.2.4
  `src/thread/pthread_create.c:243`) or glibc's (`0x3d0f00`): a fresh tid, the child's `tp` is
  the `tls` argument (`CLONE_SETTLS`), the tid is written at `ptid` (`CLONE_PARENT_SETTID`),
  the child records `ctid` (`CLONE_CHILD_CLEARTID`), the parent gets the tid. x86-64 argument
  order: `flags, newsp, ptid, ctid, tls`;
* `futex` (202) `WAIT` (op `0`/`128`, the latter `FUTEX_PRIVATE_FLAG`; one process, so the
  two coincide): check-and-block in one step, `-EAGAIN` on a mismatch; `WAKE` (op `1`/`129`):
  wakes any list of at most `n` waiters and returns their number; waiters may also wake
  spuriously with `0`;
* `exit` (60): the thread exits; if other threads are alive and `ctid` is mapped, it is
  cleared to `0` and at most one waiter on it is woken (Linux `mm_release`, which clears only
  when the address space has other users); if no thread is left, the process exits;
* `exit_group` (231), `set_tid_address` (218), `gettid` (186);
* every other number is delegated to a **base** single-threaded syscall relation (`Base`),
  the slot where LPS's table goes; `clone3` (435) is reserved and has no step.

Unmodelled requests (other flag words, other futex ops, unmapped words) have no step. The
memory is SC (one heap); weak memory is CIR's job (the buffered machines), and every syscall
is a full barrier there (`Lab.drains`).

## The process IR (`PStmt`, `pIsa`)

`PStmt` is CIR's spawn/join-free core (`cir s` for one atomic CIR statement) plus `sys dst nr
args child` (a raw syscall; `child` indexes the code table for `clone`), `tp dst` (read the
thread pointer), structured control and an unbounded `whl` loop. `pIsa code` is its user ISA.

## The lowering (`lower`)

* `spawn u` ↦ `clone(0x7d0f00, stk u, &ctl u, &ctl u, tls u)` (the child runs `code u`:
  zero all registers, the body, `exit(0)`, like musl's `__clone` child path);
* `join u` ↦ `r11 := 1; while r11 ≠ 0 { r11 := load ctl u; if r11 ≠ 0 then futex_wait(ctl u,
  r11) }` (glibc's protocol: the kernel clears `ctl u` at the child's exit and wakes);
* `futexWait d a v` ↦ `futex(a, FUTEX_WAIT_PRIVATE, v) → d; d := (d ≠ 0) ? 11 : 0` (the
  kernel returns `-EAGAIN`, CIR `11`);
* `futexWake a n` ↦ `futex(a, FUTEX_WAKE_PRIVATE, n)`.

`ctl u` is CIR's ghost control address `ctlAddr u`; the process initialises it to `1`.
`r11` is the join loop's scratch register (the x86 `syscall` clobbers it anyway): source
programs must not read it (`Stmt.noR .r11`).

## The CIR sync semantics (`SStep`)

An SC machine over the thread steps (`Csl.TStep`) with explicit `spawn`/`join`: a thread is
started by `spawn u` (once), and `join u` waits until thread `u` is started and finished. All
other labels act on the heap as in the `ScStep`.

## The single-threaded view (`SoloStep`)

One thread, no `clone`/`futex`: the bridge to LPS's single-task model (`Proc/Lps`).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir

open Csl (Heap)

/-- A plain memory label: what user code does to shared memory without the kernel (not a
futex call, `spawn` or `join`). -/
def Lab.plain : Lab → Bool
  | .rd .. | .wr .. | .rmw .. | .fence _ | .blk .. => true
  | _ => false

/-- Set an optional register. -/
def Regs.setO (rs : Regs) : Option Reg → Word → Regs
  | none, _ => rs
  | some r, w => rs.set r w

/-- An expression does not read register `r`. -/
def Expr.noR (r : Reg) : Expr → Bool
  | .lit _ => true
  | .reg q => q != r
  | .bin _ a b => a.noR r && b.noR r

/-- A read-modify-write operation does not read `r`. -/
def RmwOp.noR (r : Reg) : RmwOp → Bool
  | .cas e => e.noR r
  | _ => true

/-- A statement does not read register `r`. -/
def Stmt.noR (r : Reg) : Stmt → Bool
  | .skip | .fence _ | .spawn _ | .join _ => true
  | .assign _ e => e.noR r
  | .load _ _ _ _ a => a.noR r
  | .store _ _ _ a v => a.noR r && v.noR r
  | .rmw _ _ _ op a arg => op.noR r && a.noR r && arg.noR r
  | .futexWait _ a v => a.noR r && v.noR r
  | .futexWake a n => a.noR r && n.noR r
  | .local b => !(b.rin.contains r)
  | .seq s t => s.noR r && t.noR r
  | .ite c s t => c.noR r && s.noR r && t.noR r
  | .loop _ c b => c.noR r && b.noR r

end Silmaril.X86.Concurrency.Cir

namespace Silmaril.X86.Concurrency.Cir.Proc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl (Heap TStep upd Star)

/-! ## User ISAs -/

/-- One action of a user thread. -/
inductive UAct (σ : Type) where
  | tau (s : σ)
  | mem (l : Lab) (s : σ)
  | sys (nr : Nat) (args : List Word) (k : Word → σ) (child : σ)

/-- Map the continuation states of an action (the `clone` child is left alone). -/
def UAct.wrap {σ : Type} (f : σ → σ) : UAct σ → UAct σ
  | .tau s => .tau (f s)
  | .mem l s => .mem l (f s)
  | .sys nr a k ch => .sys nr a (fun w => f (k w)) ch

/-- **A user ISA**: thread states and steps, indexed by the thread pointer. -/
structure UIsa where
  St : Type
  step : Word → St → UAct St → Prop

/-! ## Process configurations -/

/-- The scheduling state of a thread. -/
inductive TSt (σ : Type) where
  | run (s : σ)
  /-- Blocked in `FUTEX_WAIT` on cell `a`; `k` resumes it. -/
  | wait (a : Nat) (k : Word → σ)
  | exited

/-- A thread-table entry: its state, its thread pointer (the TLS base) and its
`clear_child_tid` address. -/
structure TRec (σ : Type) where
  st : TSt σ
  tp : Word
  ctid : Option Nat

/-- **A process**: the thread table, the shared heap, the exit status. -/
structure PCfg (σ : Type) where
  th : Nat → Option (TRec σ)
  mem : Heap
  status : Option Nat

/-- A single-threaded syscall relation for the numbers the thread layer does not handle:
number, arguments, memory, return value, new memory. -/
abbrev Base := Nat → List Word → Heap → Word → Heap → Prop

/-- Syscall numbers (x86-64). -/
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

/-- `clone` flag words: musl's `pthread_create` (`CLONE_VM | CLONE_FS | CLONE_FILES |
CLONE_SIGHAND | CLONE_THREAD | CLONE_SYSVSEM | CLONE_SETTLS | CLONE_PARENT_SETTID |
CLONE_CHILD_CLEARTID | CLONE_DETACHED`) and glibc's (the same without `CLONE_DETACHED`). -/
def cloneMusl : Nat := 0x7d0f00
def cloneGlibc : Nat := 0x3d0f00

/-- A supported `clone` flag word. -/
def CloneOk (fl : Word) : Prop := fl.toNat = cloneMusl ∨ fl.toNat = cloneGlibc

/-- `FUTEX_WAIT` and `FUTEX_WAIT_PRIVATE`. -/
def WaitOp (op : Word) : Prop := op.toNat = 0 ∨ op.toNat = 128

/-- `FUTEX_WAKE` and `FUTEX_WAKE_PRIVATE`. -/
def WakeOp (op : Word) : Prop := op.toNat = 1 ∨ op.toNat = 129

/-- `-EAGAIN`. -/
def errAgain : Word := 0 - 11

/-- Linux's default `pid_max` envelope (as in LPS: `PID_MAX_ENVELOPE`). -/
def pidMax : Nat := 2 ^ 22

/-- Write one cell. -/
def heapPut (h : Heap) (a v : Nat) : Heap := fun x => if x = a then some v else h x


/-- The thread has exited. -/
def TSt.isExited {σ : Type} : TSt σ → Bool
  | .exited => true
  | _ => false

/-- A live thread: present and not exited. -/
def Live {σ : Type} (th : Nat → Option (TRec σ)) (t : Nat) : Prop :=
  ∃ r, th t = some r ∧ r.st.isExited = false

/-- Thread `t` waits on cell `a`. -/
def Waiting {σ : Type} (th : Nat → Option (TRec σ)) (a t : Nat) : Prop :=
  ∃ r k, th t = some r ∧ r.st = .wait a k

/-- Wake a thread: a waiter resumes with `0`. -/
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
/-- The process status after a thread exit: exited with `code` if no thread is left. -/
noncomputable def lastExit {σ : Type} (th : Nat → Option (TRec σ)) (code : Nat) : Option Nat :=
  if ∃ t, Live th t then none else some code

/-- Replace thread `t`'s record. -/
def setTh {σ : Type} (th : Nat → Option (TRec σ)) (t : Nat) (r : TRec σ) :
    Nat → Option (TRec σ) :=
  upd th t (some r)

/-! ## Process steps -/

/-- **Steps of a multithreaded process.** Every rule needs a live process (`status = none`);
the user rules need the thread to be running. -/
inductive PStep (I : UIsa) (base : Base) : PCfg I.St → PCfg I.St → Prop
  | tau {C t r s s'} (hl : C.status = none) (ht : C.th t = some r) (hr : r.st = .run s)
      (hs : I.step r.tp s (.tau s')) :
      PStep I base C { C with th := setTh C.th t { r with st := .run s' } }
  | mem {C t r s l s'} (hl : C.status = none) (ht : C.th t = some r) (hr : r.st = .run s)
      (hs : I.step r.tp s (.mem l s')) (hp : l.plain = true)
      (hc : ∀ a, l.Touches a → (C.mem a).isSome) (hok : l.okH C.mem) :
      PStep I base C { C with th := setTh C.th t { r with st := .run s' }, mem := l.updH C.mem }
  /-- `gettid()`. -/
  | gettid {C t r s args k ch} (hl : C.status = none) (ht : C.th t = some r) (hr : r.st = .run s)
      (hs : I.step r.tp s (.sys nrGettid args k ch)) :
      PStep I base C { C with th := setTh C.th t { r with st := .run (k (BitVec.ofNat 64 t)) } }
  /-- `set_tid_address(a)`: record `a` as `clear_child_tid`, return the tid. -/
  | setTid {C t r s a args k ch} (hl : C.status = none) (ht : C.th t = some r)
      (hr : r.st = .run s) (hs : I.step r.tp s (.sys nrSetTid (a :: args) k ch)) :
      PStep I base C
        { C with th := setTh C.th t { r with st := .run (k (BitVec.ofNat 64 t)), ctid := some a.toNat } }
  /-- `futex(a, FUTEX_WAIT, v)` with `*a = v`: block (atomically with the check). -/
  | futexBlock {C t r s a op v args k ch w} (hl : C.status = none) (ht : C.th t = some r)
      (hr : r.st = .run s) (hs : I.step r.tp s (.sys nrFutex (a :: op :: v :: args) k ch))
      (hop : WaitOp op) (hw : C.mem a.toNat = some w) (hlt : w < 2 ^ 32)
      (heq : w = v.toNat % 2 ^ 32) :
      PStep I base C { C with th := setTh C.th t { r with st := .wait a.toNat k } }
  /-- `futex(a, FUTEX_WAIT, v)` with `*a ≠ v`: `-EAGAIN`. -/
  | futexAgain {C t r s a op v args k ch w} (hl : C.status = none) (ht : C.th t = some r)
      (hr : r.st = .run s) (hs : I.step r.tp s (.sys nrFutex (a :: op :: v :: args) k ch))
      (hop : WaitOp op) (hw : C.mem a.toNat = some w) (hlt : w < 2 ^ 32)
      (hne : w ≠ v.toNat % 2 ^ 32) :
      PStep I base C { C with th := setTh C.th t { r with st := .run (k errAgain) } }
  /-- `futex(a, FUTEX_WAKE, n)`: wake at most `n` waiters on `a`, return how many. -/
  | futexWake {C t r s a op n args k ch ws} (hl : C.status = none) (ht : C.th t = some r)
      (hr : r.st = .run s) (hs : I.step r.tp s (.sys nrFutex (a :: op :: n :: args) k ch))
      (hop : WakeOp op) (hws : Wakes C.th a.toNat n.toNat ws) :
      PStep I base C
        { C with th := setTh (wakeAll C.th ws) t { r with st := .run (k (BitVec.ofNat 64 ws.length)) } }
  /-- A spurious wake-up: a waiter resumes with `0`. -/
  | spurious {C t r a k} (hl : C.status = none) (ht : C.th t = some r) (hr : r.st = .wait a k) :
      PStep I base C { C with th := setTh C.th t { r with st := .run (k 0) } }
  /-- `clone(flags, newsp, ptid, ctid, tls)` with a supported flag word: a fresh thread `t'`
  starting in the ISA's child state with thread pointer `tls`; `t'` written at `ptid`. -/
  | clone {C t r s fl sp ptid ctid tls args k ch t'} (hl : C.status = none)
      (ht : C.th t = some r) (hr : r.st = .run s)
      (hs : I.step r.tp s (.sys nrClone (fl :: sp :: ptid :: ctid :: tls :: args) k ch))
      (hf : CloneOk fl) (hfresh : C.th t' = none) (h0 : 0 < t') (hmax : t' < pidMax)
      (hpt : (C.mem ptid.toNat).isSome) :
      PStep I base C
        { C with
          th := setTh (setTh C.th t { r with st := .run (k (BitVec.ofNat 64 t')) }) t'
            ⟨.run ch, tls, some ctid.toNat⟩
          mem := heapPut C.mem ptid.toNat t' }
  /-- `exit(code)` while other threads live, with a mapped `clear_child_tid`: clear it, wake
  at most one waiter on it. -/
  | exitClear {C t r s code args k ch a ws} (hl : C.status = none) (ht : C.th t = some r)
      (hr : r.st = .run s) (hs : I.step r.tp s (.sys nrExit (code :: args) k ch))
      (hct : r.ctid = some a) (hmap : (C.mem a).isSome)
      (hlive : ∃ u, Live (setTh C.th t { r with st := .exited }) u)
      (hws : Wakes (setTh C.th t { r with st := .exited }) a 1 ws) :
      PStep I base C
        { C with th := wakeAll (setTh C.th t { r with st := .exited }) ws, mem := heapPut C.mem a 0 }
  /-- `exit(code)` otherwise; the process exits if no thread is left. -/
  | exitPlain {C t r s code args k ch} (hl : C.status = none) (ht : C.th t = some r)
      (hr : r.st = .run s) (hs : I.step r.tp s (.sys nrExit (code :: args) k ch))
      (hnc : ∀ a, r.ctid = some a → (C.mem a).isSome →
        ¬ ∃ u, Live (setTh C.th t { r with st := .exited }) u) :
      PStep I base C
        { C with th := setTh C.th t { r with st := .exited }
                 status := lastExit (setTh C.th t { r with st := .exited }) (code.toNat % 256) }
  /-- `exit_group(code)`. -/
  | exitGroup {C t r s code args k ch} (hl : C.status = none) (ht : C.th t = some r)
      (hr : r.st = .run s) (hs : I.step r.tp s (.sys nrExitGroup (code :: args) k ch)) :
      PStep I base C { C with status := some (code.toNat % 256) }
  /-- Any other syscall: the base relation. -/
  | base {C t r s nr args k ch ret mem'} (hl : C.status = none) (ht : C.th t = some r)
      (hr : r.st = .run s) (hs : I.step r.tp s (.sys nr args k ch)) (hn : ¬ threadNr nr)
      (hb : base nr args C.mem ret mem') :
      PStep I base C { C with th := setTh C.th t { r with st := .run (k ret) }, mem := mem' }

/-- Process reachability. -/
abbrev PReach (I : UIsa) (base : Base) : PCfg I.St → PCfg I.St → Prop := Star (PStep I base)

/-- A process with one running thread `tid` (thread pointer `tp`) on heap `h`. -/
def PCfg.init {σ : Type} (tid : Nat) (s : σ) (tp : Word) (h : Heap) : PCfg σ :=
  ⟨fun t => if t = tid then some ⟨.run s, tp, none⟩ else none, h, none⟩

/-! ## The single-threaded view -/

/-- A single-threaded process: its state, thread pointer, heap and exit status. -/
structure SoloCfg (σ : Type) where
  st : σ
  tp : Word
  mem : Heap
  status : Option Nat

/-- **Steps of a single-threaded process** with thread id `tid`: no `clone`, no `futex`;
`set_tid_address` returns the tid and records nothing (as in LPS: with one thread, the
`clear_child_tid` write never happens). -/
inductive SoloStep (I : UIsa) (base : Base) (tid : Nat) : SoloCfg I.St → SoloCfg I.St → Prop
  | tau {x s'} (hl : x.status = none) (hs : I.step x.tp x.st (.tau s')) :
      SoloStep I base tid x { x with st := s' }
  | mem {x l s'} (hl : x.status = none) (hs : I.step x.tp x.st (.mem l s')) (hp : l.plain = true)
      (hc : ∀ a, l.Touches a → (x.mem a).isSome) (hok : l.okH x.mem) :
      SoloStep I base tid x { x with st := s', mem := l.updH x.mem }
  | gettid {x args k ch} (hl : x.status = none) (hs : I.step x.tp x.st (.sys nrGettid args k ch)) :
      SoloStep I base tid x { x with st := k (BitVec.ofNat 64 tid) }
  | setTid {x args k ch} (hl : x.status = none) (hs : I.step x.tp x.st (.sys nrSetTid args k ch))
      (hne : args ≠ []) :
      SoloStep I base tid x { x with st := k (BitVec.ofNat 64 tid) }
  | exit {x code args k ch} (hl : x.status = none)
      (hs : I.step x.tp x.st (.sys nrExit (code :: args) k ch)) :
      SoloStep I base tid x { x with status := some (code.toNat % 256) }
  | exitGroup {x code args k ch} (hl : x.status = none)
      (hs : I.step x.tp x.st (.sys nrExitGroup (code :: args) k ch)) :
      SoloStep I base tid x { x with status := some (code.toNat % 256) }
  | base {x nr args k ch ret mem'} (hl : x.status = none) (hs : I.step x.tp x.st (.sys nr args k ch))
      (hn : ¬ threadNr nr) (hb : base nr args x.mem ret mem') :
      SoloStep I base tid x { x with st := k ret, mem := mem' }

/-- The process `C` is the single-threaded process `x` with thread id `tid`: one thread,
running `x.st` (or exited, once the process has exited), with `x`'s heap and status. -/
def SoloRel {σ : Type} (tid : Nat) (x : SoloCfg σ) (C : PCfg σ) : Prop :=
  C.mem = x.mem ∧ C.status = x.status ∧ (∀ t, t ≠ tid → C.th t = none) ∧
    ∃ r, C.th tid = some r ∧ r.tp = x.tp ∧ (r.st = .run x.st ∨ (x.status.isSome ∧ r.st = .exited))

/-- The state never requests `clone` or `futex`. -/
def NoThreadSys (I : UIsa) (tp : Word) (s : I.St) : Prop :=
  ∀ nr args k ch, I.step tp s (.sys nr args k ch) → nr ≠ nrClone ∧ nr ≠ nrFutex ∧ nr ≠ nrClone3

/-! ## The process IR -/

/-- **The process IR**: CIR's sync-free core plus raw syscalls and the thread pointer. -/
inductive PStmt where
  | skip
  /-- One atomic CIR statement (`assign`, `load`, `store`, `rmw`, `fence`, `local`). -/
  | cir (s : Stmt)
  /-- A raw syscall; the result goes to `dst`; `child` is the code-table entry a `clone`
  child runs. -/
  | sys (dst : Option Reg) (nr : Nat) (args : List Expr) (child : Nat)
  /-- Read the thread pointer. -/
  | tp (dst : Reg)
  | seq (p q : PStmt)
  | ite (c : Expr) (p q : PStmt)
  | loop (n : Nat) (c : Expr) (body : PStmt)
  | whl (c : Expr) (body : PStmt)

/-- A process-IR thread state. -/
abbrev PSt := PStmt × Regs

/-- The registers a `clone` child starts with: the parent's, with `rax = 0` and `rsp` the
new stack (argument 1). -/
def childRegs (rs : Regs) (args : List Expr) : Regs :=
  (rs.set .rax 0).set .rsp ((args.getD 1 (.lit 0)).eval rs)

/-- **Steps of a process-IR thread** with code table `code` and thread pointer `tp` (a
relation by recursion on the statement, so inversion is unfolding). -/
def PTStep (code : Nat → PStmt) (tp : Word) : PStmt → Regs → UAct PSt → Prop
  | .skip, _, _ => False
  | .cir s, rs, a =>
    ∃ rs', (TStep s rs none .skip rs' ∧ a = .tau (.skip, rs')) ∨
      ∃ l, TStep s rs (some l) .skip rs' ∧ a = .mem l (.skip, rs')
  | .sys d nr args c, rs, a =>
    a = .sys nr (args.map (·.eval rs)) (fun w => (.skip, Regs.setO rs d w)) (code c, childRegs rs args)
  | .tp d, rs, a => a = .tau (.skip, rs.set d tp)
  | .seq p q, rs, a =>
    (p = .skip ∧ a = .tau (q, rs)) ∨
      ∃ a', PTStep code tp p rs a' ∧ a = a'.wrap (fun x => (.seq x.1 q, x.2))
  | .ite c p q, rs, a => a = .tau (if truthy (c.eval rs) then p else q, rs)
  | .loop 0 c _, rs, a => truthy (c.eval rs) = false ∧ a = .tau (.skip, rs)
  | .loop (n + 1) c b, rs, a =>
    a = .tau (if truthy (c.eval rs) then .seq b (.loop n c b) else .skip, rs)
  | .whl c b, rs, a => a = .tau (if truthy (c.eval rs) then .seq b (.whl c b) else .skip, rs)

/-- **The process-IR user ISA.** -/
def pIsa (code : Nat → PStmt) : UIsa := ⟨PSt, fun tp x a => PTStep code tp x.1 x.2 a⟩

/-! ## The lowering of CIR sync to syscalls -/

/-- Where the lowering puts each thread's stack and TLS block. -/
structure Layout where
  stk : Nat → Nat
  tls : Nat → Nat

/-- The scratch register of the join loop. -/
def scratch : Reg := .r11

/-- `x ≠ 0`. -/
def nz (e : Expr) : Expr := .bin .ne e (.lit 0)

/-- The futex result normalisation: `0 ↦ 0`, anything else (`-EAGAIN`) `↦ 11`. -/
def nrm (d : Reg) : Expr := .bin .and (.lit 11) (.bin .sub (.lit 0) (nz (.reg d)))

/-- `spawn u`: `clone` with musl's flags, `ptid = ctid = ctl u`. -/
def spawnS (L : Layout) (u : Nat) : PStmt :=
  .sys none nrClone
    [.lit cloneMusl, .lit (L.stk u), .lit (ctlAddr u), .lit (ctlAddr u), .lit (L.tls u)] u

/-- The futex wait of the join loop. -/
def jFw (u : Nat) : PStmt := .sys none nrFutex [.lit (ctlAddr u), .lit 128, .reg scratch] 0

/-- The test of the join loop. -/
def jIt (u : Nat) : PStmt := .ite (nz (.reg scratch)) (jFw u) .skip

/-- The load of the join loop. -/
def jLd (u : Nat) : PStmt := .cir (.load scratch .acq 4 .wb (.lit (ctlAddr u)))

/-- The join loop proper. -/
def jW (u : Nat) : PStmt := .whl (nz (.reg scratch)) (.seq (jLd u) (jIt u))

/-- `join u`: wait until the kernel has cleared `ctl u`. -/
def joinS (u : Nat) : PStmt := .seq (.cir (.assign scratch (.lit 1))) (jW u)

/-- `futexWait d a v`. -/
def fwS (d : Reg) (a v : Expr) : PStmt :=
  .seq (.sys (some d) nrFutex [a, .lit 128, v] 0) (.cir (.assign d (nrm d)))

/-- `futexWake a n`. -/
def fkS (a n : Expr) : PStmt := .sys none nrFutex [a, .lit 129, n] 0

/-- **The lowering** of a CIR statement to the process IR. -/
def lower (L : Layout) : Stmt → PStmt
  | .skip => .skip
  | .assign d e => .cir (.assign d e)
  | .load d m sz fl a => .cir (.load d m sz fl a)
  | .store m sz fl a v => .cir (.store m sz fl a v)
  | .rmw d m sz op a arg => .cir (.rmw d m sz op a arg)
  | .fence k => .cir (.fence k)
  | .local b => .cir (.local b)
  | .futexWait d a v => fwS d a v
  | .futexWake a n => fkS a n
  | .spawn u => spawnS L u
  | .join u => joinS u
  | .seq s t => .seq (lower L s) (lower L t)
  | .ite c s t => .ite c (lower L s) (lower L t)
  | .loop n c b => .loop n c (lower L b)

/-- All sixteen registers. -/
def allRegs : List Reg :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- Zero the registers `l`. -/
def zeroAll : List Reg → PStmt
  | [] => .skip
  | r :: l => .seq (.cir (.assign r (.lit 0))) (zeroAll l)

/-- `exit(0)`. -/
def exitS : PStmt := .sys none nrExit [.lit 0] 0

/-- `exit_group(0)`. -/
def exitGroupS : PStmt := .sys none nrExitGroup [.lit 0] 0

/-! ## CIR programs with spawn and join, and their sync semantics -/

/-- A CIR program: thread bodies (thread `0` is the main thread, the others are spawned) and
the initial heap. -/
structure SProg where
  bodies : List Stmt
  heap : Heap

/-- The number of threads. -/
def SProg.N (P : SProg) : Nat := P.bodies.length

/-- Thread `u`'s body. -/
def SProg.body (P : SProg) (u : Nat) : Stmt := P.bodies.getD u .skip

/-- The code a spawned thread runs: zero the registers, the body, `exit(0)`. -/
def childCode (L : Layout) (b : Stmt) : PStmt := .seq (.seq (zeroAll allRegs) (lower L b)) exitS

/-- The main thread's code: the body, `exit_group(0)`. -/
def mainCode (L : Layout) (b : Stmt) : PStmt := .seq (lower L b) exitGroupS

/-- The code table of a lowered program. -/
def SProg.code (P : SProg) (L : Layout) : Nat → PStmt := fun u => childCode L (P.body u)

/-- `a` is a control address (`ctlAddr u` for some `u`). -/
def isCtl (a : Nat) : Bool := decide (0x7f0000 ≤ a) && (a - 0x7f0000) % 64 == 0

/-- The process heap of a lowered program: the control word of every spawnable thread
`1 … N-1` is `1`; elsewhere the program's heap. -/
def SProg.pheap (P : SProg) : Heap := fun a =>
  if (List.range P.N).any (fun u => decide (0 < u) && a == ctlAddr u) then some 1 else P.heap a

/-- **The lowered process**: the main thread `tid0` (thread pointer `tp0`) runs `mainCode`. -/
def SProg.pinit (P : SProg) (L : Layout) (tid0 : Nat) (tp0 : Word) : PCfg PSt :=
  PCfg.init tid0 (mainCode L (P.body 0), Regs.zero) tp0 P.pheap

/-- A configuration of the CIR sync machine. -/
structure SCfg where
  ts : Nat → Stmt × Regs
  started : Nat → Bool
  mem : Heap

/-- **The CIR sync semantics**: SC interleaving of the started threads among `0 … N-1`,
with `spawn u` starting thread `u` (once) and `join u` waiting until `u` has finished. -/
inductive SStep (N : Nat) : SCfg → SCfg → Prop
  | tau {C t s' rs'} (ht : t < N) (hst : C.started t = true)
      (hs : TStep (C.ts t).1 (C.ts t).2 none s' rs') :
      SStep N C { C with ts := upd C.ts t (s', rs') }
  | lab {C t l s' rs'} (ht : t < N) (hst : C.started t = true)
      (hs : TStep (C.ts t).1 (C.ts t).2 (some l) s' rs') (hm : l.isMem = true)
      (hc : ∀ a, l.Touches a → (C.mem a).isSome) (hok : l.okH C.mem) :
      SStep N C { C with ts := upd C.ts t (s', rs'), mem := l.updH C.mem }
  | spawn {C t u s' rs'} (ht : t < N) (hst : C.started t = true)
      (hs : TStep (C.ts t).1 (C.ts t).2 (some (.spawn u)) s' rs') (hu : 0 < u ∧ u < N)
      (hns : C.started u = false) :
      SStep N C { C with ts := upd C.ts t (s', rs'), started := upd C.started u true }
  | join {C t u s' rs'} (ht : t < N) (hst : C.started t = true)
      (hs : TStep (C.ts t).1 (C.ts t).2 (some (.join u)) s' rs') (hu : C.started u = true)
      (hd : (C.ts u).1 = .skip) :
      SStep N C { C with ts := upd C.ts t (s', rs') }

/-- The initial sync configuration: every thread at its body with zero registers, only the
main thread started. -/
def SProg.init (P : SProg) : SCfg := ⟨fun u => (P.body u, Regs.zero), fun u => u == 0, P.heap⟩

/-- Sync reachability. -/
abbrev SReach (P : SProg) : SCfg → SCfg → Prop := Star (SStep P.N)

/-- **Sync safety**: in every reachable configuration, no started thread can take a label
step that touches an unmapped cell, spawns a thread that is not spawnable or already started,
or joins a thread that is not spawnable. (A program certified by the logic touches only cells
it owns or that its invariant holds.) -/
def SProg.SyncSafe (P : SProg) : Prop :=
  ∀ A, SReach P P.init A → ∀ t, t < P.N → A.started t = true → ∀ l s' rs',
    TStep (A.ts t).1 (A.ts t).2 (some l) s' rs' →
      (∀ a, l.Touches a → (A.mem a).isSome) ∧
      (∀ u, l = .spawn u → 0 < u ∧ u < P.N ∧ A.started u = false) ∧
      (∀ u, l = .join u → 0 < u ∧ u < P.N)

/-- **Well-formed for the lowering**: there is a main thread, no thread reads the scratch
register, the heap has no control cell, and every control address is below `2^64`. -/
structure SProg.Wf (P : SProg) : Prop where
  pos : 0 < P.N
  noR : ∀ u, (P.body u).noR scratch = true
  noCtl : ∀ u, P.heap (ctlAddr u) = none
  small : ctlAddr P.N < 2 ^ 64


end Silmaril.X86.Concurrency.Cir.Proc

namespace Silmaril.X86.Concurrency.Cir

/-! ## A static sufficient condition for sync safety -/

/-- Every access is at a literal address in `D` (as the label sees it, modulo `2^64`). -/
def Stmt.litIn (D : List Nat) : Stmt → Bool
  | .load _ _ _ _ (.lit a) | .store _ _ _ (.lit a) _ | .rmw _ _ _ _ (.lit a) _
  | .futexWait _ (.lit a) _ => D.contains (a % 2 ^ 64)
  | .load .. | .store .. | .rmw .. | .futexWait .. => false
  | .local b => (b.ins ++ b.outs).all fun c => D.contains c.1
  | .seq s t | .ite _ s t => s.litIn D && t.litIn D
  | .loop _ _ b => b.litIn D
  | _ => true

/-- Every `join u` names a spawnable thread `0 < u < N`. -/
def Stmt.joinsIn (N : Nat) : Stmt → Bool
  | .join u => decide (0 < u) && decide (u < N)
  | .seq s t | .ite _ s t => s.joinsIn N && t.joinsIn N
  | .loop _ _ b => b.joinsIn N
  | _ => true

/-- The `spawn` targets of a statement (both branches of a test). -/
def Stmt.spawns : Stmt → List Nat
  | .spawn u => [u]
  | .seq s t | .ite _ s t => s.spawns ++ t.spawns
  | .loop _ _ b => b.spawns
  | _ => []

/-- No `spawn` under a loop. -/
def Stmt.loopSpawnFree : Stmt → Bool
  | .seq s t | .ite _ s t => s.loopSpawnFree && t.loopSpawnFree
  | .loop _ _ b => b.spawns.isEmpty
  | _ => true

end Silmaril.X86.Concurrency.Cir

namespace Silmaril.X86.Concurrency.Cir.Proc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl (Heap TStep upd Star)

/-- **Static sync safety** over the cells `D`: every cell of `D` is mapped; every access of
every thread is at a literal address in `D`; every `join` names a spawnable thread; only the
main thread spawns, never under a loop, each spawnable thread at most once. -/
structure SProg.Static (P : SProg) (D : List Nat) : Prop where
  dom : ∀ a ∈ D, (P.heap a).isSome
  lit : ∀ s ∈ P.bodies, s.litIn D = true
  joins : ∀ s ∈ P.bodies, s.joinsIn P.N = true
  child : ∀ s ∈ P.bodies.tail, s.spawns = []
  mainLoop : (P.body 0).loopSpawnFree = true
  mainNodup : (P.body 0).spawns.Nodup
  mainRange : ∀ u ∈ (P.body 0).spawns, 0 < u ∧ u < P.N

/-! ## The refinement relation -/

/-- Register files agree outside the scratch register. -/
def Ag (rs rs' : Regs) : Prop := ∀ r, r ≠ scratch → rs r = rs' r

/-- The states of the join loop for `u` before it has seen `ctl u = 0` (the CIR thread is
still at `join u`). -/
def JRes (u : Nat) (p : PStmt) (rs : Regs) : Prop :=
  p = joinS u ∨
    (rs scratch ≠ 0 ∧
      (p = .seq .skip (jW u) ∨ p = jW u ∨ p = .seq (.seq (jLd u) (jIt u)) (jW u) ∨
        p = .seq (.seq .skip (jIt u)) (jW u) ∨ p = .seq (jIt u) (jW u) ∨
        p = .seq (jFw u) (jW u)))

/-- The states of the join loop for `u` after it has seen `ctl u = 0` (the CIR thread is
past `join u`). -/
def JPost (u : Nat) (p : PStmt) (rs : Regs) : Prop :=
  rs scratch = 0 ∧
    (p = .seq (.seq .skip (jIt u)) (jW u) ∨ p = .seq (jIt u) (jW u) ∨ p = .seq .skip (jW u) ∨
      p = jW u)

/-- **Thread correspondence** inside lowered code: the process-IR state `(p, rs)` implements
the CIR state `(s, rs')`. -/
inductive Corr (L : Layout) : PStmt → Regs → Stmt → Regs → Prop
  | low {s rs rs'} (hs : s.noR scratch = true) (ha : Ag rs rs') : Corr L (lower L s) rs s rs'
  | seq {p rs s rs' t} (h : Corr L p rs s rs') (ht : t.noR scratch = true) :
      Corr L (.seq p (lower L t)) rs (.seq s t) rs'
  | jn {u p rs rs'} (hj : JRes u p rs) (ha : Ag rs rs') : Corr L p rs (.join u) rs'
  | jnPost {u p rs rs'} (hj : JPost u p rs) (ha : Ag rs rs') : Corr L p rs .skip rs'
  | fw {d rs rs'} (ha : Ag (rs.set d ((nrm d).eval rs)) rs') :
      Corr L (.seq .skip (.cir (.assign d (nrm d)))) rs .skip rs'
  | fw2 {d rs rs'} (ha : Ag (rs.set d ((nrm d).eval rs)) rs') :
      Corr L (.cir (.assign d (nrm d))) rs .skip rs'

/-- **Top-level thread correspondence**: lowered code followed by `exit`/`exit_group`, and the
register-zeroing prologue of a spawned thread. -/
inductive Top (L : Layout) : PStmt → Regs → Stmt → Regs → Prop
  | tail {p rs s rs' e} (h : Corr L p rs s rs') (he : e = exitS ∨ e = exitGroupS) :
      Top L (.seq p e) rs s rs'
  | fin {e rs rs'} (he : e = exitS ∨ e = exitGroupS) : Top L e rs .skip rs'
  | pro {l b rs} (hb : b.noR scratch = true) (hz : ∀ r, r ∉ l → rs r = 0) :
      Top L (.seq (.seq (zeroAll l) (lower L b)) exitS) rs b Regs.zero
  | proS {l b rs} (hb : b.noR scratch = true) (hz : ∀ r, r ∉ l → rs r = 0) :
      Top L (.seq (.seq (.seq .skip (zeroAll l)) (lower L b)) exitS) rs b Regs.zero

/-- A thread record implements a CIR thread state (a waiter by the state it resumes in). -/
def TCorr (L : Layout) (r : TRec PSt) (a : Stmt × Regs) : Prop :=
  match r.st with
  | .run x => Top L x.1 x.2 a.1 a.2
  | .wait _ k => Top L (k 0).1 (k 0).2 a.1 a.2
  | .exited => a.1 = .skip

/-- **The refinement relation** between a lowered process and a sync configuration:
* the heaps agree outside the control cells; the sync heap has no control cell;
* the control word of a spawnable thread is mapped, and `0` only once that thread has
  finished;
* unstarted sync threads are at their bodies;
* an injective map `g` from tids to CIR threads: each process thread implements a started
  CIR thread, and its `clear_child_tid` is that thread's control word, or absent, in which case
  the thread is CIR thread `0` (the main thread; this pins the main thread's identity, which
  `Top` alone does not, since `Top` accepts either exit). -/
structure Rel (P : SProg) (L : Layout) (C : PCfg PSt) (A : SCfg) : Prop where
  heap : ∀ a, isCtl a = false → C.mem a = A.mem a
  actl : ∀ u, A.mem (ctlAddr u) = none
  cctl : ∀ u, 0 < u → u < P.N →
    ∃ v, C.mem (ctlAddr u) = some v ∧ (v = 0 → A.started u = true ∧ (A.ts u).1 = .skip)
  fresh : ∀ u, A.started u = false → A.ts u = (P.body u, Regs.zero)
  map : ∃ g : Nat → Nat,
    (∀ t t' r r', C.th t = some r → C.th t' = some r' → g t = g t' → t = t') ∧
    ∀ t r, C.th t = some r → g t < P.N ∧ A.started (g t) = true ∧ TCorr L r (A.ts (g t)) ∧
      ((r.ctid = none ∧ g t = 0) ∨ (r.ctid = some (ctlAddr (g t)) ∧ 0 < g t))

/-- The heap without the control cells. -/
def userHeap (h : Heap) : Heap := fun a => if isCtl a then none else h a


/-! ## Example: fork-join -/

namespace Ex

/-- The shared cell. -/
def x : Nat := 0x1000

/-- The heap: `x ↦ 0`. -/
def heap : Heap := fun a => if a = x then some 0 else none

/-- The main thread: `spawn 1; join 1; rax := load x`. -/
def main : Stmt := .seq (.spawn 1) (.seq (.join 1) (.load .rax .na 8 .wb (.lit x)))

/-- The child: `store x 42`. -/
def child : Stmt := .store .na 8 .wb (.lit x) (.lit 42)

/-- **Fork-join**. -/
def forkJoin : SProg := ⟨[main, child], heap⟩

/-- Stacks and TLS blocks. -/
def layout : Layout := ⟨fun u => 0x100000 * (u + 1), fun u => 0x200000 + 0x1000 * u⟩

end Ex

end Silmaril.X86.Concurrency.Cir.Proc
