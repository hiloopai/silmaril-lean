module

public import Silmaril.X86.Concurrency.Cir.Mutex.Defs
public import Silmaril.X86.Concurrency.Cir.Fj.Defs

/-!
# A worker pool over a mutex-protected queue

`Wp` (worker pool) is a small IR **on top of**
CIR and `Mutex.Client`, in the style of `Fj`: a pool is a list of jobs, a number of
workers and a memory layout. `Wp.client` lowers it to an ordinary `Mutex.Client` (CIR code
with holes for `lock`/`unlock`), so every mutex meeting `Mutex.Iface` can be linked in
(`link_any_mutex`), and the proof is done **once** for every pool.

## Jobs (`Item`)

An item is a `Fj.Job` (input cells, output cells, a function `fn` from input values to
output values; its CIR code is the opaque block `local job.block`), the values `arg` of its input
cells, and a **run counter** cell `cnt`. Running an item (`Item.run`) is the block followed by
`[cnt] := [cnt] + 1`, so "exactly once" is observable: the counter ends at `1`.

* `Item.freshH`: the item's cells before it runs (`cnt ↦ 0`, inputs ↦ `arg`, outputs ↦ `0`);
* `Item.doneH`: its cells after one run (the block's contract, then the counter increment).

## The pool (`Wp`) and its code

`K` workers (threads `0 … K-1`) share a queue: the cell `qa` holds the index of the next job.
The cells `da` (jobs returned) and `ea` (workers exited) are bookkeeping, `cur t` is worker `t`'s
private cell, and the mutex lives at `m` in a slot of `slot` bytes. Every worker runs, at most
`n + 1` times (`worker`):

```
lock; k := [qa]; if k < n then ([qa] := k + 1; [cur] := k) else ([ea] := [ea] + 1; [cur] := n);
unlock;
if [cur] < n then (run job [cur]; lock; [da] := [da] + 1; unlock);
continue while [cur] < n
```

Thread `0` then waits (at most `W` times, `waitL`) until `[da] = n` and `[ea] = K` under the
lock, and **keeps the lock**: it owns the whole queue state at the end. Values that must survive
a `lock`/`unlock` hole are kept in `cur t`, because the interface's specs say nothing about
registers.

## The proof idea (no ghost state)

The mutex protects `R` (`Wp.R`): the queue cells and, for every job `j`, its cells in state
`σ j` (`fresh`: not yet taken, in `R`; `taken`: owned by the worker running it; `done`: handed
back, in `R`), with `σ j = fresh ↔ k ≤ j` and `[da] = #{j | σ j = done}`. Taking a job moves its
fresh cells to the worker; returning it moves its done cells back. A job is taken at most once
because its fresh cells leave `R` when it is taken, and returned at most once because a done
heap cannot be disjoint from itself. When thread `0` sees `[da] = n`, every job is done and its
cells are in thread `0`'s final heap: this is the goal (`Wp.goal`).

`Wp.Ok` (decided by `Wp.okB`) is the layout condition: footprints of different jobs are
disjoint (each footprint address has its own job as `owner`), the control cells are distinct and
owned by no job, nothing overlaps the mutex slot, and all addresses fit in 64 bits.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Pool

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Mutex (Iface Client)

/-! ## Items -/

/-- A list of `(address, size, value)` cells as a heap (the first entry for an address wins). -/
def cellsH (l : List (Nat × Nat × Nat)) : Heap := fun a => (l.find? (·.1 == a)).map (·.2.2)

/-- **A job of the pool**: a job, the values of its input cells, and its run counter. -/
structure Item where
  job : Fj.Job
  arg : List Nat
  cnt : Nat

namespace Item

/-- The item's footprint: its counter, its input and its output addresses. -/
def fp (it : Item) : List Nat := it.cnt :: (it.job.ins.map (·.1) ++ it.job.outs.map (·.1))

/-- **The item before it runs**: `cnt ↦ 0`, inputs ↦ `arg`, outputs ↦ `0`. -/
def freshH (it : Item) : Heap :=
  Heap.union (Heap.single it.cnt 0)
    (Heap.union (cellsH (cellVals it.job.ins it.arg))
      (cellsH (cellVals it.job.outs (it.job.outs.map fun _ => 0))))

/-- The values the block reads (its input cells in the fresh heap). -/
def ivals (it : Item) : List Nat := it.job.ins.map fun c => (it.freshH c.1).getD 0

/-- The label of the item's block run on its fresh cells. -/
def blkLab (it : Item) : Lab :=
  .blk it.job.name (cellVals it.job.ins it.ivals) (cellVals it.job.outs (it.job.fn it.ivals)) []

/-- The item's cells after its block. -/
def blkH (it : Item) : Heap := it.blkLab.updH it.freshH

/-- **The item after one run**: the block's writes, then the counter incremented. -/
def doneH (it : Item) : Heap := fun a =>
  if a = it.cnt then some (((it.blkH it.cnt).getD 0 + 1) % 2 ^ 64) else it.blkH a

/-- `[a] := [a] + 1` (non-atomic, 8 bytes), through `rbx`. -/
def incr (a : Nat) : Stmt :=
  .seq (.load .rbx .na 8 .wb (.lit a)) (.store .na 8 .wb (.lit a) (.bin .add (.reg .rbx) (.lit 1)))

/-- **Run the item**: its block, then its counter. -/
def run (it : Item) : Stmt := .seq (.local it.job.block) (incr it.cnt)

/-- **A well-formed item**: distinct input addresses, distinct output addresses, the counter
apart from both, inputs apart from outputs, and `arg`, `fn arg` of the right lengths. -/
def wfB (it : Item) : Bool :=
  decide (it.job.ins.map (·.1)).Nodup && decide (it.job.outs.map (·.1)).Nodup &&
    !(it.job.ins.map (·.1)).contains it.cnt && !(it.job.outs.map (·.1)).contains it.cnt &&
    (it.job.ins.map (·.1)).all (fun a => !(it.job.outs.map (·.1)).contains a) &&
    it.arg.length == it.job.ins.length && (it.job.fn it.arg).length == it.job.outs.length

end Item

/-- The state of a job in the queue's invariant. -/
inductive St where
  | fresh
  | taken
  | done
  deriving DecidableEq, Repr

/-- The cells of an item in a state that `R` holds (`taken`: none, the worker has them). -/
def Item.stH (it : Item) : St → Heap
  | .fresh => it.freshH
  | .taken => Heap.empty
  | .done => it.doneH

/-! ## Pools -/

/-- **A worker pool**: `K` workers, the jobs, the mutex address and slot, the queue cells
`qa` (next job), `da` (jobs returned), `ea` (workers exited), the base of the workers' private
cells, and the bound of thread `0`'s final wait. -/
structure Wp where
  K : Nat
  items : List Item
  m : Nat
  slot : Nat
  qa : Nat
  da : Nat
  ea : Nat
  cur0 : Nat
  W : Nat

namespace Wp

/-- The number of jobs. -/
def n (P : Wp) : Nat := P.items.length

/-- Worker `t`'s private cell. -/
def cur (P : Wp) (t : Nat) : Nat := P.cur0 + 8 * t

/-- The control cells: the queue cells and the workers' private cells. -/
def ctl (P : Wp) : List Nat := [P.qa, P.da, P.ea] ++ (List.range P.K).map P.cur

/-- Job `j`'s cells in state `s`. -/
def stH (P : Wp) (j : Nat) (s : St) : Heap :=
  match P.items[j]? with
  | some it => it.stH s
  | none => Heap.empty

/-- Address `a` is in job `j`'s footprint. -/
def fpB (P : Wp) (j a : Nat) : Bool :=
  match P.items[j]? with
  | some it => it.fp.contains a
  | none => false

/-- The job whose footprint holds `a` (the first one). -/
def owner (P : Wp) (a : Nat) : Option Nat := (List.range P.n).find? fun j => P.fpB j a

/-- **The jobs' cells** with job `j` in state `σ j`. -/
def jobH (P : Wp) (σ : Nat → St) : Heap := fun a =>
  match P.owner a with
  | some j => P.stH j (σ j) a
  | none => none

/-- The queue cells: `qa ↦ k`, `da ↦ d`, `ea ↦ e`. -/
def ctlH (P : Wp) (k d e : Nat) : Heap :=
  Heap.union (Heap.single P.qa k) (Heap.union (Heap.single P.da d) (Heap.single P.ea e))

/-- The number of returned jobs. -/
def doneCount (P : Wp) (σ : Nat → St) : Nat := (List.range P.n).countP fun j => σ j == .done

/-- **The resource the mutex protects**: the queue at `k`, `d` jobs returned, `e` exits, and
every job's cells in its state: fresh exactly from `k` on, `d` of them done. -/
def R (P : Wp) : HProp := fun h => ∃ k d e σ, k ≤ P.n ∧ (∀ j < P.n, σ j = .fresh ↔ k ≤ j) ∧
  d = P.doneCount σ ∧ h = Heap.union (P.ctlH k d e) (P.jobH σ)

/-! ## The code -/

/-- `d := [a]` (non-atomic, 8 bytes). -/
def ldc (d : Reg) (a : Nat) : Stmt := .load d .na 8 .wb (.lit a)

/-- `[a] := v` (non-atomic, 8 bytes). -/
def stc (a : Nat) (v : Expr) : Stmt := .store .na 8 .wb (.lit a) v

/-- A critical section: `lock(m); body; unlock(m); cont`. -/
def crit (P : Wp) (lk ul : Expr → Stmt) (body cont : Stmt) : Stmt :=
  .seq (lk (.lit P.m)) (.seq body (.seq (ul (.lit P.m)) cont))

/-- **Take a job** (under the lock): `k := [qa]`; if `k < n`, advance the queue and remember `k`,
else count an exit and remember `n`. -/
def takeB (P : Wp) (t : Nat) : Stmt :=
  .seq (ldc .r12 P.qa)
    (.ite (.bin .ltu (.reg .r12) (.lit P.n))
      (.seq (stc P.qa (.bin .add (.reg .r12) (.lit 1))) (stc (P.cur t) (.reg .r12)))
      (.seq (Item.incr P.ea) (stc (P.cur t) (.lit P.n))))

/-- **Return a job** (under the lock): count it. -/
def retB (P : Wp) : Stmt := Item.incr P.da

/-- **Dispatch** on `r12`: run the job with that index. -/
def disp : List Item → Nat → Stmt
  | [], _ => .skip
  | it :: l, j => .ite (.bin .eq (.reg .r12) (.lit j)) it.run (disp l (j + 1))

/-- **One round of worker `t`**. -/
def wbody (P : Wp) (lk ul : Expr → Stmt) (t : Nat) : Stmt :=
  .seq (P.crit lk ul (P.takeB t) .skip)
    (.seq (ldc .r12 (P.cur t))
      (.seq (.ite (.bin .ltu (.reg .r12) (.lit P.n))
          (.seq (disp P.items 0) (P.crit lk ul P.retB .skip)) .skip)
        (.seq (ldc .r12 (P.cur t)) (.assign .r13 (.bin .ltu (.reg .r12) (.lit P.n))))))

/-- **Worker `t`**: rounds while it got a job, at most `n + 1` of them. -/
def worker (P : Wp) (lk ul : Expr → Stmt) (t : Nat) : Stmt :=
  .seq (.assign .r13 (.lit 1)) (.loop (P.n + 1) (.reg .r13) (P.wbody lk ul t))

/-- **One wait round of thread `0`**: lock; if every job is back and every worker has exited,
keep the lock and stop; else unlock and go on. -/
def waitB (P : Wp) (lk ul : Expr → Stmt) : Stmt :=
  .seq (lk (.lit P.m))
    (.seq (ldc .rbx P.da)
      (.seq (ldc .rcx P.ea)
        (.ite (.bin .and (.bin .eq (.reg .rbx) (.lit P.n)) (.bin .eq (.reg .rcx) (.lit P.K)))
          (.assign .r14 (.lit 0))
          (.seq (ul (.lit P.m)) (.assign .r14 (.lit 1))))))

/-- **Thread `0`'s wait** (at most `W` rounds). -/
def waitL (P : Wp) (lk ul : Expr → Stmt) : Stmt :=
  .seq (.assign .r14 (.lit 1)) (.loop P.W (.reg .r14) (P.waitB lk ul))

/-- **Thread `t` of the pool**: a worker; thread `0` then waits. -/
def body (P : Wp) (lk ul : Expr → Stmt) (t : Nat) : Stmt :=
  if t = 0 then .seq (P.worker lk ul 0) (P.waitL lk ul) else P.worker lk ul t

/-- The workers' private cells, all `0`. -/
def cursH (P : Wp) : Heap := fun a =>
  if (List.range P.K).any (fun t => P.cur t == a) then some 0 else none

/-- **The pool's initial cells**: the queue at `0`, private cells `0`, every job fresh. -/
def mem0 (P : Wp) : Heap :=
  Heap.union (Heap.union (P.ctlH 0 0 0) P.cursH) (P.jobH fun _ => .fresh)

/-- **The pool as a `Mutex.Client`**: `K` threads, one mutex at `m`. -/
def client (P : Wp) : Client := ⟨P.K, P.body, P.mem0, [P.m], P.slot⟩

/-- **The goal: every job ran exactly once, with its contract.** Every item's done cells (the
block's outputs on its inputs, and the run counter incremented once) are in the final memory. -/
def goal (P : Wp) (_ : Nat → Regs) (mem : Heap) : Prop := ∀ it ∈ P.items, Heap.Le it.doneH mem

/-! ## Layout conditions -/

/-- **The layout conditions** of a pool. -/
structure Ok (P : Wp) : Prop where
  kpos : 0 < P.K
  nlt : P.n + 1 < 2 ^ 64
  klt : P.K < 2 ^ 64
  mlt : P.m < 2 ^ 64
  own : ∀ j < P.n, ∀ a, P.fpB j a = true → P.owner a = some j
  fpLt : ∀ j a, P.fpB j a = true → a < 2 ^ 64 ∧ (a < P.m ∨ P.m + P.slot ≤ a)
  ctlLt : ∀ a ∈ P.ctl, a < 2 ^ 64 ∧ (a < P.m ∨ P.m + P.slot ≤ a)
  ctlOwn : ∀ a ∈ P.ctl, P.owner a = none
  ctlNodup : P.ctl.Nodup
  argLen : ∀ it ∈ P.items, it.arg.length = it.job.ins.length

/-- An address is below `2 ^ 64` and outside the mutex slot. -/
def placedB (P : Wp) (a : Nat) : Bool :=
  decide (a < 2 ^ 64) && (decide (a < P.m) || decide (P.m + P.slot ≤ a))

/-- `Ok` as a Boolean (`Wp.ok_of_okB`). -/
def okB (P : Wp) : Bool :=
  decide (0 < P.K) && decide (P.n + 1 < 2 ^ 64) && decide (P.K < 2 ^ 64) &&
    decide (P.m < 2 ^ 64) &&
    (List.range P.n).all (fun j => match P.items[j]? with
      | some it => it.fp.all fun a => P.owner a == some j && P.placedB a
      | none => true) &&
    P.ctl.all (fun a => P.placedB a && P.owner a == none) &&
    decide P.ctl.Nodup &&
    P.items.all (fun it => it.arg.length == it.job.ins.length)

end Wp

/-! ## Termination -/

/-- The next leaf statement (through `seq`). -/
def headS : Stmt → Stmt
  | .seq s _ => headS s
  | s => s

/-- A thread has **run out of a loop bound**: its next statement is a loop with no iterations
left whose condition still holds. -/
def Exhausted (p : Stmt × Regs) : Prop :=
  ∃ c b, headS p.1 = .loop 0 c b ∧ truthy (c.eval p.2) = true

/-- **A job that cannot get stuck**: its function returns one value per output
cell on **every** input of the right length (so its block always has a step), and its counter is
not one of its outputs (so the 8-byte load of the counter never reads an output value, which
need not fit 64 bits). `wfB` gives the length only at `arg`; the CSL proof does not record which
values a job's inputs hold when it runs, so totality is asked for every input. -/
def Item.Total (it : Item) : Prop :=
  (∀ vs : List Nat, vs.length = it.job.ins.length → (it.job.fn vs).length = it.job.outs.length) ∧
    it.cnt ∉ it.job.outs.map (·.1)

/-- **The original statement of `Task.poolNoDeadlock`**, kept as the record of the
counterexample. It is **false** (`Pool.poolNoDeadlockAsStated_false`): `Wp.Ok` does
not constrain a job's function, and a job whose function returns the wrong number of values
(`fn _ = [0]` with no output cells) has a block with no step at all. The linked pool, with one
worker and the spin mutex, reaches a drained configuration in which the worker is at that
block: stuck, not finished, and with no loop out of its bound. -/
def poolNoDeadlockAsStated (P : Wp) (M : Iface) : Prop :=
  P.Ok → ∀ (L : Nat) (model : OModel) (Cf : OCfg),
    OReach model P.K (P.client.link M L).toO Cf → (∀ Cf', ¬ OStep model P.K Cf Cf') →
    (Cf.Drained ∧ ∀ t < P.K, (Cf.ts t).1 = .skip) ∨ ∃ t < P.K, Exhausted (Cf.ts t)

/-- **No deadlock** (PROVED for the spin mutexes and the futex mutex,
`Pool.poolNoDeadlock_spin`, `Pool.poolNoDeadlock_fmutex`, and for every mutex whose code is
`Progress.MutexLive`, `Pool.poolNoDeadlock_of_live`). With the mutex `M` fitting the slot and
every job total (`Item.Total`), every reachable configuration of the linked pool from which the
TSO/XL machine has no step is finished and drained, or some thread has run out of a loop bound.

Restated: the original statement (kept as `poolNoDeadlockAsStated`) had neither hypothesis and is
false (`poolNoDeadlockAsStated_false`: a job whose function has the wrong length blocks its
worker). `M.size ≤ P.slot` is the hypothesis of the pool's CSL certificate (`Wp.proved`), which
the proof uses to know that every label touches a mapped cell; no counterexample without it is
known.

CIR loops are bounded, so every run is finite, and nothing in CIR blocks: a lock is a bounded
spin and `futex_wait` always returns. So the statement is a safety property (no thread is
ever stuck except at an exhausted loop), and no fairness argument is needed: an unfair schedule
only makes some spin exhaust, which is the second disjunct. Under a fair scheduler, as the bounds
grow, the spins and the wait end; that limit statement is not formalised.

The statement is per mutex: `Iface` is a partial-correctness interface, met also by a mutex whose
lock code is stuck, so it cannot hold for every `M`. `Progress.MutexLive` is the extra property
(the mutex code is thread-locally `Good` at its lock word) under which it holds.

It is not lock liveness: it also holds for a mutex whose lock is never granted
(`Pool.poolNoDeadlock_deadMutex`), since such a lock ends as an exhausted spin. -/
def Task.poolNoDeadlock (P : Wp) (M : Iface) : Prop :=
  P.Ok → M.size ≤ P.slot → (∀ it ∈ P.items, it.Total) → ∀ (L : Nat) (model : OModel) (Cf : OCfg),
    OReach model P.K (P.client.link M L).toO Cf → (∀ Cf', ¬ OStep model P.K Cf Cf') →
    (Cf.Drained ∧ ∀ t < P.K, (Cf.ts t).1 = .skip) ∨ ∃ t < P.K, Exhausted (Cf.ts t)

end Silmaril.X86.Concurrency.Cir.Pool
