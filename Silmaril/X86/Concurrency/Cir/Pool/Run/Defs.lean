module

public import Silmaril.X86.Concurrency.Cir.Pool.Defs
public import Silmaril.X86.Concurrency.Cir.Robust.Defs

/-!
# Concrete runs of a worker pool (non-vacuity)

The explorer (`Cir.Robust`) has no `local` blocks: `tsucc` gives them no step. A pool's jobs
are `local` blocks, so this module adds the missing step for **functional** blocks (outputs
`fn` of the inputs, no register outputs, as `Fj.Job.block`):

* `blkSucc fn mem vw s rs`: the block step at the head of `s` (through `seq`), reading the
  view `vw`, if every cell is mapped in `mem` and the block's own contract accepts `fn`;
* `blkC fn c t`: that step of thread `t` on a concrete configuration, buffering the writes;
* `runT fn N t fuel c`: run thread `t` alone, taking its block step when there is one, else the
  first successor `tsoStepT` lists (a thread step, or a flush when the thread must drain).

`Run/Thms.lean` proves each step a TSO step, so `runT` follows a real TSO run.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Pool.Run

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl (Heap view)
open Silmaril.X86.Concurrency.Cir.Robust (CSt memOf tsoStepT)

/-- **The block step at the head of a statement**, for a functional block. -/
def blkSucc (fn : List Nat → List Nat) (mem vw : Heap) : Stmt → Regs → Option (Lab × Stmt × Regs)
  | .local b, rs =>
    let ivs := b.ins.map fun c => (vw c.1).getD 0
    if b.rout.isEmpty && (b.ins.all fun c => (vw c.1).isSome && (mem c.1).isSome) &&
        (b.outs.all fun c => (mem c.1).isSome) && (fn ivs).length == b.outs.length &&
        @decide (b.spec (b.rin.map (fun r => (rs r).toNat) ++ ivs) ([] ++ fn ivs)) (b.dec _ _)
    then some (.blk b.name (cellVals b.ins ivs) (cellVals b.outs (fn ivs)) [], .skip,
      rs.setMany b.rout [])
    else none
  | .seq s t, rs => (blkSucc fn mem vw s rs).map fun p => (p.1, .seq p.2.1 t, p.2.2)
  | _, _ => none

/-- **A block step of thread `t`** on a concrete configuration: its writes are buffered. -/
def blkC (fn : List Nat → List Nat) (c : CSt) (t : Nat) : Option CSt :=
  match blkSucc fn (memOf c.mem) (view (memOf c.mem) (c.bufT t)) (c.th t).1 (c.th t).2 with
  | some (l, s', rs') => some { c.setTh t s' rs' with buf := c.buf.set t (c.bufT t ++ l.ents) }
  | none => none

/-- **Run thread `t` alone**: its block step if any, else its first enumerated TSO successor. -/
def runT (fn : List Nat → List Nat) (N t : Nat) : Nat → CSt → CSt
  | 0, c => c
  | f + 1, c =>
    if t < N ∧ t < c.buf.length ∧ t < c.ts.length then
      match blkC fn c t with
      | some d => runT fn N t f d
      | none =>
        match (tsoStepT c t)[0]? with
        | some d => runT fn N t f d
        | none => c
    else c

/-- Run the threads of a schedule one after another, each alone. -/
def runAll (fn : List Nat → List Nat) (N fuel : Nat) (c : CSt) : List Nat → CSt
  | [] => c
  | t :: ts => runAll fn N fuel (runT fn N t fuel c) ts

/-- **Run a schedule of slices**: each entry `(t, f)` runs thread `t` alone for at most `f`
steps (`runT`), so threads can be interleaved at chosen points. -/
def runS (fn : List Nat → List Nat) (N : Nat) (c : CSt) : List (Nat × Nat) → CSt
  | [] => c
  | (t, f) :: l => runS fn N (runT fn N t f c) l

/-- The cells of a linked pool: the mutex object, the control cells and the jobs' footprints. -/
def dom (P : Wp) (M : Mutex.Iface) : List Nat :=
  (List.range M.size).map (P.m + ·) ++ P.ctl ++ P.items.flatMap Item.fp

/-- **The linked pool as a concrete configuration** (`Run.start_cfg`). -/
def start (P : Wp) (M : Mutex.Iface) (L : Nat) : CSt :=
  Robust.start ((List.range P.K).map fun t => (P.body (M.lock L) (M.unlock L) t, Regs.zero))
    ((dom P M).filterMap fun a => ((P.client.link M L).mem a).map (a, ·))

/-- **A racy mutant**: the pool with **no mutex**, both holes replaced by a full
fence (`mfence`), from the pool's own initial cells `P.mem0`. Not a `Mutex.Iface` instance
(no `lock_spec` can hold for it); used only to show that the goal can fail
(`noLock_violates`). -/
def startNoLock (P : Wp) : CSt :=
  Robust.start ((List.range P.K).map fun t =>
      (P.body (fun _ => .fence .mfence) (fun _ => .fence .mfence) t, Regs.zero))
    ((P.ctl ++ P.items.flatMap Item.fp).filterMap fun a => (P.mem0 a).map (a, ·))

/-- **A job with no step** (the counterexample to `poolNoDeadlockAsStated`): no
input or output cells, but its function returns one value, so its block's contract
`outs = fn ins` has no solution (`[] = [0]`). `Wp.Ok` does not look at job functions. -/
def badJob : Fj.Job := ⟨"bad", [], [], fun _ => [0]⟩

/-- One worker, the single job `badJob`, the layout of `exHash`. -/
def badP : Wp where
  K := 1
  items := [⟨badJob, [], 0x3000⟩]
  m := 0x100
  slot := 8
  qa := 0x200
  da := 0x208
  ea := 0x210
  cur0 := 0x300
  W := 1

/-- The next statement is a block with no cells and no registers whose contract rejects the
empty output: such a thread has no step (`Run.stuckB_noStep`). -/
def stuckB (s : Stmt) : Bool :=
  match headS s with
  | .local b => b.ins.isEmpty && b.outs.isEmpty && b.rin.isEmpty && b.rout.isEmpty &&
      !(@decide (b.spec [] []) (b.dec [] []))
  | _ => false

end Silmaril.X86.Concurrency.Cir.Pool.Run
