module

public import Silmaril.X86.Concurrency.Cir.Progress.Defs
public import Silmaril.X86.Concurrency.Cir.Mutex.Thms
public import Silmaril.X86.Concurrency.Cir.Mutex.Futex.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.Progress.Rules
import Silmaril.Proofs.X86.Concurrency.Cir.Progress.Stuck
public import Silmaril.Proofs.X86.Concurrency.Cir.Progress.Mutex

/-!
# Progress of CSL-certified CIR programs: theorems

Everything here is PROVED (standard axioms
only). Proofs are in `Silmaril/Proofs/X86/Concurrency/Cir/Progress/`.

* **Thread-local rules** for `Inv w A s B`: `inv_conseq`, `inv_skip`, `inv_seq`, `inv_ite`,
  `inv_loop` (every bound, `A` a loop invariant), and the leaves `inv_assign`, `inv_load`
  (the cell is no wider than the load), `inv_store` (no narrower than the store), `inv_rmw`
  (exactly as wide), `inv_fence`, `inv_fwait` (at most four bytes), `inv_fwake`, `inv_block`
  (a total contract, outputs to unconstrained cells).
* **`stuck`**: on the TSO and XL store-buffer machines, every stuck configuration reached from a
  CSL-certified start whose threads are thread-locally `Good` (and whose initial values fit) is
  drained and finished, or has a thread out of a loop bound. No fairness assumption is needed:
  nothing in CIR blocks, so a stuck thread is a thread with no enabled step at all.
* **Mutexes**: `spinLive`, `spinScLive`, `fmutexLive`: the spin mutexes and the futex mutex
  are `MutexLive` (their code accesses only the 4-byte lock word `[rdi]`, at every loop bound).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Progress

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Mutex (spinMutex spinMutexSc)
open Silmaril.X86.Atomic9 (FenceKind)

variable {w : Nat → Option Nat} {A B C : Regs → Prop}

theorem inv_conseq {A' B' : Regs → Prop} {s : Stmt} (hA : ∀ rs, A' rs → A rs)
    (hB : ∀ rs, B rs → B' rs) (h : Inv w A s B) : Inv w A' s B' :=
  Silmaril.Proofs.X86.Concurrency.Cir.Progress.inv_conseq hA hB h

theorem inv_skip : Inv w A .skip A := Silmaril.Proofs.X86.Concurrency.Cir.Progress.inv_skip

theorem inv_seq {s t : Stmt} (h1 : Inv w A s B) (h2 : Inv w B t C) : Inv w A (.seq s t) C :=
  Silmaril.Proofs.X86.Concurrency.Cir.Progress.inv_seq h1 h2

theorem inv_ite {c : Expr} {s t : Stmt} (h1 : Inv w A s B) (h2 : Inv w A t B) :
    Inv w A (.ite c s t) B :=
  Silmaril.Proofs.X86.Concurrency.Cir.Progress.inv_ite h1 h2

/-- **Bounded loops**, at every bound, with `A` a loop invariant of the body. -/
theorem inv_loop {n : Nat} {c : Expr} {b : Stmt} (hb : Inv w A b A) : Inv w A (.loop n c b) A :=
  Silmaril.Proofs.X86.Concurrency.Cir.Progress.inv_loop hb

theorem inv_assign {d : Reg} {e : Expr} (hB : ∀ rs, A rs → B (rs.set d (e.eval rs))) :
    Inv w A (.assign d e) B :=
  Silmaril.Proofs.X86.Concurrency.Cir.Progress.inv_assign hB

/-- A load from a cell no wider than the load. -/
theorem inv_load {d : Reg} {m : Mode} {sz : Nat} {fl : Flav} {a : Expr}
    (hw : ∀ rs, A rs → ∃ k, w (a.eval rs).toNat = some k ∧ k ≤ sz)
    (hB : ∀ rs, A rs → ∀ v, B (rs.set d v)) : Inv w A (.load d m sz fl a) B :=
  Silmaril.Proofs.X86.Concurrency.Cir.Progress.inv_load hw hB

/-- A store to a cell no narrower than the store. -/
theorem inv_store {m : Mode} {sz : Nat} {fl : Flav} {a v : Expr}
    (hw : ∀ rs, A rs → ∀ k, w (a.eval rs).toNat = some k → sz ≤ k)
    (hB : ∀ rs, A rs → B rs) : Inv w A (.store m sz fl a v) B :=
  Silmaril.Proofs.X86.Concurrency.Cir.Progress.inv_store hw hB

/-- A read-modify-write of a cell exactly as wide. -/
theorem inv_rmw {d : Reg} {m : Mode} {sz : Nat} {op : RmwOp} {a arg : Expr}
    (hw : ∀ rs, A rs → w (a.eval rs).toNat = some sz)
    (hB : ∀ rs, A rs → ∀ v, B (rs.set d v)) : Inv w A (.rmw d m sz op a arg) B :=
  Silmaril.Proofs.X86.Concurrency.Cir.Progress.inv_rmw hw hB

theorem inv_fence {k : FenceKind} (hB : ∀ rs, A rs → B rs) : Inv w A (.fence k) B :=
  Silmaril.Proofs.X86.Concurrency.Cir.Progress.inv_fence hB

/-- A futex wait on a word of at most four bytes. -/
theorem inv_fwait {d : Reg} {a v : Expr}
    (hw : ∀ rs, A rs → ∃ k, w (a.eval rs).toNat = some k ∧ k ≤ 4)
    (hB : ∀ rs, A rs → ∀ x, B (rs.set d x)) : Inv w A (.futexWait d a v) B :=
  Silmaril.Proofs.X86.Concurrency.Cir.Progress.inv_fwait hw hB

theorem inv_fwake {a n : Expr} (hB : ∀ rs, A rs → B rs) : Inv w A (.futexWake a n) B :=
  Silmaril.Proofs.X86.Concurrency.Cir.Progress.inv_fwake hB

/-- A block with a total contract whose outputs go to unconstrained cells. -/
theorem inv_block {b : Block}
    (htot : ∀ rs, A rs → ∀ ivs, ivs.length = b.ins.length → ∃ rvs ovs,
      rvs.length = b.rout.length ∧ ovs.length = b.outs.length ∧
      b.spec (b.rin.map (fun r => (rs r).toNat) ++ ivs) (rvs ++ ovs))
    (hw : ∀ c ∈ b.outs, w c.1 = none)
    (hB : ∀ rs, A rs → ∀ rvs, B (rs.setMany b.rout rvs)) : Inv w A (.local b) B :=
  Silmaril.Proofs.X86.Concurrency.Cir.Progress.inv_block htot hw hB

/-- **Progress of certified programs.** On the TSO or XL store-buffer machine, let `C0` be a
CSL-certified start whose threads `0 … N-1` are thread-locally `Good` (every thread state they
can reach) and whose initial values fit the width map. Then every reachable configuration from
which the machine has no step is drained with every thread finished, or has a thread whose next
statement is a loop with no iterations left and a true condition. -/
theorem stuck {I : HProp} {Q : Nat → Regs → HProp} {N : Nat} {C0 : Cfg} {hs : Nat → Heap}
    {hI : Heap} {M : OModel} {Cf : OCfg} (G : GInv I Q N C0 hs hI)
    (hg : ∀ t < N, ∀ p, TReach (C0.ts t) p → Good w p.1 p.2)
    (hw0 : ∀ a v, C0.mem a = some v → fits w a v) (hr : OReach M N C0.toO Cf)
    (hst : ∀ Cf', ¬ OStep M N Cf Cf') :
    (Cf.Drained ∧ ∀ t < N, (Cf.ts t).1 = .skip) ∨ ∃ t < N, Exh (Cf.ts t) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Progress.stuck G hg hw0 hr hst

/-- **The spin mutex (`mutex_lock`, `mutex_unlock`) cannot get stuck.** -/
def spinLive : MutexLive spinMutex := Silmaril.Proofs.X86.Concurrency.Cir.Progress.spinLive

/-- **The spin mutex with `mutex_unlock_sc` cannot get stuck.** -/
def spinScLive : MutexLive spinMutexSc := Silmaril.Proofs.X86.Concurrency.Cir.Progress.spinScLive

/-- **The futex mutex (`fmutex_lock`, `fmutex_unlock`) cannot get stuck.** -/
def fmutexLive : MutexLive Mutex.Futex.fmutex :=
  Silmaril.Proofs.X86.Concurrency.Cir.Progress.fmutexLive

end Silmaril.X86.Concurrency.Cir.Progress
