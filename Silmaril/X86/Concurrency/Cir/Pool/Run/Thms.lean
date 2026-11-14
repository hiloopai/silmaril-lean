module

public import Silmaril.X86.Concurrency.Cir.Pool.Run.Defs
public import Silmaril.X86.Concurrency.Cir.Pool.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.Pool.Run
import Silmaril.Proofs.X86.Concurrency.Cir.Pool.Values

/-!
# Concrete runs of a worker pool: theorems (non-vacuity)

PROVED (standard axioms). `Wp.any_mutex` and `exHash_correct` speak about finished, drained
states only; these theorems show that such states exist, with both mutexes, so the statements
are not vacuous.

* `Run.runT_reach`, `Run.runAll_reach`: a concrete run built by `runT`/`runAll` (block steps
  added to `tsoStepT`) is a run of the CIR-native TSO machine;
* `Run.start_cfg`: `Run.start P M L` is the linked pool;
* `exHash_spin_finishes`, `exHash_fmutex_finishes`: the concrete hashing pool, linked with
  the spin mutex or the futex mutex at loop bound `2`, has a finished, drained TSO run.
  Worker `1` takes and runs all three jobs and exits; worker `0` then finds the queue empty,
  exits, and its wait sees every job back and both workers out. The run is a schedule checked by
  kernel evaluation, not an exhaustive exploration.

Further runs (PROVED, kernel evaluation of schedules):

* `Run.runS_reach`: schedules of slices `(thread, steps)` are TSO runs;
* `exHash_spin_conc_finishes`, `exHash_fmutex_conc_finishes`: interleaved, contended runs at
  loop bound `8` in which both workers hold a job at once, ending finished and drained;
* `noLock_violates`: with the mutex removed (holes replaced by `mfence`), a finished, drained TSO
  run runs job `0` twice and violates the goal, so the goal is not implied by the code shape.

No-deadlock statement:

* `poolNoDeadlockAsStated_false`: the no-deadlock statement is false (a job whose function
  has the wrong length; a 200-step TSO schedule ends drained with the worker stuck at it);
* `poolNoDeadlock_deadMutex`: the restated `Task.poolNoDeadlock` also holds for
  `Run.deadMutex`, whose lock is never granted, so it is a safety property, not lock liveness.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Pool

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Robust (CSt)
open Silmaril.X86.Concurrency.Cir.Mutex (Iface spinMutex)

namespace Run

/-- **A concrete run of one thread is a TSO run.** -/
theorem runT_reach {fn : List Nat → List Nat} {N t : Nat} (f : Nat) (c : CSt) :
    OReach .tso N c.ocfg (runT fn N t f c).ocfg :=
  Silmaril.Proofs.X86.Concurrency.Cir.Pool.runT_reach f c

/-- **A concrete run of a schedule is a TSO run.** -/
theorem runAll_reach {fn : List Nat → List Nat} {N fuel : Nat} (ts : List Nat) (c : CSt) :
    OReach .tso N c.ocfg (runAll fn N fuel c ts).ocfg :=
  Silmaril.Proofs.X86.Concurrency.Cir.Pool.runAll_reach ts c

/-- **The concrete start is the linked pool.** -/
theorem start_cfg (P : Wp) (M : Iface) (L : Nat) : (start P M L).cfg = P.client.link M L :=
  Silmaril.Proofs.X86.Concurrency.Cir.Pool.start_cfg P M L

/-- **A concrete run of a schedule of slices is a TSO run**. -/
theorem runS_reach {fn : List Nat → List Nat} {N : Nat} (l : List (Nat × Nat)) (c : CSt) :
    OReach .tso N c.ocfg (runS fn N c l).ocfg :=
  Silmaril.Proofs.X86.Concurrency.Cir.Pool.runS_reach l c

/-- A finished, drained schedule run of the linked pool. -/
theorem finishes_of_check {P : Wp} {M : Iface} {L : Nat} {fn : List Nat → List Nat}
    {fuel : Nat} {ts : List Nat}
    (h : ((runAll fn P.K fuel (start P M L) ts).doneB P.K &&
      (runAll fn P.K fuel (start P M L) ts).drainedB) = true) :
    ∃ Cf : OCfg, OReach .tso P.K (P.client.link M L).toO Cf ∧ Cf.Drained ∧
      (∀ t < P.K, (Cf.ts t).1 = .skip) := by
  obtain ⟨hd, hf⟩ := Silmaril.Proofs.X86.Concurrency.Cir.Pool.final_of_checks h
  refine ⟨_, ?_, hd, hf⟩
  rw [← Silmaril.Proofs.X86.Concurrency.Cir.Pool.start_toO]
  exact runAll_reach ts _

/-- A finished, drained run of a schedule of slices of the linked pool. -/
theorem finishes_of_checkS {P : Wp} {M : Iface} {L : Nat} {fn : List Nat → List Nat}
    {l : List (Nat × Nat)}
    (h : ((runS fn P.K (start P M L) l).doneB P.K && (runS fn P.K (start P M L) l).drainedB)
      = true) :
    ∃ Cf : OCfg, OReach .tso P.K (P.client.link M L).toO Cf ∧ Cf.Drained ∧
      (∀ t < P.K, (Cf.ts t).1 = .skip) := by
  obtain ⟨hd, hf⟩ := Silmaril.Proofs.X86.Concurrency.Cir.Pool.final_of_checks h
  refine ⟨_, ?_, hd, hf⟩
  rw [← Silmaril.Proofs.X86.Concurrency.Cir.Pool.start_toO]
  exact runS_reach l _

end Run

theorem exHash_spin_check :
    ((Run.runAll ParHash.crcFn exHash.K 3000 (Run.start exHash spinMutex 2) [1, 0]).doneB
        exHash.K &&
      (Run.runAll ParHash.crcFn exHash.K 3000 (Run.start exHash spinMutex 2) [1, 0]).drainedB)
      = true := by
  decide +kernel

theorem exHash_fmutex_check :
    ((Run.runAll ParHash.crcFn exHash.K 3000 (Run.start exHash Mutex.Futex.fmutex 2)
        [1, 0]).doneB exHash.K &&
      (Run.runAll ParHash.crcFn exHash.K 3000 (Run.start exHash Mutex.Futex.fmutex 2)
        [1, 0]).drainedB) = true := by
  decide +kernel

/-- **Non-vacuity with the spin mutex**: the concrete hashing pool has a finished, drained TSO
run, so `exHash_correct` holds of a real final state. -/
theorem exHash_spin_finishes : ∃ Cf : OCfg,
    OReach .tso 2 (exHash.client.link spinMutex 2).toO Cf ∧ Cf.Drained ∧
      (∀ t < 2, (Cf.ts t).1 = .skip) :=
  Run.finishes_of_check exHash_spin_check

/-- **Non-vacuity with the futex mutex.** -/
theorem exHash_fmutex_finishes : ∃ Cf : OCfg,
    OReach .tso 2 (exHash.client.link Mutex.Futex.fmutex 2).toO Cf ∧ Cf.Drained ∧
      (∀ t < 2, (Cf.ts t).1 = .skip) :=
  Run.finishes_of_check exHash_fmutex_check

/-! ## A contended interleaved run, and a racy mutant

`exHash_spin_finishes`/`exHash_fmutex_finishes` run the threads one after the other (worker `1`
does every job), and loop bound `2` makes any contended spin exhaust. The schedule `conc` below
interleaves slices at loop bound `8`: worker `0` holds the lock with its queue stores still
buffered while worker `1` tries to lock, then both workers hold a job at once (`[qa] = 2`,
`[cur 0] = 0`, `[cur 1] = 1`), and the run ends finished and drained. -/

/-- An interleaved schedule of slices (thread, steps). -/
def conc : List (Nat × Nat) := [(0, 20), (1, 6), (0, 10), (1, 30), (1, 3000), (0, 3000)]

theorem exHash_spin_conc_check :
    let c := Run.runS ParHash.crcFn exHash.K (Run.start exHash spinMutex 8) conc
    let c4 := Run.runS ParHash.crcFn exHash.K (Run.start exHash spinMutex 8) (conc.take 4)
    (c.doneB exHash.K && c.drainedB) = true ∧ Robust.memOf c4.mem exHash.qa = some 2 ∧
      Robust.memOf c4.mem (exHash.cur 0) = some 0 ∧
      Robust.memOf c4.mem (exHash.cur 1) = some 1 := by
  decide +kernel

theorem exHash_fmutex_conc_check :
    let c := Run.runS ParHash.crcFn exHash.K (Run.start exHash Mutex.Futex.fmutex 8) conc
    let c4 := Run.runS ParHash.crcFn exHash.K (Run.start exHash Mutex.Futex.fmutex 8)
      (conc.take 4)
    (c.doneB exHash.K && c.drainedB) = true ∧ Robust.memOf c4.mem exHash.qa = some 2 ∧
      Robust.memOf c4.mem (exHash.cur 0) = some 0 ∧
      Robust.memOf c4.mem (exHash.cur 1) = some 1 := by
  decide +kernel

/-- **Non-vacuity, interleaved, spin mutex**: a finished, drained TSO run in which both workers
hold a job at once. -/
theorem exHash_spin_conc_finishes : ∃ Cf : OCfg,
    OReach .tso 2 (exHash.client.link spinMutex 8).toO Cf ∧ Cf.Drained ∧
      (∀ t < 2, (Cf.ts t).1 = .skip) :=
  Run.finishes_of_checkS exHash_spin_conc_check.1

/-- **Non-vacuity, interleaved, futex mutex.** -/
theorem exHash_fmutex_conc_finishes : ∃ Cf : OCfg,
    OReach .tso 2 (exHash.client.link Mutex.Futex.fmutex 8).toO Cf ∧ Cf.Drained ∧
      (∀ t < 2, (Cf.ts t).1 = .skip) :=
  Run.finishes_of_checkS exHash_fmutex_conc_check.1

/-- The racy schedule: both workers read `[qa] = 0` before either advances it, so both take and
run job `0`; one increment of `[da]` is then lost, so the count of returns still reaches `3`. -/
def racy : List (Nat × Nat) := [(0, 8), (1, 8), (0, 25), (1, 25), (0, 3), (1, 3000), (0, 3000)]

theorem noLock_check :
    let c := Run.runS ParHash.crcFn 2 (Run.startNoLock exHash) racy
    (c.doneB 2 && c.drainedB) = true ∧ Robust.memOf c.mem 0x3000 = some 2 := by
  decide +kernel

/-- **The goal is not trivial: without the mutex it fails**. The pool with both
holes replaced by `mfence` has a finished, drained TSO run in which job `0` ran twice: its counter
is `2`, so `exHash.goal` is false there. -/
theorem noLock_violates : ∃ Cf : OCfg,
    OReach .tso 2 (Run.startNoLock exHash).ocfg Cf ∧ Cf.Drained ∧
      (∀ t < 2, (Cf.ts t).1 = .skip) ∧ ¬ exHash.goal (fun t => (Cf.ts t).2) Cf.mem := by
  obtain ⟨h1, h2⟩ := noLock_check
  obtain ⟨hd, hf⟩ := Silmaril.Proofs.X86.Concurrency.Cir.Pool.final_of_checks h1
  refine ⟨_, Run.runS_reach racy _, hd, hf, fun hg => ?_⟩
  have hit : exHash.items[0]'(by decide) ∈ exHash.items := List.getElem_mem _
  have hwf : (exHash.items[0]'(by decide)).wfB = true := by decide +kernel
  have := hg _ hit _ _ (Silmaril.Proofs.X86.Concurrency.Cir.Pool.Item.doneH_cnt_one hwf)
  have h3 : (exHash.items[0]'(by decide)).cnt = 0x3000 := by decide +kernel
  rw [h3] at this
  simp only [Robust.CSt.ocfg] at this
  rw [h2] at this
  cases this

/-! ## The original no-deadlock statement is false -/

namespace Run

/-- A thread whose next statement is such a block has no step. -/
theorem stuckB_noStep : ∀ (s : Stmt) {rs : Regs} {l : Option Lab} {s' : Stmt} {rs' : Regs},
    stuckB s = true → ¬ TStep s rs l s' rs'
  | .seq s1 t, _, _, _, _, h, st => by
    cases st with
    | seq h' => exact stuckB_noStep s1 h h'
    | seqSkip => simp [stuckB, headS] at h
  | .local b, rs, _, _, _, h, st => by
    cases st with
    | blk hspec hi hr ho =>
      simp only [stuckB, headS, Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true',
        decide_eq_false_iff_not] at h
      obtain ⟨⟨⟨⟨hi0, ho0⟩, hrin⟩, hrout⟩, hsp⟩ := h
      rw [hi0, List.length_nil, List.length_eq_zero_iff] at hi
      rw [ho0, List.length_nil, List.length_eq_zero_iff] at ho
      rw [hrout, List.length_nil, List.length_eq_zero_iff] at hr
      subst hi ho hr
      rw [hrin] at hspec
      exact hsp (by simpa using hspec)
  | .skip, _, _, _, _, h, _ | .assign .., _, _, _, _, h, _ | .load .., _, _, _, _, h, _
  | .store .., _, _, _, _, h, _ | .rmw .., _, _, _, _, h, _ | .fence .., _, _, _, _, h, _
  | .futexWait .., _, _, _, _, h, _ | .futexWake .., _, _, _, _, h, _
  | .spawn .., _, _, _, _, h, _ | .join .., _, _, _, _, h, _ | .ite .., _, _, _, _, h, _
  | .loop .., _, _, _, _, h, _ => by simp [stuckB, headS] at h

/-- The run of `badP` with the spin mutex: worker `0` alone, until it cannot step. -/
def badRun : CSt := runS (fun _ => [0]) badP.K (start badP spinMutex 2) [(0, 200)]

end Run

theorem badP_okB : Run.badP.okB = true := by decide +kernel

/-- The run ends drained, with worker `0` at `badJob`'s block. -/
theorem badRun_check : (Run.badRun.drainedB && Run.stuckB (Run.badRun.th 0).1) = true := by
  decide +kernel

/-- **The original statement of `Task.poolNoDeadlock` is false**. `Run.badP` meets
`Wp.Ok`, and linked with the spin mutex at loop bound `2` it reaches, on TSO, a drained
configuration with no step in which worker `0` is neither finished nor out of a loop bound: it is
at the block of `Run.badJob`, whose contract has no output. -/
theorem poolNoDeadlockAsStated_false : ¬ poolNoDeadlockAsStated Run.badP spinMutex := by
  intro H
  have hc := badRun_check
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hd, hb⟩ := hc
  have hDr : Run.badRun.ocfg.Drained :=
    (Silmaril.Proofs.X86.Concurrency.Cir.Pool.final_of_checks (N := 0)
      (by simp [hd, Robust.CSt.doneB])).1
  have hr : OReach .tso Run.badP.K (Run.badP.client.link spinMutex 2).toO Run.badRun.ocfg := by
    rw [← Silmaril.Proofs.X86.Concurrency.Cir.Pool.start_toO]
    exact Run.runS_reach _ _
  have hst : ∀ Cf', ¬ OStep .tso Run.badP.K Run.badRun.ocfg Cf' := by
    intro Cf' st
    have k1 : Run.badP.K = 1 := rfl
    cases st with
    | tau ht hs =>
      rw [k1, Nat.lt_one_iff] at ht
      subst ht
      exact Run.stuckB_noStep _ hb hs
    | buffered ht hs =>
      rw [k1, Nat.lt_one_iff] at ht
      subst ht
      exact Run.stuckB_noStep _ hb hs
    | drained ht hs =>
      rw [k1, Nat.lt_one_iff] at ht
      subst ht
      exact Run.stuckB_noStep _ hb hs
    | flush ht hbuf =>
      rw [hDr] at hbuf
      simp at hbuf
  rcases H (Wp.ok_of_okB badP_okB) 2 .tso _ hr hst with ⟨-, hf⟩ | ⟨t, ht, c, b, h1, -⟩
  · have h0 := hf 0 (by decide)
    simp only [Robust.CSt.ocfg] at h0
    rw [h0] at hb
    simp [Run.stuckB, headS] at hb
  · obtain rfl : t = 0 := by have : Run.badP.K = 1 := rfl; omega
    simp only [Robust.CSt.ocfg] at h1
    simp [Run.stuckB, h1] at hb

/-! ## The restated statement is a safety property, not lock liveness

`Task.poolNoDeadlock` holds even for a mutex whose lock is **never granted**: `deadMutex`'s lock
is a bounded spin on the constant `1`, so every thread that calls it ends out of a loop bound,
which is the second disjunct. It meets `Iface` (its `locked` token is `False`, so `unlock` is
never safely called) and `Progress.MutexLive`. So the Task rules out threads stuck at a
non-loop statement; it does not say that the lock is ever acquired or that a fair run finishes.
That limit form is open. -/

namespace Run

/-- A spin on the constant `1`, `n` rounds left: it never exits normally. -/
def deadSpin (n : Nat) : Stmt := .loop n (.lit 1) .skip

/-- The states of `deadSpin`, with the empty heap. -/
def deadR : Stmt → Regs → Heap → Prop := fun s _ h =>
  h = Heap.empty ∧ ∃ n, s = deadSpin n ∨ s = .seq .skip (deadSpin n)

theorem deadR_post (I : HProp) (Q : Regs → HProp) :
    ∀ s rs h, deadR s rs h → SafeF I Q deadR s rs h := by
  rintro s rs h ⟨rfl, n, rfl | rfl⟩
  · refine ⟨by simp [deadSpin], ?_, ?_⟩
    · intro s' rs' st
      cases st with
      | loopT _ => exact ⟨rfl, _, Or.inr rfl⟩
      | loopF h => simp [Expr.eval, truthy] at h
    · intro l s' rs' st; cases st
  · refine ⟨by simp, ?_, ?_⟩
    · intro s' rs' st
      cases st with
      | seq h => cases h
      | seqSkip => exact ⟨rfl, _, Or.inl rfl⟩
    · intro l s' rs' st
      cases st with
      | seq h => cases h

/-- **A mutex whose lock is never granted**: `lock` is `deadSpin`, `unlock` is `skip`, and the
lock token is `False`. It is an `Iface` (partial correctness). -/
def deadMutex : Iface where
  size := 0
  init := fun _ => Heap.empty
  inv := fun _ R => R
  locked := fun _ _ => False
  lockCode := deadSpin
  unlockCode := fun _ => .skip
  init_dom := by intro l a h; simp [Heap.empty] at h
  init_inv := by
    intro l R hR h _
    have : Heap.union Heap.empty hR = hR := by
      funext a; simp [Heap.union, Silmaril.X86.Sep.BI.SepAlg.pmapUnion, Heap.empty]
    rw [this]; exact h
  locked_excl := by intro l h ⟨_, _, _, _, a, _⟩; exact a
  lock_spec := by
    intro l R J L rs _
    exact ⟨deadR, ⟨rfl, L, Or.inl rfl⟩, deadR_post _ _⟩
  unlock_spec := by intro l R J L rs h _ ⟨_, _, _, _, _, a⟩; exact a.elim

/-- `deadMutex` is `Progress.MutexLive`: its code never gets stuck at a non-loop statement. -/
def deadLive : Progress.MutexLive deadMutex where
  wd := fun _ _ => none
  wd_dom := by intro l a k h; simp at h
  init_fits := by intro l a v h; simp [deadMutex, Heap.empty] at h
  lock_inv := fun _ _ _ _ => Progress.inv_conseq (fun _ h => h) (fun _ _ => trivial)
    (Progress.inv_loop Progress.inv_skip)
  unlock_inv := fun _ _ _ _ => Progress.inv_conseq (fun _ h => h) (fun _ _ => trivial)
    Progress.inv_skip

end Run

/-- **The restated Task holds for a mutex that is never granted**: it is a safety
statement (no thread stuck except at an exhausted loop), not deadlock freedom under fairness. -/
theorem poolNoDeadlock_deadMutex (P : Wp) : Task.poolNoDeadlock P Run.deadMutex :=
  poolNoDeadlock_of_live Run.deadLive P

end Silmaril.X86.Concurrency.Cir.Pool
