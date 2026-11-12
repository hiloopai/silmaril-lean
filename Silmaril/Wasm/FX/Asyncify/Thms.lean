module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Example
public import Silmaril.Wasm.Models.FXAsyncPC.Thms
public import Silmaril.Wasm.Atlas.Defs

/-!
# Asyncify as a family of comorphisms: results

The header of `Defs`: the family `scheme V st o` of asyncify instances, indexed by a strategy
`st` (`unwind`: stack unwinding with call-site checks; `unwindDispatch`: the same with
first-order records and `br_table` resume dispatch) and an optimization `o` (which call sites
are instrumented: `Opt.whole`, or `Opt.selective S` for a suspension analysis `S`), from the
one-shot handler kernel `FXAsync.sstep` to a machine without continuations.

**The general theorems.**

* `correct_of_sim`: an instance whose target behaviours are those of a deterministic machine is
  correct as soon as, for each program of its fragment, some stuttering relational simulation
  (`SimRel`) relates the initial configurations. Proof: `beh_eq_of_simRel`.
* `comorphism`: a correct instance is a comorphism of behaviour charts (`Atlas.BTrans.ofEq`,
  direction `equal`, every sentence) from the kernel chart restricted to the instance's fragment
  (`srcChart`) to the instance's target chart (`Scheme.tgtChart`). Points are (program, branch
  test) pairs, calls are (function, arguments) pairs, observations `Obs`.

**The instances.**

* **`unwind_correct`**: for every optimization `o`, the `unwind` instance is correct on its
  fragment: for a sound analysis (`Sound o.instr P`: functions outside `o.instr` have calm code,
  with no `suspend`, no `resume` and calls only outside `o.instr`), a call in the kernel and the
  same call on `compPO o P` have the same behaviours. The simulation (`simRel_sel`) relates
  stacks whose waiting frames are flagged checked or unchecked; unchecked frames only ever have
  calm frames above them, so unwinding never reaches one.
* `dispatch_run_eq`, **`dispatch_correct`**: for every optimization, the `unwindDispatch` and
  `unwind` instances have the same target behaviours on every compiled program (by
  `FXAsyncPC.pc_correct`), so the dispatch instance is correct on the same fragment.
  `strategies`: this is a comorphism between the two target charts.
* `whole_dom`: whole-program instrumentation has no hypothesis (every program is in its
  fragment).

**The existing results as instances.**

* `lower_correct_init'`: `FXAsync.lower_correct_init` (the kernel lowering `compP` and `tstep`)
  is the `(unwind, whole)` instance (`compO_whole`: `compO .whole = comp`), re-derived here from
  the selective simulation without `FXAsync`'s proof; `unwind_whole_via_kernel` derives the same
  instance from `FXAsync.sim_step` through `correct_of_sim` instead.
* `kernel_pc_correct'`: `FXAsyncPC.kernel_pc_correct` is the `(unwindDispatch, whole)` instance.
  The `br_table` resume prologue on Core 3.0 (`FXDispatch.dispatch_joins`) is the Core code that
  `fstep`'s dispatch stands for; it is not a theorem about this family.

**Optimizations compared.** `selective_eq_whole`: on a sound analysis, selective and
whole-program instrumentation have the same target behaviours. `sel_shorter`: on the example the
selective code is one check shorter. `noneS_wrong`: with an unsound analysis the lowering is
wrong (the source returns `[2]`, the target traps), so the fragment is needed.

What this does **not** say: the kernel is an abstract machine (its relation to `StepFX'` is
`FXAsyncFX`, `FXAsyncBack`, `FXAsyncSus`), and the targets are abstract asyncify machines, not
Core 3.0 `Step` (pieces in `FXCoreSave`, `FXDispatch`). CPS and state-machine strategies, and
liveness-based save sets, are not defined. See `docs/projects/wasm-binaryen-tooling.md`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.Models.FXAsyncPC (fstep annP bodies rootCode fInit)

variable {V : Type}

/-! ## The general theorems -/

/-- `SimRel` is `RelSim.RSim`: one notion of stuttering relational simulation. -/
theorem simRel_iff_rsim {C D : Type} {s : C → Res C V} {t : D → Res D V} {R : C → D → Prop} :
    SimRel s t R ↔ RelSim.RSim R s t :=
  Silmaril.Proofs.Wasm.FX.Asyncify.simRel_iff_rsim

/-- **Equal behaviours under a stuttering relational simulation** (`RelSim.beh_eq_of_rsim`). -/
theorem beh_eq_of_simRel {C D : Type} {s : C → Res C V} {t : D → Res D V} {R : C → D → Prop}
    (hsim : SimRel s t R) {x : C} {y : D} (hxy : R x y) : beh s x = beh t y :=
  RelSim.beh_eq_of_rsim (simRel_iff_rsim.mp hsim) hxy

/-- **An instance given by a machine is correct if a relational simulation relates the initial
configurations.** -/
theorem correct_of_sim {A : Scheme V} {D : Type} (step : A.TP → (V → Bool) → D → Res D V)
    (init : Nat → List (SV V) → D)
    (hrun : ∀ Q test f args, A.run Q test f args = beh (step Q test) (init f args))
    (hsim : ∀ P, A.dom P → ∀ test f args, ∃ R : SCfg V → D → Prop,
      SimRel (sstep P test) (step (A.compile P) test) R ∧ R (sInit f args) (init f args)) :
    A.Correct := by
  intro P hP test f args
  obtain ⟨R, hR, hi⟩ := hsim P hP test f args
  rw [hrun]
  exact (Silmaril.Proofs.Wasm.FX.Asyncify.beh_eq_of_simRel hR hi).symm

/-- The kernel chart on a fragment `dom`: points are programs with a branch test, calls are
functions with arguments. -/
def srcChart (dom : Prog (Ins V) → Prop) : Chart :=
  BChart (Prog (Ins V) × (V → Bool)) (Nat × List (SV V)) (Obs V) (fun p => dom p.1)
    (fun p c => srcRun p.1 p.2 c.1 c.2)

/-- The target chart of an instance. -/
def Scheme.tgtChart (A : Scheme V) : Chart :=
  BChart (A.TP × (V → Bool)) (Nat × List (SV V)) (Obs V) (fun _ => True)
    (fun q c => A.run q.1 q.2 c.1 c.2)

/-- **A correct instance is a comorphism** (equal on every behaviour sentence). -/
def Scheme.comorphism (A : Scheme V) (h : A.Correct) : Transition (srcChart A.dom) A.tgtChart :=
  BTrans.ofEq (fun p => (A.compile p.1, p.2)) id (fun _ _ => trivial)
    (fun p hp c => h p.1 hp p.2 c.1 c.2)

theorem comorphism_dir (A : Scheme V) (h : A.Correct) : (A.comorphism h).dir = .equal := rfl

/-! ## The instances -/

/-- Whole-program instrumentation has no hypothesis. -/
theorem whole_dom (P : Prog (Ins V)) : Opt.whole.Dom P :=
  Silmaril.Proofs.Wasm.FX.Asyncify.sound_whole P

/-- **Stack unwinding is correct for every optimization, on its fragment.** -/
theorem unwind_correct (o : Opt) : (scheme V .unwind o).Correct :=
  fun P hP test f args => (Silmaril.Proofs.Wasm.FX.Asyncify.beh_sel o P test f args hP).symm

/-- The dispatch strategy and the unwinding strategy agree on every compiled program. -/
theorem dispatch_run_eq (o : Opt) (Q : Prog (TIns V)) (test : V → Bool) (f : Nat)
    (args : List (SV V)) :
    (scheme V .unwindDispatch o).run Q test f args = (scheme V .unwind o).run Q test f args :=
  (Silmaril.Wasm.Models.FXAsyncPC.pc_correct Q (rootCode f) test _ _
    (Silmaril.Wasm.Models.FXAsyncPC.init_related Q f args)).symm

/-- **Stack unwinding with `br_table` dispatch is correct for every optimization.** -/
theorem dispatch_correct (o : Opt) : (scheme V .unwindDispatch o).Correct :=
  fun P hP test f args => (dispatch_run_eq o _ test f args).trans (unwind_correct o P hP test f args)

/-- The two strategies' targets are related by a comorphism (equal on every sentence). -/
def strategies (o : Opt) :
    Transition (scheme V .unwind o).tgtChart (scheme V .unwindDispatch o).tgtChart :=
  BTrans.ofEq (fun q => q) id (fun _ _ => trivial)
    (fun q _ c => dispatch_run_eq o q.1 q.2 c.1 c.2)

/-- Every instance of the family is correct. -/
theorem scheme_correct (st : Strategy) (o : Opt) : (scheme V st o).Correct := by
  cases st with
  | unwind => exact unwind_correct o
  | unwindDispatch => exact dispatch_correct o

/-! ## The existing results as instances -/

/-- `FXAsync.lower_correct_init`, re-derived as the `(unwind, whole)` instance. -/
theorem lower_correct_init' (P : Prog (Ins V)) (test : V → Bool) (f : Nat) (args : List (SV V)) :
    beh (sstep P test) (sInit f args) = beh (tstep (compP P) test) (tInit f args) := by
  rw [← Silmaril.Proofs.Wasm.FX.Asyncify.compPO_whole]
  exact (unwind_correct .whole P (whole_dom P) test f args).symm

/-- The `(unwind, whole)` instance from `FXAsync`'s own simulation, through `correct_of_sim`. -/
theorem unwind_whole_via_kernel : (scheme V .unwind .whole).Correct := by
  refine correct_of_sim (A := scheme V .unwind .whole) (fun Q test => tstep Q test) tInit
    (fun _ _ _ _ => rfl) fun P _ test f args => ⟨fun x y => y = trC x, ?_, rfl⟩
  have hP : (scheme V .unwind .whole).compile P = compP P :=
    Silmaril.Proofs.Wasm.FX.Asyncify.compPO_whole P
  rw [hP]
  exact Silmaril.Proofs.Wasm.FX.Asyncify.simRel_of_simStep (sim_step P test)

/-- `FXAsyncPC.kernel_pc_correct`, re-derived as the `(unwindDispatch, whole)` instance. -/
theorem kernel_pc_correct' (P : Prog (Ins V)) (test : V → Bool) (f : Nat) (args : List (SV V)) :
    beh (sstep P test) (sInit f args) =
      beh (fstep (annP (compP P)) (bodies (compP P) (rootCode f)) test) (fInit f args) := by
  rw [← Silmaril.Proofs.Wasm.FX.Asyncify.compPO_whole]
  exact (dispatch_correct .whole P (whole_dom P) test f args).symm

/-! ## Optimizations compared -/

/-- **On a sound analysis, selective and whole-program asyncify have the same behaviours.** -/
theorem selective_eq_whole (S : Nat → Bool) (P : Prog (Ins V)) (hS : Sound S P)
    (test : V → Bool) (f : Nat) (args : List (SV V)) :
    beh (tstep (compPO (.selective S) P) test) (tInit f args) =
      beh (tstep (compPO .whole P) test) (tInit f args) :=
  (unwind_correct (.selective S) P hS test f args).trans
    (unwind_correct .whole P (whole_dom P) test f args).symm

open Silmaril.Proofs.Wasm.FX.Asyncify (selP selS noneS) in
/-- On the example, the selective code is one check shorter. -/
theorem sel_shorter :
    (compO (V := Nat) (.selective selS) [.push 1, .call 5, .suspend 0 1, .push 0]).length + 1 =
      (compO (V := Nat) .whole [.push 1, .call 5, .suspend 0 1, .push 0]).length :=
  Silmaril.Proofs.Wasm.FX.Asyncify.sel_shorter

open Silmaril.Proofs.Wasm.FX.Asyncify (selP selS) in
/-- The example's analysis is sound, and all three machines return `[2]`. -/
theorem sel_example :
    Sound selS selP ∧
    beh (sstep selP Silmaril.Proofs.Wasm.Models.FXAsync.natTest) (sInit 2 []) = {.done [.val 2]} ∧
    beh (tstep (compPO (.selective selS) selP) Silmaril.Proofs.Wasm.Models.FXAsync.natTest)
      (tInit 2 []) = {.done [.val 2]} :=
  ⟨Silmaril.Proofs.Wasm.FX.Asyncify.selS_sound, Silmaril.Proofs.Wasm.FX.Asyncify.sel_src_beh,
    Silmaril.Proofs.Wasm.Models.FXAsync.beh_of_stop Silmaril.Proofs.Wasm.FX.Asyncify.sel_tgt_run⟩

open Silmaril.Proofs.Wasm.FX.Asyncify (selP noneS) in
/-- **An unsound analysis breaks the lowering.** -/
theorem noneS_wrong :
    ¬ Sound noneS selP ∧
    beh (sstep selP Silmaril.Proofs.Wasm.Models.FXAsync.natTest) (sInit 2 []) ≠
      beh (tstep (compPO (.selective noneS) selP) Silmaril.Proofs.Wasm.Models.FXAsync.natTest)
        (tInit 2 []) :=
  ⟨Silmaril.Proofs.Wasm.FX.Asyncify.noneS_unsound, Silmaril.Proofs.Wasm.FX.Asyncify.noneS_wrong⟩

/-- info: 'Silmaril.Wasm.FX.Asyncify.scheme_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scheme_correct

/-- info: 'Silmaril.Wasm.FX.Asyncify.noneS_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms noneS_wrong

end Silmaril.Wasm.FX.Asyncify
