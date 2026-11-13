module

public import Silmaril.Compiler.Core.Verified.PrintfCall.Defs
public import Silmaril.Compiler.Core.Verified.StateExpr.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-! # The three unsequenced printf operands

The integer operand may read State slots. Run it inside the same arena as the
callee and the decayed format literal, recording its read accesses and keeping
all objects and prior output. This is the input boundary of a formatted statement.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.PrintfInputs

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open PrintfStd PrintfStmt StrMem

abbrev EExp := Expr Codec.wireModel Unit Unit Sym

/-- Decaying a literal cannot start a C call. -/
theorem fmtTask_noCall {t : EExp} {lit : Sym} (h : fmtTask t = some lit) : hasCCall t = false := by
  unfold fmtTask at h
  obtain ⟨⟨t1, e1, r1⟩, q1, h⟩ := bind_some h; try dsimp only at h
  obtain ⟨lit', q2, h⟩ := bind_some h
  obtain ⟨⟨t2, e2, r2⟩, q3, h⟩ := bind_some h; try dsimp only at h
  obtain ⟨⟨t1', n⟩, q4, h⟩ := bind_some h; try dsimp only at h
  obtain ⟨t2', q5, h⟩ := bind_some h
  obtain ⟨A0, P0, b0, rfl⟩ := wseqOf_inv q1
  obtain ⟨A1, a1, u1, rfl⟩ := pureSym_inv q2
  obtain ⟨A2, P2, b2, rfl⟩ := wseqOf_inv q3
  obtain ⟨A3, a4, u4, a5, u5, ct, a6, u6, rfl, _⟩ := shiftOf_inv q4
  obtain ⟨A7, a8, u8, a9, u9, rfl⟩ := pureSpecified_inv q5
  simp [hasCCall]

variable (file : Program) (labels : Labels)

/-- The input arena computes a State expression at runtime. Its accesses only
read, so the format and callee tasks cannot race with it. -/
theorem unseq_reaches {t0 t1 t2 : EExp} {w0 : Fold.WVal}
    (h0 : ExitCall.calleeTask file t0 = some w0) {lit : Sym} (h1 : fmtTask t1 = some lit)
    {t : StateExpr.Term} (h2 : StateExpr.term file t2 = some t) {env : Env}
    {σ : StateExpr.Key → Int} (ok : t.Ok σ) {sid saddr : Int}
    (hl : env.lookup lit = some (.object (.pointer (.allocated sid saddr)))) {cs : List Int}
    (ann : List Annot) (k : List Frame) (m : Mem.Concrete.State) (str : StrObj m sid saddr cs)
    (locs : StateExpr.Locs env m σ t) :
    ∃ m' xs, ReturnConst.Reaches file labels
      ⟨.effectExpr (.mk ann (.unseq [t0, t1, t2])) env, k, m⟩
      ⟨.value (.tuple [runtimeValue w0, .loaded (.specified (.pointer (.allocated sid saddr))),
        IntExpr.spec (t.val σ)]), .annotations xs :: k, m'⟩ ∧
      (∀ a ∈ xs, a.write = false) ∧ LoadTask.Touched m m' ∧ Keeps m m' := by
  obtain ⟨xs, m2, fr, hfr, reads, touched, r2⟩ :=
    StateExpr.term_runs (file := file) (labels := labels) t h2 ok [] m locs
  have task2 : Interleave.TaskRuns file labels false ⟨.effectExpr t2 env, [], m⟩
      (IntExpr.spec (t.val σ)) xs m2 := by
    refine ⟨fr, by simpa using r2, ?_⟩
    rcases hfr with ⟨rfl, rfl⟩ | rfl <;> simp [annotationsOnly]
  have keep2 : Keeps m m2 := by
    obtain ⟨l, u, rfl⟩ := touched
    exact ((Keeps.refl m).location l).lastUsed u
  obtain ⟨l1, r1⟩ := fmtTask_runs file labels h1 hl m2 (str.keeps keep2)
  obtain ⟨l0, r0⟩ := ExitCall.calleeTask_runs file labels h0 env {m2 with currentLocation := l1}
  have flag2 : Interleave.taskFlag false k
      [(0, .effectExpr t0 env, []), (1, .effectExpr t1 env, [])] = false := by
    simp [Interleave.taskFlag, Interleave.controlHasCCall_effectExpr,
      ExitCall.calleeTask_noCall file h0, fmtTask_noCall h1]
  have flag1 : Interleave.taskFlag false k [(0, .effectExpr t0 env, [])] = false := by
    simp [Interleave.taskFlag, Interleave.controlHasCCall_effectExpr, ExitCall.calleeTask_noCall file h0]
  have flag0 : Interleave.taskFlag false k [] = false := by simp [Interleave.taskFlag]
  have run : Interleave.TasksRun file labels false k
      [(0, .effectExpr t0 env, []), (1, .effectExpr t1 env, []), (2, .effectExpr t2 env, [])] m
      [(0, runtimeValue w0, []), (1, .loaded (.specified (.pointer (.allocated sid saddr))), []),
        (2, IntExpr.spec (t.val σ), xs)] {m2 with currentLocation := l0} :=
    .snoc (flag2 ▸ task2) (.snoc (flag1 ▸ r1) (.snoc (flag0 ▸ r0) .nil))
  have arena := Interleave.unseq_runs file labels (annots := ann) (es := [t0, t1, t2])
    (env := env) (by simpa [Interleave.unseqTasks] using run) (by
      intro x hx a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · cases ha
      · cases ha
      · exact reads a ha)
  refine ⟨_, xs, Interleave.reaches_of_local file labels (by simpa using arena), reads,
    touched.trans ⟨l0, m2.lastUsed, rfl⟩, keep2.trans ((Keeps.refl m2).location l0)⟩

/-- Overflow in an open operand escapes the entire printf input arena before either
argument object is created. Earlier callee and format tasks need not execute. -/
theorem unseq_fails {t0 t1 t2 : EExp} {w0 : Fold.WVal}
    (h0 : ExitCall.calleeTask file t0 = some w0) {lit : Sym} (h1 : fmtTask t1 = some lit)
    {t : StateExpr.Term} (h2 : StateExpr.term file t2 = some t) {env : Env}
    {σ : StateExpr.Key → Int} (bad : ¬ t.Ok σ)
    (ann : List Annot) (k : List Frame) (m : Mem.Concrete.State)
    (locs : StateExpr.Locs env m σ t) :
    ArenaFail.Fails file labels false
      ⟨.effectExpr (.mk ann (.unseq [t0, t1, t2])) env, k, m⟩ IntExpr.overflow := by
  let pending : List (Nat × (Control × List Frame)) :=
    [(0, .effectExpr t0 env, []), (1, .effectExpr t1 env, [])]
  have flag : Interleave.taskFlag false k pending = false := by
    simp [pending, Interleave.taskFlag, Interleave.controlHasCCall_effectExpr,
      ExitCall.calleeTask_noCall file h0, fmtTask_noCall h1]
  have hp : Interleave.Pending pending 2 := by
    refine ⟨by simp [pending], ?_⟩
    intro task ht
    simp only [pending, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> exact Interleave.activeCall_effectExpr _ _
  have fail : ArenaFail.Fails file labels (Interleave.taskFlag false k pending)
      ⟨.effectExpr t2 env, [], m⟩ IntExpr.overflow := by
    rw [flag]
    exact StateExpr.term_fails t h2 bad [] m locs
  have start : Interleave.LocalReaches file labels false
      ⟨.effectExpr (.mk ann (.unseq [t0, t1, t2])) env, k, m⟩
      ⟨.interleave [] (pending ++ [(2, .effectExpr t2 env, [])]), k, m⟩ :=
    .single (.next (Interleave.requestAux_unseq file labels m ann [t0, t1, t2] env k false)
      (Interleave.plain_interleave _ _))
  exact ArenaFail.Fails.pre file labels start (ArenaFail.fail_task file labels hp fail)

end Silmaril.Compile.Core.Verified.PrintfInputs
