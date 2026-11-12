module

public import Silmaril.Wasm.Wasmi.Observed.Defs
public import Silmaril.Wasm.Atlas.Variant.Thms
public import Silmaril.Wasm.Execution.Core.Sim.Context
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# The issue-#2046 reproducer in the wasmi 0.40.0 model (proofs)

The call `f 5 1` of the reproducer store (`Silmaril.Wasm.Wasmi.reproStore`) runs
`invoke → FRAME (LABEL body)`, two `local.get` steps, the comparison `i32.ne 0 1 = 1`, the
`select` of the first operand `7`, then leaves the label and the frame. Every configuration of
this Core 3.0 run has no pending quirk redex (the code has no float instruction; `pending` is
computed by `rfl`), so it is a run of the wasmi 0.40.0 step relation (`run_of`), and the model
returns `7` (`returns7`). `reproFnB` is an executable check of the facts about the function at
address `0` that the run uses; `repro_fn` is its kernel evaluation on the reproducer store.

This is one run: that the model has no other observation of `f 5 1` is not shown here. New
proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Wasmi.Observed

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Atlas Silmaril.Wasm.Wasmi Silmaril.Wasm.Wasmi.Observed

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The facts about the function at address `0` that the reproducer run uses. -/
structure ReproFn (s : Store H) where
  fi : FuncInst H
  code : Func
  ps : Ty (.list .val)
  rs : Ty (.list .val)
  hf : s.funcs[0]? = some fi
  hcode : fi.code = .wasm code
  hbody : code.body = reproBody
  he : Expand fi.type (.func ps rs)
  hps : ps.length = 2
  hrs : rs.length = 1

/-- The executable form of `ReproFn`. -/
def reproFnB (s : Store H) : Bool :=
  match s.funcs[0]? with
  | some fi =>
    (match fi.code with
      | .wasm g =>
        match g.body with
        | [.intConst .i32 a, .localGet x, .intConst .i32 b, .localGet y, .intRelOp .i32 .ne,
            .select none] => decide (a = 7 ∧ x = ⟨0⟩ ∧ b = 0 ∧ y = ⟨1⟩)
        | _ => false
      | .host _ => false) &&
    (match fi.type.expand? with
      | some (.func ps rs) => ps.length == 2 && rs.length == 1
      | _ => false)
  | none => false

theorem reproFn_of {s : Store H} (h : reproFnB s = true) : Nonempty (ReproFn s) := by
  unfold reproFnB at h
  split at h
  · rename_i fi hf
    simp only [Bool.and_eq_true] at h
    obtain ⟨h₁, h₂⟩ := h
    split at h₁
    · rename_i g hg
      split at h₁
      · rename_i a x b y hb
        obtain ⟨rfl, rfl, rfl, rfl⟩ := of_decide_eq_true h₁
        split at h₂
        · rename_i ps rs he
          simp only [Bool.and_eq_true, beq_iff_eq] at h₂
          exact ⟨⟨fi, g, ps, rs, hf, hg, hb, Expand.iff.mpr he, h₂.1, h₂.2⟩⟩
        · cases h₂
      · cases h₁
    · cases h₁
  · cases h

/-- **The reproducer's function** is the body of issue #2046 with two parameters and one
result (kernel evaluation). -/
theorem repro_fn : reproFnB reproStore = true := by decide +kernel

namespace ReproFn

variable {s : Store H} (R : ReproFn s)

/-- The callee frame of `f 5 1`. -/
def frame : Frame := Frame.forCall R.fi.module [Val.i32 5, Val.i32 1] R.code.locals

/-- The configuration `FRAME (LABEL code)`. -/
def cfg (code : List Admin) : Config H :=
  ⟨s, {}, [.frame R.rs.length R.frame [.label R.rs.length [] code]]⟩

theorem local0 : R.frame.local? ⟨0⟩ = some (some (Val.i32 5)) := by
  simp [frame, Frame.forCall, Frame.local?, Idx.toNat]

theorem local1 : R.frame.local? ⟨1⟩ = some (some (Val.i32 1)) := by
  simp [frame, Frame.forCall, Frame.local?, Idx.toNat]

/-- `i32.const`. -/
abbrev ci (x : BitVec 32) : Admin := .plain (.intConst .i32 x)

/-- The call step. -/
theorem step_call :
    Execution.Core.Step P host (invoke s 0 [Val.i32 5, Val.i32 1])
      (R.cfg [ci 7, .plain (.localGet ⟨0⟩), ci 0, .plain (.localGet ⟨1⟩),
        .plain (.intRelOp .i32 .ne), .plain (.select none)]) := by
  have h := Step.callRefFunc (P := P) (host := host) (f := {}) (vs := [Val.i32 5, Val.i32 1])
    (c := .callRefType R.fi.type) trivial R.hf R.he (by simp [R.hps]) R.hcode
  have hb : expression R.code.body = [ci 7, .plain (.localGet ⟨0⟩), ci 0,
      .plain (.localGet ⟨1⟩), .plain (.intRelOp .i32 .ne), .plain (.select none)] := by
    rw [R.hbody]
    rfl
  rw [hb] at h
  simpa [invoke, R.hf, cfg, frame] using h

/-- `local.get 0`. -/
theorem step_get0 :
    Execution.Core.Step P host
      (R.cfg [ci 7, .plain (.localGet ⟨0⟩), ci 0, .plain (.localGet ⟨1⟩),
        .plain (.intRelOp .i32 .ne), .plain (.select none)])
      (R.cfg [ci 7, ci 5, ci 0, .plain (.localGet ⟨1⟩), .plain (.intRelOp .i32 .ne),
        .plain (.select none)]) := by
  have h : Execution.Core.Step P host ⟨s, R.frame, [.plain (.localGet ⟨0⟩)]⟩
      ⟨s, R.frame, [(Val.i32 5).toAdmin]⟩ :=
    .variable (.localGet R.local0)
  exact .ctxtFrame (.ctxtLabel (Sim.Step.vals_left (vs := [Val.i32 7])
    (Sim.Step.append_right h [ci 0, .plain (.localGet ⟨1⟩), .plain (.intRelOp .i32 .ne),
      .plain (.select none)])))

/-- `local.get 1`. -/
theorem step_get1 :
    Execution.Core.Step P host
      (R.cfg [ci 7, ci 5, ci 0, .plain (.localGet ⟨1⟩), .plain (.intRelOp .i32 .ne),
        .plain (.select none)])
      (R.cfg [ci 7, ci 5, ci 0, ci 1, .plain (.intRelOp .i32 .ne), .plain (.select none)]) := by
  have h : Execution.Core.Step P host ⟨s, R.frame, [.plain (.localGet ⟨1⟩)]⟩
      ⟨s, R.frame, [(Val.i32 1).toAdmin]⟩ :=
    .variable (.localGet R.local1)
  exact .ctxtFrame (.ctxtLabel (Sim.Step.vals_left (vs := [Val.i32 7, Val.i32 5, Val.i32 0])
    (Sim.Step.append_right h [.plain (.intRelOp .i32 .ne), .plain (.select none)])))

/-- `i32.ne 0 1`. -/
theorem step_ne :
    Execution.Core.Step P host
      (R.cfg [ci 7, ci 5, ci 0, ci 1, .plain (.intRelOp .i32 .ne), .plain (.select none)])
      (R.cfg [ci 7, ci 5, constI32 (intRelOp .i32 .ne 0 1), .plain (.select none)]) := by
  have h : Execution.Core.Step P host ⟨s, R.frame, [ci 0, ci 1, .plain (.intRelOp .i32 .ne)]⟩
      ⟨s, R.frame, [constI32 (intRelOp .i32 .ne 0 1)]⟩ :=
    .numeric .intRelOp
  exact .ctxtFrame (.ctxtLabel (Sim.Step.vals_left (vs := [Val.i32 7, Val.i32 5])
    (Sim.Step.append_right h [.plain (.select none)])))

/-- `select` takes the first operand, since the condition is `1`. -/
theorem step_select :
    Execution.Core.Step P host
      (R.cfg [ci 7, ci 5, constI32 (intRelOp .i32 .ne 0 1), .plain (.select none)])
      (R.cfg [ci 7]) :=
  .ctxtFrame (.ctxtLabel (.parametric (.selectTrue (v₁ := Val.i32 7) (v₂ := Val.i32 5)
    (by decide))))

/-- Leaving the label. -/
theorem step_label :
    Execution.Core.Step P host (R.cfg [ci 7])
      ⟨s, {}, [.frame R.rs.length R.frame [ci 7]]⟩ :=
  .ctxtFrame (Step.labelVals (vs := [Val.i32 7]))

/-- Leaving the frame. -/
theorem step_frame :
    Execution.Core.Step P host ⟨s, {}, [.frame R.rs.length R.frame [ci 7]]⟩
      ⟨s, {}, vals [Val.i32 7]⟩ :=
  Step.frameVals (vs := [Val.i32 7]) (by simp [R.hrs])

include R in
/-- **The run of `f 5 1` to `7`** for any step relation containing the Core steps from
configurations without a pending quirk redex. -/
theorem run_of {Rel : Config H → Config H → Prop}
    (hcore : ∀ c c', pending c.code = false → Execution.Core.Step P host c c' → Rel c c') :
    Relation.ReflTransGen Rel (invoke s 0 [Val.i32 5, Val.i32 1]) ⟨s, {}, vals [Val.i32 7]⟩ := by
  have h₀ := hcore _ _ rfl (R.step_call (P := P) (host := host))
  have h₁ := hcore _ _ rfl (R.step_get0 (P := P) (host := host))
  have h₂ := hcore _ _ rfl (R.step_get1 (P := P) (host := host))
  have h₃ := hcore _ _ rfl (R.step_ne (P := P) (host := host))
  have h₄ := hcore _ _ rfl (R.step_select (P := P) (host := host))
  have h₅ := hcore _ _ rfl (R.step_label (P := P) (host := host))
  have h₆ := hcore _ _ rfl (R.step_frame (P := P) (host := host))
  exact .head h₀ (.head h₁ (.head h₂ (.head h₃ (.head h₄ (.head h₅ (.single h₆))))))

end ReproFn

/-- **The wasmi 0.40.0 model returns `7` on the reproducer**, at every profile. -/
theorem returns7 (P : Profile) :
    Behaviour.returns [Val.i32 7] ∈ Silmaril.Wasm.Wasmi.Observed.obs P reproPt reproCall := by
  obtain ⟨R⟩ := reproFn_of repro_fn
  exact .inl ⟨_, .values [Val.i32 7], R.run_of (fun _ _ hp h => .inl ⟨hp, h⟩), rfl, rfl⟩

end Silmaril.Proofs.Wasm.Wasmi.Observed
