module

public import Silmaril.Wasm.Wasmi.Observed.Defs
public import Silmaril.Wasm.Atlas.Variant.Thms
public import Silmaril.Wasm.Execution.Core.Sim.Context

/-!
# Runs of a rounding function (proofs)

For a function `local.get 0; t.op` of type `[t] → [t]` at address `a`, the call `a x` runs
`invoke → FRAME (LABEL (local.get 0; t.op)) → FRAME (LABEL (t.const x; t.op))`, then takes the
operator step, then leaves the label and the frame. `run_of` builds this run for any step
relation that contains the Core steps from configurations without a pending quirk redex and the
given operator step under the frame and the label:

* `core_run`: the Core 3.0 run to `t.const z`, for any `z` the profile allows;
* `wasmi_run`: the wasmi 0.40.0 run to `t.const x`, for a rounding operator and a NaN `x`.

The configurations before and after the operator step have no pending quirk redex
(`pending` is computed by `rfl`). New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Wasmi.Observed

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Atlas Silmaril.Wasm.Wasmi.Observed

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The facts about the function at `a` that the runs use. -/
structure RoundFn (s : Store H) (a : Nat) (t : FloatType) (op : FloatUnOp) where
  fi : FuncInst H
  code : Func
  ps : Ty (.list .val)
  rs : Ty (.list .val)
  hf : s.funcs[a]? = some fi
  hcode : fi.code = .wasm code
  hbody : code.body = [.localGet ⟨0⟩, .floatUnOp t op]
  he : Expand fi.type (.func ps rs)
  hps : ps.length = 1
  hrs : rs.length = 1

namespace RoundFn

variable {s : Store H} {a : Nat} {t : FloatType} {op : FloatUnOp} (R : RoundFn s a t op)

/-- The callee frame of `a x`. -/
def frame (x : FloatValue t) : Frame := Frame.forCall R.fi.module [fval t x] R.code.locals

/-- The configuration `FRAME (LABEL code)`. -/
def cfg (x : FloatValue t) (code : List Admin) : Config H :=
  ⟨s, {}, [.frame R.rs.length (R.frame x) [.label R.rs.length [] code]]⟩

theorem local0 (x : FloatValue t) : (R.frame x).local? ⟨0⟩ = some (some (fval t x)) := by
  simp [frame, Frame.forCall, Frame.local?, Idx.toNat]

/-- The call step. -/
theorem step_call (x : FloatValue t) :
    Execution.Core.Step P host (invoke s a [fval t x])
      (R.cfg x [.plain (.localGet ⟨0⟩), .plain (.floatUnOp t op)]) := by
  have h := Step.callRefFunc (P := P) (host := host) (f := {}) (vs := [fval t x])
    (c := .callRefType R.fi.type) trivial R.hf R.he (by simp [R.hps]) R.hcode
  have hb : expression R.code.body = [.plain (.localGet ⟨0⟩), .plain (.floatUnOp t op)] := by
    rw [R.hbody]
    rfl
  rw [hb] at h
  simpa [invoke, R.hf, cfg, frame] using h

/-- The `local.get` step. -/
theorem step_get (x : FloatValue t) :
    Execution.Core.Step P host (R.cfg x [.plain (.localGet ⟨0⟩), .plain (.floatUnOp t op)])
      (R.cfg x [.plain (.floatConst t x), .plain (.floatUnOp t op)]) := by
  have h : Execution.Core.Step P host ⟨s, R.frame x, [.plain (.localGet ⟨0⟩)]⟩
      ⟨s, R.frame x, [(fval t x).toAdmin]⟩ :=
    .variable (.localGet (R.local0 x))
  exact .ctxtFrame (.ctxtLabel (Sim.Step.append_right h [.plain (.floatUnOp t op)]))

/-- Leaving the label. -/
theorem step_label (x y : FloatValue t) :
    Execution.Core.Step P host (R.cfg x [.plain (.floatConst t y)])
      ⟨s, {}, [.frame R.rs.length (R.frame x) [.plain (.floatConst t y)]]⟩ :=
  .ctxtFrame (Step.labelVals (vs := [fval t y]))

/-- Leaving the frame. -/
theorem step_frame (x y : FloatValue t) :
    Execution.Core.Step P host ⟨s, {}, [.frame R.rs.length (R.frame x) [.plain (.floatConst t y)]]⟩
      ⟨s, {}, vals [fval t y]⟩ :=
  Step.frameVals (vs := [fval t y]) (by simp [R.hrs])

/-- **The run of `a x`** for a step relation `Rel` that contains the Core steps from
configurations without a pending quirk redex, and the operator step to `t.const y`. -/
theorem run_of {Rel : Config H → Config H → Prop}
    (hcore : ∀ c c', pending c.code = false → Execution.Core.Step P host c c' → Rel c c')
    {x y : FloatValue t}
    (hop : Rel (R.cfg x [.plain (.floatConst t x), .plain (.floatUnOp t op)])
      (R.cfg x [.plain (.floatConst t y)])) :
    Relation.ReflTransGen Rel (invoke s a [fval t x]) ⟨s, {}, vals [fval t y]⟩ := by
  have h₀ := hcore _ _ rfl (R.step_call (op := op) x)
  have h₁ := hcore _ _ rfl (R.step_get (op := op) x)
  have h₃ := hcore _ _ rfl (R.step_label x y)
  have h₄ := hcore _ _ rfl (R.step_frame x y)
  exact .head h₀ (.head h₁ (.head hop (.head h₃ (.single h₄))))

include R in
/-- **The Core 3.0 run** to any result the profile allows. -/
theorem core_run {x z : FloatValue t} (hz : floatUnOpP P t op x z) :
    Steps P host (invoke s a [fval t x]) ⟨s, {}, vals [fval t z]⟩ :=
  R.run_of (fun _ _ _ h => h) (.ctxtFrame (.ctxtLabel (.numeric (.floatUnOp hz))))

include R in
/-- **The wasmi 0.40.0 run**: a rounding operator on a NaN returns the input. -/
theorem wasmi_run (hop : IsRound op = true) {x : FloatValue t} (hx : isNaNB t x = true) :
    Relation.ReflTransGen (Silmaril.Wasm.Wasmi.Observed.Step P host) (invoke s a [fval t x])
      ⟨s, {}, vals [fval t x]⟩ :=
  R.run_of (fun _ _ hp h => .inl ⟨hp, h⟩)
    (.inr (.frame (.label (.base (Quirk.roundNaN hop hx)))))

end RoundFn

end Silmaril.Proofs.Wasm.Wasmi.Observed
