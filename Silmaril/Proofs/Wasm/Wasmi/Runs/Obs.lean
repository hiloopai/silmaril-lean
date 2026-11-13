module

public import Silmaril.Proofs.Wasm.Wasmi.Runs.Inv
public import Silmaril.Proofs.Wasm.Wasmi.Runs.Quirk

/-!
# Full behaviour sets of a rounding-function call (proofs)

`behaviours_chain`: for any step relation whose successors along the six configurations of a
rounding-function call are known (one successor each, except the operator, which has one per
allowed result `z`), the behaviours of the call are exactly `returns [t.const z]` for the
allowed `z`: no trap, no exception, no divergence, no other value.

* `RoundFn.core_behaviours`: Core 3.0, with the results `floatUnOpP P t op x`;
* `RoundFn.model_behaviours`: the wasmi 0.40.0 model, with the results `wUnOpP P t op x`. Away
  from the operator, no quirk redex is pending, so the model's successors are Core's
  (`step_of_not_pending`); at the operator, either no quirk redex is pending (Core's results)
  or one is, and the only step is the quirk step (`step_of_pending`, `ctx_quirk_inv`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Wasmi.Runs

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas Silmaril.Wasm.Wasmi.Observed Silmaril.Wasm.Wasmi.Runs
open Silmaril.Proofs.Wasm.Wasmi.Observed (RoundFn pending_op)
open Silmaril.Wasm.Logic.Hoare (not_step_vals)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Behaviours along a known chain of successors.** -/
theorem behaviours_chain {Rel : Config H → Config H → Prop} {t : FloatType}
    {c₀ c₁ c₂ : Config H} {c₃ c₄ : FloatValue t → Config H} {s : Store H} {f : Frame}
    (Z : FloatValue t → Prop)
    (n₀ : ∀ r : Result, c₀.code ≠ r.toAdmin) (n₁ : ∀ r : Result, c₁.code ≠ r.toAdmin)
    (n₂ : ∀ r : Result, c₂.code ≠ r.toAdmin) (n₃ : ∀ z (r : Result), (c₃ z).code ≠ r.toAdmin)
    (n₄ : ∀ z (r : Result), (c₄ z).code ≠ r.toAdmin)
    (h₀ : ∀ c', Rel c₀ c' ↔ c' = c₁) (h₁ : ∀ c', Rel c₁ c' ↔ c' = c₂)
    (h₂ : ∀ c', Rel c₂ c' ↔ ∃ z, Z z ∧ c' = c₃ z) (h₃ : ∀ z c', Rel (c₃ z) c' ↔ c' = c₄ z)
    (h₄ : ∀ z c', Rel (c₄ z) c' ↔ c' = ⟨s, f, vals [fval t z]⟩)
    (h₅ : ∀ z c', ¬ Rel ⟨s, f, vals [fval t z]⟩ c') :
    Variant.behavioursR Rel c₀ = {b | ∃ z, Z z ∧ b = .returns [fval t z]} := by
  rw [behavioursR_det n₀ h₀, behavioursR_det n₁ h₁, behavioursR_succ _ n₂ h₂]
  ext b
  constructor
  · rintro ⟨c', ⟨z, hz, rfl⟩, hb⟩
    rw [behavioursR_det (n₃ z) (h₃ z), behavioursR_det (n₄ z) (h₄ z), behavioursR_vals (h₅ z)]
      at hb
    exact ⟨z, hz, hb⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨c₃ z, ⟨z, hz, rfl⟩, ?_⟩
    rw [behavioursR_det (n₃ z) (h₃ z), behavioursR_det (n₄ z) (h₄ z), behavioursR_vals (h₅ z)]
    rfl

namespace RoundFn

variable {s : Store H} {a : Nat} {t : FloatType} {op : FloatUnOp} (R : RoundFn s a t op)

theorem invoke_ne (x : FloatValue t) (r : Result) : (invoke s a [fval t x]).code ≠ r.toAdmin := by
  cases r with
  | values vs =>
    exact vals_ne_of_mem (a := .callRefType ((s.funcs[a]?.map FuncInst.type).getD default))
      (by simp [Admin.val?]) (by simp [invoke]) vs
  | throw a => simp [invoke, Result.toAdmin, vals]
  | trap => simp [invoke, Result.toAdmin, vals]

theorem cfg_ne (x : FloatValue t) (code : List Admin) (r : Result) :
    (R.cfg x code).code ≠ r.toAdmin :=
  frame_ne_toAdmin _ _ _ r

theorem frameCfg_ne (x y : FloatValue t) (r : Result) : (frameCfg R x y).code ≠ r.toAdmin :=
  frame_ne_toAdmin _ _ _ r

/-- The Core successors of the call. -/
theorem core_succ_call (x : FloatValue t) (c' : Config H) :
    Execution.Core.Step P host (invoke s a [fval t x]) c' ↔
      c' = R.cfg x [.plain (.localGet ⟨0⟩), .plain (.floatUnOp t op)] :=
  ⟨RoundFn.core_call R x, fun h => h ▸ R.step_call x⟩

theorem core_succ_get (x : FloatValue t) (c' : Config H) :
    Execution.Core.Step P host (R.cfg x [.plain (.localGet ⟨0⟩), .plain (.floatUnOp t op)]) c' ↔
      c' = R.cfg x [.plain (.floatConst t x), .plain (.floatUnOp t op)] :=
  ⟨RoundFn.core_get R x, fun h => h ▸ R.step_get x⟩

theorem core_succ_op (x : FloatValue t) (c' : Config H) :
    Execution.Core.Step P host (R.cfg x [.plain (.floatConst t x), .plain (.floatUnOp t op)]) c' ↔
      ∃ z, floatUnOpP P t op x z ∧ c' = R.cfg x [.plain (.floatConst t z)] := by
  refine ⟨RoundFn.core_op R x, ?_⟩
  rintro ⟨z, hz, rfl⟩
  exact .ctxtFrame (.ctxtLabel (.numeric (.floatUnOp hz)))

theorem core_succ_label (x y : FloatValue t) (c' : Config H) :
    Execution.Core.Step P host (R.cfg x [.plain (.floatConst t y)]) c' ↔ c' = frameCfg R x y :=
  ⟨RoundFn.core_label R x y, fun h => h ▸ R.step_label x y⟩

theorem core_succ_frame (x y : FloatValue t) (c' : Config H) :
    Execution.Core.Step P host (frameCfg R x y) c' ↔ c' = ⟨s, {}, vals [fval t y]⟩ :=
  ⟨RoundFn.core_frame R x y, fun h => h ▸ R.step_frame x y⟩

include R in
/-- **Every Core 3.0 behaviour of `a x`**: exactly `returns [t.const z]` for the `z` the
profile allows. -/
theorem core_behaviours (x : FloatValue t) :
    Variant.behavioursR (Execution.Core.Step P host) (invoke s a [fval t x]) =
      {b | ∃ z, floatUnOpP P t op x z ∧ b = .returns [fval t z]} :=
  behaviours_chain _ (invoke_ne x) (RoundFn.cfg_ne R x _) (RoundFn.cfg_ne R x _) (fun _ => RoundFn.cfg_ne R x _)
    (fun z => frameCfg_ne R x z) (RoundFn.core_succ_call R x) (RoundFn.core_succ_get R x) (RoundFn.core_succ_op R x)
    (RoundFn.core_succ_label R x) (RoundFn.core_succ_frame R x) (fun _ _ => not_step_vals)

/-! ## The wasmi 0.40.0 model -/

theorem pending_call (x : FloatValue t) : pending (invoke s a [fval t x]).code = false := by
  cases t <;> rfl

theorem pending_get (x : FloatValue t) :
    pending (R.cfg x [.plain (.localGet ⟨0⟩), .plain (.floatUnOp t op)]).code = false := rfl

theorem pending_label (x y : FloatValue t) :
    pending (R.cfg x [.plain (.floatConst t y)]).code = false := by
  cases t <;> rfl

theorem pending_frame (x y : FloatValue t) : pending (frameCfg R x y).code = false := by
  cases t <;> rfl

theorem pending_vals1 (y : FloatValue t) :
    pending (⟨s, {}, vals [fval t y]⟩ : Config H).code = false := by
  cases t <;> rfl

theorem fire_op (x : FloatValue t) :
    fire (R.cfg x [.plain (.floatConst t x), .plain (.floatUnOp t op)]).code =
      (R.cfg x [.plain (.floatConst t x)]).code := by
  cases t <;> rfl

/-- The model's successors at the operator. -/
theorem model_succ_op (x : FloatValue t) (c' : Config H) :
    Silmaril.Wasm.Wasmi.Observed.Step P host
        (R.cfg x [.plain (.floatConst t x), .plain (.floatUnOp t op)]) c' ↔
      ∃ z, wUnOpP P t op x z ∧ c' = R.cfg x [.plain (.floatConst t z)] := by
  by_cases hq : IsRound op = true ∧ isNaNB t x = true
  · have hp := pending_op R x
    rw [hq.1, hq.2] at hp
    simp only [wUnOpP, hq, and_self, ↓reduceIte, exists_eq_left]
    constructor
    · intro h
      rw [step_of_pending hp h, fire_op]
      rfl
    · rintro rfl
      exact .inr (.frame (.label (.base (Quirk.roundNaN hq.1 hq.2))))
  · have hp : pending (R.cfg x [.plain (.floatConst t x), .plain (.floatUnOp t op)]).code =
        false := by
      rw [pending_op R x]
      simpa using hq
    simp only [wUnOpP, hq, ↓reduceIte]
    rw [step_of_not_pending hp]
    exact RoundFn.core_succ_op R x c'

include R in
/-- **Every behaviour of `a x` in the wasmi 0.40.0 model**: exactly `returns [t.const z]` for
the `z` that `wUnOpP` allows. -/
theorem model_behaviours (x : FloatValue t) :
    Variant.behavioursR (Silmaril.Wasm.Wasmi.Observed.Step P host) (invoke s a [fval t x]) =
      {b | ∃ z, wUnOpP P t op x z ∧ b = .returns [fval t z]} := by
  refine behaviours_chain (c₁ := R.cfg x [.plain (.localGet ⟨0⟩), .plain (.floatUnOp t op)])
    (s := s) (f := {}) _ (invoke_ne x) (RoundFn.cfg_ne R x _) (RoundFn.cfg_ne R x _)
    (fun _ => RoundFn.cfg_ne R x _) (fun z => frameCfg_ne R x z) ?_ ?_
    (RoundFn.model_succ_op R x) ?_ ?_ ?_
  · intro c'
    rw [step_of_not_pending (pending_call x)]
    exact RoundFn.core_succ_call R x c'
  · intro c'
    rw [step_of_not_pending (RoundFn.pending_get R x)]
    exact RoundFn.core_succ_get R x c'
  · intro z c'
    rw [step_of_not_pending (RoundFn.pending_label R x z)]
    exact RoundFn.core_succ_label R x z c'
  · intro z c'
    rw [step_of_not_pending (RoundFn.pending_frame R x z)]
    exact RoundFn.core_succ_frame R x z c'
  · intro z c' h
    rw [step_of_not_pending (pending_vals1 z)] at h
    exact not_step_vals h

end RoundFn

end Silmaril.Proofs.Wasm.Wasmi.Runs
