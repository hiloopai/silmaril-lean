module

public import Silmaril.Wasm.SingleThreaded.Determinism.FamDet

@[expose] public section

/-! # Determinism of the `VectorStep` family in the deterministic profile

Under canonical NaNs and `$ND = false` every vector result relation is a
function.
-/

namespace Silmaril.Wasm.SingleThreaded.Det

open Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation

variable {H : Type}

theorem forall₂_functional {α β : Type _} {R : α → β → Prop}
    (hR : ∀ a b₁ b₂, R a b₁ → R a b₂ → b₁ = b₂) :
    ∀ {xs : List α} {ys zs : List β}, List.Forall₂ R xs ys → List.Forall₂ R xs zs → ys = zs
  | [], [], [], .nil, .nil => rfl
  | _ :: _, _ :: _, _ :: _, .cons h₁ t₁, .cons h₂ t₂ => by
    rw [hR _ _ _ h₁ h₂, forall₂_functional hR t₁ t₂]

theorem vrelaxedTruncRel_false_fun {p : RelaxedParams} {sx : Signedness} {src : FloatShape}
    {a r₁ r₂ : V128} (h₁ : vrelaxedTruncRel false p sx src a r₁)
    (h₂ : vrelaxedTruncRel false p sx src a r₂) : r₁ = r₂ := by
  have hR : ∀ t x b₁ b₂, relaxedTrunc false p t sx x b₁ → relaxedTrunc false p t sx x b₂ →
      b₁ = b₂ := by
    intro t x b₁ b₂ hb₁ hb₂
    rw [relaxedTrunc_false_iff] at hb₁ hb₂
    rw [hb₁, hb₂]
  cases src with
  | f32x4 =>
    obtain ⟨c₁, hc₁, rfl⟩ := h₁
    obtain ⟨c₂, hc₂, rfl⟩ := h₂
    rw [forall₂_functional (hR _) hc₁ hc₂]
  | f64x2 =>
    obtain ⟨c₁, hc₁, rfl⟩ := h₁
    obtain ⟨c₂, hc₂, rfl⟩ := h₂
    rw [forall₂_functional (hR _) hc₁ hc₂]

section
variable {o : GrowKind → Nat → Nat → Nat → Bool}

/-- `relaxed_min`/`relaxed_max` are `min`/`max` with `$ND = false`. -/
def canonBinOp : VecFloatBinOp → VecFloatBinOp
  | .relaxedMin => .min
  | .relaxedMax => .max
  | op => op

@[simp] theorem VecFloatUnOpRel_det {sh : FloatShape} {op : FloatUnOp} {a r : V128} :
    VecFloatUnOpRel (Profile.deterministic o) sh op a r ↔ vunopFloat sh op a = r := eq_comm

@[simp] theorem VecFloatBinOpRel_det {sh : FloatShape} {op : VecFloatBinOp} {a b r : V128} :
    VecFloatBinOpRel (Profile.deterministic o) sh op a b r ↔
      vbinopFloat sh (canonBinOp op) a b = some r := by
  cases op <;> exact Iff.rfl

@[simp] theorem VecFloatTernOpRel_det {sh : FloatShape} {op : VecFloatTernOp} {a b c r : V128} :
    VecFloatTernOpRel (Profile.deterministic o) sh op a b c r ↔
      sh.invLanes (List.zipWith3 (fmaddCanon sh.floatType op)
        (sh.lanesOf a) (sh.lanesOf b) (sh.lanesOf c)) = r := eq_comm

theorem VecExtBinOpRel_fun {P : Profile} {sh₁ sh₂ : IntShape} {op : VecExtBinOp}
    {a b r₁ r₂ : V128} (h₁ : VecExtBinOpRel P sh₁ sh₂ op a b r₁)
    (h₂ : VecExtBinOpRel P sh₁ sh₂ op a b r₂) : r₁ = r₂ := by
  cases op with
  | relaxedDotS => exact h₁.trans h₂.symm
  | extmul => exact Option.some.inj (h₁.symm.trans h₂)
  | dotS => exact Option.some.inj (h₁.symm.trans h₂)

theorem VecConvertRel_det_fun {src tgt : Shape} {op : VecConvertOp} {a r₁ r₂ : V128}
    (h₁ : VecConvertRel (Profile.deterministic o) src tgt op a r₁)
    (h₂ : VecConvertRel (Profile.deterministic o) src tgt op a r₂) : r₁ = r₂ := by
  cases op with
  | relaxedTrunc sx z =>
    cases src with
    | float fs => exact vrelaxedTruncRel_false_fun h₁.2 h₂.2
    | int _ => exact h₁.elim
  | extend => exact Option.some.inj (h₁.symm.trans h₂)
  | convert => exact Option.some.inj (h₁.symm.trans h₂)
  | truncSat => exact Option.some.inj (h₁.symm.trans h₂)
  | demoteZero => exact Option.some.inj (h₁.symm.trans h₂)
  | promoteLow => exact Option.some.inj (h₁.symm.trans h₂)

end

theorem VectorStep.det {o : GrowKind → Nat → Nat → Nat → Bool} {l₁ l₂ r₁ r₂ : List Admin}
    {p : List Val} (h₁ : VectorStep (Profile.deterministic o) l₁ r₁)
    (h₂ : VectorStep (Profile.deterministic o) l₂ r₂) (hl : l₁ = vals p ++ l₂) :
    p = [] ∧ r₁ = r₂ := by
  cases h₁ <;> cases h₂ <;> (fam_pre <;> first
    | fam_post
    | (rename_i h₁ h₂; rw [VecExtBinOpRel_fun h₁ h₂])
    | (rename_i h₁ h₂; rw [VecConvertRel_det_fun h₁ h₂]))

end Silmaril.Wasm.SingleThreaded.Det
