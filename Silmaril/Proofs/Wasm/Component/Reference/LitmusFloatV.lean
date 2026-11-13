module

public import Silmaril.Proofs.Wasm.Component.Reference.FloatVSound
public import Silmaril.Proofs.Wasm.Component.Reference.Litmus

/-!
# Litmus: an `f32` in a variant payload

`floatVariantS` exports `tag-plus-bits(v: variant { c(f32), cx(u32) }) -> u32` over the adder
core module. The `f32` payload shares the `i32` joined slot with the `u32` payload, so the
reference lowers an `f32` payload by `lowerFloat` and then `encodeFloat` (two C7 choices). The
hypotheses of `Simple.sound_floatV` hold (`floatVariantS_good`, `floatVariantS_inst`,
`floatVariantS_arity`), and:

* `floatVariantS_sound`: every behaviour of calling `tag-plus-bits` on `c(x)` is the IR
  observation of the call on `c(y)` for some admissible lowering `y` of `x`
  (`NanLower prof .f32 x y`), at every profile and component choice profile;
* `floatVariantS_sound_deterministic`: under the deterministic component profile, on
  `c(canonicalizeNaN .f32 x)`.

The result type is `u32`: `Simple.Arity` allows one flat result, and a variant with a payload
flattens to at least two slots, so a variant cannot be returned in the fragment.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Litmus

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Component (ProfileKind)
open Silmaril.Wasm.Component.Value (NanLower)
open Silmaril.Wasm.Numerics (Profile)

theorem floatVariantS_good : floatVariantS.Good :=
  ⟨by decide, by
    intro x hx
    simp only [floatVariantS, List.mem_singleton] at hx
    subst hx
    exact ⟨"f", rfl⟩⟩

theorem floatVariantS_inst : floatVariantS.Inst := binMod_inst instSummary_add _

theorem floatVariantS_arity : floatVariantS.Arity := by
  intro x hx
  simp only [floatVariantS, List.mem_singleton] at hx
  subst hx
  decide

/-- **An `f32` in a variant payload**: a call of `tag-plus-bits` on `c(x)` is the IR call on
`c(y)` for an admissible lowering `y` of `x`. -/
theorem floatVariantS_sound (P : Profile) (prof : ProfileKind) (x : BitVec 32)
    (b : Silmaril.Wasm.Component.Reference.Outcome)
    (hb : b ∈ exportBehaviours prof (refHost P) () floatVariantS.toRef []
      floatVariantS.exports[0].name [toRefVal (.variant 0 (some (.f32 x)))]) :
    ∃ y, NanLower prof .f32 x y ∧
      IRObsFV (k := floatVariantS.toComp.exports.length) (floatVariantS.toComp.den (modSem P))
        ⟨0, by decide⟩ [.u32] [.variant 0 (some (.f32 y))] b := by
  obtain ⟨vs', hn, -, ho⟩ := Simple.sound_floatV P prof floatVariantS floatVariantS_good
    floatVariantS_inst floatVariantS_arity ⟨0, by decide⟩ [.variant 0 (some (.f32 x))] rfl b hb
  obtain ⟨v, vs, w, ws, e₁, rfl, hv, hvs⟩ := hn
  obtain ⟨rfl, rfl⟩ := List.cons.inj e₁
  obtain ⟨-, rfl⟩ := hvs
  obtain ⟨i, pl, pl', e₂, rfl, hc⟩ := hv
  obtain ⟨rfl, rfl⟩ := Val.variant.inj e₂
  obtain ⟨v₁, w₁, e₃, rfl, h₁⟩ := hc
  cases e₃
  obtain ⟨x', y, e₄, rfl, hy⟩ := h₁
  cases e₄
  exact ⟨y, hy, ho⟩

/-- **Under the deterministic component profile** the IR is called on the canonicalised
payload. -/
theorem floatVariantS_sound_deterministic (P : Profile) (x : BitVec 32)
    (b : Silmaril.Wasm.Component.Reference.Outcome)
    (hb : b ∈ exportBehaviours .deterministic (refHost P) () floatVariantS.toRef []
      floatVariantS.exports[0].name [toRefVal (.variant 0 (some (.f32 x)))]) :
    IRObsFV (k := floatVariantS.toComp.exports.length) (floatVariantS.toComp.den (modSem P))
      ⟨0, by decide⟩ [.u32]
      [.variant 0 (some (.f32 (Silmaril.Wasm.Component.ABI.canonicalizeNaN .f32 x)))] b :=
  Simple.sound_floatV_deterministic P floatVariantS floatVariantS_good floatVariantS_inst
    floatVariantS_arity ⟨0, by decide⟩ [.variant 0 (some (.f32 x))] rfl b hb

end Silmaril.Proofs.Wasm.Component.Reference.Litmus
