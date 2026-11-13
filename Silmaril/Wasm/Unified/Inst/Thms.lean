module

public import Silmaril.Wasm.Unified.Inst.Defs
public import Silmaril.Wasm.Unified.Model.Thms

/-!
# The unified Wasm institution: first consequences

* `sat_incl_iff`: the satisfaction condition along an inclusion of feature sets (Lime below
  3.0, 3.0 below FX): a sentence of the smaller signature holds in a model of the larger one
  iff it holds in the reduct, which forgets the extra opcodes.
* `Equiv.reduct`: elementarily equivalent models have elementarily equivalent reducts.
* `sat_congr_calls`: satisfaction only reads the observations of the calls a sentence mentions.
* `sat_update_iff`: **a model updated on one opcode (an erratum) satisfies the same sentences
  that avoid that opcode**; `sat_map_update_iff`: and the same translated sentences along any
  morphism whose image avoids it.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified

open CategoryTheory Silmaril.Wasm.Atlas

variable {In B : Type}

/-- The satisfaction condition along an inclusion of feature sets. -/
theorem sat_incl_iff {S S' : FSig} (h : FSig.Sub S S') (M : Model In B S') (φ : Sen In B S) :
    Sat M (φ.map (FSig.incl h)) ↔ Sat (M.reduct (FSig.incl h)) φ :=
  sat_map_iff _ M φ

/-- Elementarily equivalent models have elementarily equivalent reducts. -/
theorem Equiv.reduct {S S' : FSig} (σ : S ⟶ S') {M M' : Model In B S'} (h : Equiv M M') :
    Equiv (M.reduct σ) (M'.reduct σ) := fun φ =>
  (sat_map_iff σ M φ).symm.trans ((h _).trans (sat_map_iff σ M' φ))

/-- Satisfaction only reads the observations of the calls a sentence mentions. -/
theorem sat_congr_calls {C : Type} {P : C → Prop} {obs obs' : C → Set B}
    (h : ∀ c, P c → obs c = obs' c) : (φ : BSen C B) → callsIn P φ → (φ.Sat obs ↔ φ.Sat obs')
  | .always c _, hc => by rw [BSen.Sat, BSen.Sat, h c hc]
  | .may c _, hc => by rw [BSen.Sat, BSen.Sat, h c hc]
  | .and s t, hc => and_congr (sat_congr_calls h s hc.1) (sat_congr_calls h t hc.2)
  | .top, _ => Iff.rfl

/-- **An erratum is invisible to sentences that avoid its opcode.** -/
theorem sat_update_iff {S : FSig} (M : Model In B S) (o : S.Op)
    (v : List Imm → List M.alg.D → List Handler → M.alg.I) (φ : Sen In B S) (h : φ.Avoids o) :
    Sat (M.update o v) φ ↔ Sat M φ :=
  sat_congr_calls (fun x hx => Model.obs_update M o v x.1 x.2 hx) φ h

/-- **An erratum outside the image of `σ` is invisible to translated sentences.** -/
theorem sat_map_update_iff {S S' : FSig} (σ : S ⟶ S') (M : Model In B S') (o : S'.Op)
    (v : List Imm → List M.alg.D → List Handler → M.alg.I) (h : ∀ x, σ.f x ≠ o)
    (φ : Sen In B S) : Sat (M.update o v) (φ.map σ) ↔ Sat M (φ.map σ) := by
  rw [sat_map_iff, sat_map_iff, Model.reduct_update σ M o v h]

end Silmaril.Wasm.Unified
