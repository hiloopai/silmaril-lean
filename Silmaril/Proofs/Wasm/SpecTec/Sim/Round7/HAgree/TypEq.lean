module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.HAgree.Typ
public import Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.Defs

/-!
# Round 7, memory SIMD: `simEnv B₁` and `simEnv B₂` type alike away from `$vbytes_`

`AgreeOff` is symmetric, so `VDecl.tAgreeAt` gives both inequalities. At every fuel, on an `RG`
type in a scope with `DefsOk` definition variables and `TypsG` type variables, the two
environments type every value alike (`hasTyp_eq`, fuel-free `hasTyp_iff`). Hence:

* `quantsOk_iff`: a rule's quantifiers are well typed alike when their types are `RG`;
* `typedV_iff`: `TypedV` at an `RG` type;
* `typedD_withVBytes_iff`: `TypedD` at `withVBytes B` and at `B`, for every `B`. Unlike the
  `$utf8` case (`TypAgree.hasTyp_config_iff`), no condition on the configuration is needed: no type
  `Step` reaches refers to `$vbytes_`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round7.Script (evTyp stepReach le_antisymm' mem_of_find?)

variable {B₁ B₂ : Builtins}

/-- **`simEnv B₁` and `simEnv B₂` type alike at an `RG` type**, at every fuel. -/
theorem hasTyp_eq (hB : AgreeOff B₁ B₂) (n : Nat) {ρ : VarEnv} {t : Typ} {v : Value}
    (hD : DefsOk ρ) (hT : TypsG ρ) (ht : RG (evTyp t)) :
    hasTyp n (simEnv B₁) ρ t v = hasTyp n (simEnv B₂) ρ t v :=
  le_antisymm' ((tAgreeAt B₁ B₂ hB n).typ ρ t v hD hT ht)
    ((tAgreeAt B₂ B₁ (agreeOff_symm hB) n).typ ρ t v hD hT ht)

/-- `hasTyp_eq`, fuel-free. -/
theorem hasTyp_iff (hB : AgreeOff B₁ B₂) {ρ : VarEnv} {t : Typ} {v : Value} (hD : DefsOk ρ)
    (hT : TypsG ρ) (ht : RG (evTyp t)) : HasTyp (simEnv B₁) ρ t v ↔ HasTyp (simEnv B₂) ρ t v := by
  simp only [HasTyp, hasTyp_eq hB _ hD hT ht]

/-- **The quantifiers of a rule are well typed alike** when their types are `RG`. -/
theorem quantsOk_iff (hB : AgreeOff B₁ B₂) {ρ : VarEnv} {qs : List Param} (hD : DefsOk ρ)
    (hT : TypsG ρ) (hq : ∀ x t, Param.expP x t ∈ qs → RG (evTyp t)) :
    QuantsOk (simEnv B₁) ρ qs ↔ QuantsOk (simEnv B₂) ρ qs := by
  unfold QuantsOk
  refine forall_congr' fun x => forall_congr' fun t => forall_congr' fun hx => ?_
  exact exists_congr fun w => and_congr_right fun _ => hasTyp_iff hB hD hT (hq x t hx)

/-- A scope binding term variables only is `DefsOk` and `TypsG`. -/
theorem defsOk_typsG_of_valsOnly {ρ : VarEnv} (h : ValsOnly ρ) : DefsOk ρ ∧ TypsG ρ := by
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · rw [h.2.1] at hp; simp at hp
  · rw [h.1] at hp; simp at hp

/-- **`TypedV` at an `RG` type.** -/
theorem typedV_iff (hB : AgreeOff B₁ B₂) {t : Typ} {v : Value} (ht : RG (evTyp t)) :
    TypedV (simEnv B₁) t v ↔ TypedV (simEnv B₂) t v := by
  unfold TypedV
  refine forall_congr' fun ρ => forall_congr' fun hρ => ?_
  have h := defsOk_typsG_of_valsOnly hρ
  exact hasTyp_iff hB h.1 h.2 ht

theorem config_reach : (2, "config") ∈ stepReach := by decide +kernel

theorem rg_config : RG (evTyp (.varT "config" [])) := by
  simp only [evTyp, Round7.Script.evArgs, rg_cons_ref, rg_nil, and_true]
  exact ⟨config_reach, by decide, by decide, by decide⟩

/-- **`TypedD` reads alike at `withVBytes B` and at `B`**, at every configuration. -/
theorem typedD_withVBytes_iff (B : Builtins) {H : Type} (hn : H → String)
    (c : Silmaril.Wasm.Execution.Core.Config H) :
    MemSimd.TypedD (simEnv (MemSimd.withVBytes B)) hn c ↔ MemSimd.TypedD (simEnv B) hn c :=
  hasTyp_iff (agreeOff_withVBytes B) HAgree.defsOk_empty typsG_empty rg_config

end Silmaril.Wasm.SpecTec.Sim.Round7.HAgree
