module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecAgreeLift

/-!
# From the original script to the corrected one, at `VOk` values

`hasTyp_20toV`: what `simEnv20 B` types in a scope that binds term variables only, at a
relation-free type naming no family directly and a `VOk` value, `simEnv20V B` types: through
round 4's relation-free transfer to `simEnv20S`, round 4's `STORE` repair to `simEnv20T`, and
`VecAgree.hasTyp_TtoV`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (ValsOnly)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)

/-- **Typing moves from `simEnv20` to `simEnv20V`** at relation-free family-free types and `VOk`
values, in scopes binding term variables only. -/
theorem hasTyp_20toV {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {t : Typ}
    (hr : (Silmaril.Wasm.SpecTec.Sim.Round7.Script.evTyp t).all (RelFree.rfEvB RelFree.bad20) = true)
    (hf : ffT t) {v : Value} (hv : VOk v) (h : HasTyp (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) ρ t v) :
    HasTyp (simEnv20V B) ρ t v := by
  have hS : HasTyp (StepFix.simEnv20S B) ρ t v := by
    rw [RelFree.simEnv20S_eq B]
    refine (RelFree.hasTyp_withRels_iff (RelFree.defsGood_simEnv20 B) (RelFree.typsGood_simEnv20 B)
      ?_ ?_ (RelFree.goodEvs_of_all hr)).2 h
    · intro p hp; rw [hρ.2.1] at hp; simp at hp
    · intro p hp; rw [hρ.1] at hp; simp at hp
  have hT := StoreAgree.hasTyp_repair (StoreAgree.envSame20T B) (StoreAgree.typRepair20T B) hS
  refine hasTyp_TtoV ?_ ?_ (Or.inl hf) hv hT
  · intro p hp; rw [hρ.1] at hp; cases hp
  · intro p hp; rw [hρ.1] at hp; cases hp

end Silmaril.Wasm.SpecTec.Sim20.VecAgree
