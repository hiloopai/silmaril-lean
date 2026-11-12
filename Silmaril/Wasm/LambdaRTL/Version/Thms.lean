module

public import Silmaril.Wasm.LambdaRTL.Thms
public import Silmaril.SSA.LambdaRTL.Version.Thms

/-!
# The loop-free Wasm fragment in λSSA, by versioning its λRTL translation

The λRTL translation `trFunc f` of a loop-free fragment function writes Wasm locals in place
(store semantics, no SSA construction). Versioning (#1899, `Silmaril.SSA.LambdaRTL.Version`) turns
**any** acyclic λRTL region into a dominance-scoped SSA program with the same observable
semantics, for pair-lawful models. Composing the two:

* `model_pairLawful`: the Wasm model is pair-lawful;
* `versioned_isSSA`: `Version.versionTop R` is SSA in `Version.initCtx R`;
* `versioned_run_iff`, `versioned_stuck_iff`: for every environment giving version `0` of each
  register its λRTL entry value, the lexical **λSSA** semantics of `versionTop R` has exactly the
  fragment's call outcomes (returns with their value, traps) and is `.error .stuck` exactly when
  the fragment has no derivation.

This is a second, independent route from the Wasm fragment to λSSA, next to the existing
dialect translation `Silmaril.Wasm.SSA.compileFunc` (into the Isotope λSSA); the two have the same
outcomes (`compileFunc_run_iff_evalObs`). No syntactic relation between them is claimed.
-/

@[expose] public section

namespace Silmaril.Wasm.LambdaRTL

open Silmaril.SSA.LambdaRTL
open Silmaril.Wasm.SSA (WVal FragFunc FOut)

/-- The Wasm model is pair-lawful, the hypothesis of versioning. -/
theorem model_pairLawful : model.PairLawful := ⟨fun _ _ => rfl⟩

/-- The versioned translation is dominance-scoped SSA. -/
theorem versioned_isSSA (R : WRegion) : (Version.versionTop R).IsSSA (Version.initCtx R) :=
  Version.versionTop_isSSA R

/-- **Exact simulation through λSSA**: the versioned translation of a loop-free function, read
lexically, has exactly the fragment's call outcomes. -/
theorem versioned_run_iff {f : FragFunc} {R : WRegion} (hf : trFunc f = some R)
    {args : List WVal} (hargs : args.map WVal.type = f.params) {σ : Store}
    (hσ : InitStore f args σ) (ρ : WReg × Nat → RVal) (hρ : ∀ y, ρ (y, 0) = σ y) (o : FOut) :
    f.Run args o ↔ (Version.versionTop R).evalSSA model ρ = obsOf o := by
  rw [Version.versionTop_evalSSA model model_pairLawful R σ ρ hρ]
  exact trFunc_run_iff hf hargs hσ o

/-- **Stuckness through λSSA.** -/
theorem versioned_stuck_iff {f : FragFunc} {R : WRegion} (hf : trFunc f = some R)
    {args : List WVal} (hargs : args.map WVal.type = f.params) {σ : Store}
    (hσ : InitStore f args σ) (ρ : WReg × Nat → RVal) (hρ : ∀ y, ρ (y, 0) = σ y) :
    (¬ ∃ o, f.Run args o) ↔ (Version.versionTop R).evalSSA model ρ = .error .stuck := by
  rw [Version.versionTop_evalSSA model model_pairLawful R σ ρ hρ]
  exact trFunc_stuck_iff hf hargs hσ

/-- The λSSA environment of a call: version `0` of each register holds its λRTL entry value. -/
def initEnv (f : FragFunc) (args : List WVal) : WReg × Nat → RVal :=
  fun p => initStore f args p.1

theorem initEnv_spec (f : FragFunc) (args : List WVal) (y : WReg) :
    initEnv f args (y, 0) = initStore f args y := rfl

/-- `x + 1` on `i32` returns `42` on `41` through the λSSA reading of its versioned translation
(`exampleInc` is loop-free, so `trFunc` is defined). -/
example : ∃ R, trFunc Silmaril.Wasm.SSA.exampleInc = some R ∧
    (Version.versionTop R).evalSSA model (initEnv Silmaril.Wasm.SSA.exampleInc [.i32 41]) =
      obsOf (.ret (some (.i32 42))) := by
  cases hf : trFunc Silmaril.Wasm.SSA.exampleInc with
  | none =>
    have h : (trFunc Silmaril.Wasm.SSA.exampleInc).isSome = true := by decide
    rw [hf] at h
    cases h
  | some R =>
    refine ⟨R, rfl, ?_⟩
    exact (versioned_run_iff hf rfl (initStore_spec _ _) _ (initEnv_spec _ _) _).1
      (Silmaril.Wasm.SSA.exampleInc_run)

end Silmaril.Wasm.LambdaRTL
