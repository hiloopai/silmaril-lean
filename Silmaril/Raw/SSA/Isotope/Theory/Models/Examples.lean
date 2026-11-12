module

public import Silmaril.Raw.SSA.Isotope.Theory.Models.Theories
public import Silmaril.Raw.SSA.Isotope.Theory.Models.Refinement
public import Silmaril.Raw.SSA.Isotope.Theory.Models.RawRefinement

/-!
# Initial model and quotient regressions

These examples exercise the public interfaces at independent universes, retain
let-seq's minimal product/unit assumptions, and check a pure beta equation
through the actual quotient constructor operation.
-/

@[expose] public section
noncomputable section

universe u v w r

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel

namespace Silmaril.Isotope.LetSeq.LocallyNameless.Models.Examples

variable {τ : Type u} [HasProduct τ] [HasUnit τ] {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε]
variable (pureEff : ε) (Γ : Ctx ν τ) (R : TypedRelation ν Φ τ)

example : IsInitial (syntacticModel (Φ := Φ) pureEff Γ) :=
  syntacticModelIsInitial pureEff Γ

example : HasInitial (EquationalModels (Φ := Φ) pureEff Γ) := inferInstance

example : HasInitial (RefinementModels pureEff Γ R) := inferInstance

example (E : EquationalTheory (rawSyntax ν Φ)) : HasInitial (RawModels.EquationalModels E) :=
  inferInstance

/-- Pure beta holds for the descended operation, not just the relation on representatives. -/
example {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
    {A B : τ} (hp : Pure pureEff a) (da : Derivation Φ Γ β a A)
    (db : Derivation Φ Γ (β.snoc A) b B)
    (dc : Derivation Φ Γ β (Tm.instantiate b a) B) :
    (syntacticModel (Φ := Φ) pureEff Γ).algebra.op (Operation.let₁ (β := β) A B)
      (Fin.cases
        ((quotientMap (equationCongruence (Φ := Φ) pureEff Γ)).map (i := ⟨n, β, A⟩) ⟨a, da⟩)
        (fun _ => (quotientMap (equationCongruence (Φ := Φ) pureEff Γ)).map
          (i := ⟨n + 1, β.snoc A, B⟩) ⟨b, db⟩)) =
      (quotientMap (equationCongruence (Φ := Φ) pureEff Γ)).map
        (i := ⟨n, β, B⟩) ⟨Tm.instantiate b a, dc⟩ := by
  let q := quotientMap (equationCongruence (Φ := Φ) pureEff Γ)
  let xs : (j : Fin 2) → Carrier Φ Γ
      ((Operation.let₁ (Φ := Φ) (Γ := Γ) (β := β) A B).argSort j) :=
    Fin.cases ⟨a, da⟩ (fun _ => ⟨b, db⟩)
  have comm := q.comm (Operation.let₁ (β := β) A B) xs
  have args : (fun j => q.map (xs j)) =
      Fin.cases (q.map (i := ⟨n, β, A⟩) ⟨a, da⟩)
        (fun _ => q.map (i := ⟨n + 1, β.snoc A, B⟩) ⟨b, db⟩) := by
    funext j
    fin_cases j <;> rfl
  rw [args] at comm
  exact comm.symm.trans ((quotient_eq_iff (.let₁ da db) dc).2
    (.letBeta hp da.toHasType db.toHasType))

end Silmaril.Isotope.LetSeq.LocallyNameless.Models.Examples

namespace Silmaril.Isotope.LetCase.LocallyNameless.Models.Examples

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε]
variable (pureEff : ε) (Γ : Ctx ν τ) (R : TypedRelation ν Φ τ)

example : IsInitial (syntacticModel (Φ := Φ) pureEff Γ) :=
  syntacticModelIsInitial pureEff Γ

example : HasInitial (EquationalModels (Φ := Φ) pureEff Γ) := inferInstance

example : HasInitial (RefinementModels pureEff Γ R) := inferInstance

example (E : EquationalTheory (rawSyntax ν Φ)) : HasInitial (RawModels.EquationalModels E) :=
  inferInstance

end Silmaril.Isotope.LetCase.LocallyNameless.Models.Examples

namespace Silmaril.Isotope.LetIter.LocallyNameless.Models.Examples

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε]
variable (pureEff : ε) (Γ : Ctx ν τ) (R : TypedRelation ν Φ τ)

example : IsInitial (syntacticModel (Φ := Φ) pureEff Γ) :=
  syntacticModelIsInitial pureEff Γ

example : HasInitial (EquationalModels (Φ := Φ) pureEff Γ) := inferInstance

example : HasInitial (RefinementModels pureEff Γ R) := inferInstance

example (E : EquationalTheory (rawSyntax ν Φ)) : HasInitial (RawModels.EquationalModels E) :=
  inferInstance

/-- The loop body operation retains the continuation state as its newest bound variable. -/
example {n : Nat} (β : BoundCtx τ n) (A B : τ) :
    (signature Φ Γ).argSort (Operation.iter (β := β) A B) 1 =
      ⟨n + 1, β.snoc A, coprod B A⟩ := rfl

end Silmaril.Isotope.LetIter.LocallyNameless.Models.Examples
