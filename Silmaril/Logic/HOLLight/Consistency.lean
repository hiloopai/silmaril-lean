module

public import Silmaril.Logic.HOLLight.Soundness

@[expose] public section

/-!
# The standard model of classical HOL Light

This constructs a model, including the infinity axiom, in every universe.
The initial theory contains exactly the schematic eta and selection axioms
and the closed infinity assertion. No object-level axiom is added to Lean.
-/

namespace Silmaril.Logic.HOLLight

universe u

theorem initialSignature_valid : initialSignature.Valid := by
  simp [initialSignature, Signature.Valid]

/-- The empty signature has no uninterpreted constants to assign. -/
def Model.standard : Model.{u} initialSignature where
  toTypeModel := TypeModel.standard
  constant := fun _ _ h _ => nomatch h

/-- The three classical axioms hold in every full-function model defined here. -/
theorem Model.models_classical {sig : Signature} (M : Model.{u} sig) :
    Models M classicalTheory := by
  intro p hp
  simp only [classicalTheory, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · intro ρ ν
    exact ⟨_, Eval.eta trivial (.fvar BoundEnv.empty 0 ⟨trivial, trivial⟩),
      Carrier.eta_valid _ _ _⟩
  · intro ρ ν
    exact ⟨_, Eval.selection (.fvar BoundEnv.empty 0 ⟨trivial, trivial⟩)
      (.fvar BoundEnv.empty 1 trivial), Carrier.selection_valid _ _ _⟩
  · intro ρ ν
    exact ⟨_, Eval.infinity, Carrier.infinity_valid⟩

theorem standard_models_classical : Models Model.standard.{u} classicalTheory :=
  Model.standard.models_classical

/-- The axioms are well typed independently of their semantic validity. -/
theorem classicalTheory_wellFormed (sig : Signature) : classicalTheory.WellFormed sig := by
  intro p hp
  simp only [classicalTheory, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact HasType.eta trivial trivial (.fvar 0 ⟨trivial, trivial⟩)
  · exact HasType.selection trivial (.fvar 0 ⟨trivial, trivial⟩) (.fvar 1 trivial)
  · exact HasType.infinity

/-- Any model of an explicitly supplied theory rules out a closed derivation
of falsity. Arbitrary extra object axioms remain an explicit hypothesis. -/
theorem consistent_of_model {sig : Signature} {theory : Theory}
    (M : Model.{u} sig) (model : Models M theory) :
    ¬ Derives sig theory ∅ Tm.falsity := by
  intro proof
  let ρ : TypeValuation.{u} := fun _ => Carrier.unit
  let ν : FreeEnv M ρ := fun _ A => Classical.choice (A.denote M.toTypeModel ρ).property
  have valid := proof.sound M model ρ ν (by intro p hp; simp at hp)
  exact Holds.not_falsity valid

/-- Classical HOL Light is consistent relative to Lean's classical metatheory. -/
theorem classical_consistent : ¬ Derives initialSignature classicalTheory ∅ Tm.falsity :=
  consistent_of_model Model.standard.{0} standard_models_classical

/-- No model of the initial theory can validate falsity, at any universe level. -/
theorem standard_not_valid_falsity : ¬ Valid Model.standard.{u} Tm.falsity := by
  intro valid
  let ρ : TypeValuation.{u} := fun _ => Carrier.unit
  let ν : FreeEnv Model.standard.{u} ρ :=
    fun _ A => Classical.choice (A.denote Model.standard.toTypeModel ρ).property
  exact Holds.not_falsity (valid ρ ν)

end Silmaril.Logic.HOLLight
