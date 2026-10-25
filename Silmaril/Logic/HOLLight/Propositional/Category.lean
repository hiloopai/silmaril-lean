module

public import Silmaril.Logic.HOLLight.Propositional
public import Silmaril.Logic.Metatheory.InferenceSystemCat

@[expose] public section

/-!
# The propositional-to-HOL arrow

The canonical classical translation is a Mathlib categorical arrow. The
source retains CSLib's proof trees; the target retains the independently
defined HOL kernel judgment. Packaging lifts their proof universes without
changing the conclusions or their derivability.
-/

namespace Silmaril.Logic.HOLLight.Propositional

open Cslib.Logic CategoryTheory Silmaril.Logic.Metatheory

/-- CSLib classical propositional logic over checked HOL atoms, with a fixed
finite source context. -/
def classicalSource (sig : Signature) (Γ : PL.Ctx (Formula sig)) : InferenceSystemCat.{0, 1} :=
  InferenceSystemCat.of.{0, 0, 1, 0}
    (ContextSystem (PL.Theory.CPL (Formula sig)) Γ) (PL.Proposition (Formula sig))

/-- HOL's classical kernel with precisely the translated source assumptions. -/
def classicalTarget (sig : Signature) (Γ : PL.Ctx (Formula sig)) : InferenceSystemCat.{0, 1} :=
  InferenceSystemCat.of.{0, 0, 0, 1}
    (HOLLight.ContextSystem sig classicalTheory (translateCtx id Γ)) (Formula sig)

/-- The checked propositional interpretation, packaged as a categorical arrow. -/
def classicalContextArrow (sig : Signature) (Γ : PL.Ctx (Formula sig)) :
    classicalSource sig Γ ⟶ classicalTarget sig Γ :=
  InferenceSystemCat.ofMorphism (classicalContextMorphism sig Γ)

@[simp] theorem classicalContextArrow_map (sig : Signature) (Γ : PL.Ctx (Formula sig))
    (p : PL.Proposition (Formula sig)) :
    (classicalContextArrow sig Γ).map p = interpret id p := rfl

/-- Categorical packaging preserves the original proof-preservation theorem. -/
theorem classicalContextArrow_derivable (sig : Signature) (Γ : PL.Ctx (Formula sig))
    (p : PL.Proposition (Formula sig))
    (proof : Nonempty ((classicalSource sig Γ).Derivation p)) :
    Nonempty ((classicalTarget sig Γ).Derivation (interpret id p)) := by
  obtain ⟨proof⟩ := proof
  exact ⟨(classicalContextArrow sig Γ).mapDerivation proof⟩

/-- Removing the target packaging recovers an actual HOL kernel derivation. -/
theorem classicalContextArrow_derives (sig : Signature) (Γ : PL.Ctx (Formula sig))
    (p : PL.Proposition (Formula sig))
    (proof : Nonempty ((classicalSource sig Γ).Derivation p)) :
    Derives sig classicalTheory (translateCtx id Γ) (translate id p) := by
  obtain ⟨translated⟩ := classicalContextArrow_derivable sig Γ p proof
  exact translated.down.down

end Silmaril.Logic.HOLLight.Propositional
