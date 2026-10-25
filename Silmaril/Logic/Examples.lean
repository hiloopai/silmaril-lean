module

public import Silmaril.Logic
public import Silmaril.Logic.Arithmetic.Examples
public import Silmaril.Logic.Arithmetic.Completeness.Examples
public import Silmaril.Logic.ArithmeticToSecondOrder.Examples
public import Silmaril.Logic.Metamath.Verify.Kernel

@[expose] public section

/-! Small entry-point checks for the logic development.
Each statement uses an inhabited proof system or a concrete model.
See `docs/projects/logic.md` for the larger examples and exact contracts. -/

namespace Silmaril.Logic.Examples

open CategoryTheory

/-- The classical HOL object theory has a standard model. -/
theorem hol_model_exists :
    ∃ M : HOLLight.Model.{0} HOLLight.initialSignature, HOLLight.Models M HOLLight.classicalTheory :=
  ⟨HOLLight.Model.standard, HOLLight.standard_models_classical⟩

/-- The same model rules out a HOL proof of falsity. -/
theorem hol_consistent :
    ¬ HOLLight.Derives HOLLight.initialSignature HOLLight.classicalTheory ∅ HOLLight.Tm.falsity :=
  HOLLight.classical_consistent

/-- PA consistency is an external theorem in Lean's standard arithmetic model. -/
theorem pa_consistent :
    ¬ Nonempty (Arithmetic.PAProof [] (.bot : Arithmetic.Sentence)) :=
  Arithmetic.Theorems.pa_consistent

/-- The independent scoped ZFC calculus is consistent in Lean's set model. -/
theorem zfc_consistent :
    ¬ Nonempty (SetTheory.Inductive.ZFC.Derivation [] (.bot : SetTheory.Inductive.Sentence)) :=
  SetTheory.Theorems.zfc_consistent

/-- Kernel computation of a Metamath machine run yields an actual derivation. -/
theorem metamath_demo :
    Metamath.Derivable Metamath.Verify.Kernel.axioms Metamath.Verify.Kernel.th1 :=
  Metamath.Verify.Kernel.th1_derivable

/-- Structured specifications and their graph nodes have exactly the same models. -/
theorem specification_models {Sign : Type} [Category Sign]
    (I : Sign ⥤ Institution.Room) {S : Sign} (SP : Institution.StrSpec I S) :
    (Institution.StrSpec.devGraph I).models ⟨S, SP⟩ = SP.models :=
  Institution.StrSpec.models_devGraph SP

end Silmaril.Logic.Examples
