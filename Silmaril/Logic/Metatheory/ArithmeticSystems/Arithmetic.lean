module

public import Silmaril.Logic.Arithmetic.Peano
public import Silmaril.Logic.Metatheory.ArithmeticSystems.Forgetful

@[expose] public section

/-!
# Robinson Q and Peano arithmetic in the structured category

The base is the independent scoped Q calculus, with its actual derivation
trees. PA's interpretation uses the proved Q-to-PA translation: in particular
Q's predecessor axiom is derived from PA induction. Standard-model soundness
and induction remain separate properties of objects containing Q.
-/

namespace Silmaril.Logic.Metatheory.ArithmeticSystems

open CategoryTheory Silmaril.Logic.Arithmetic

/-- Closed arithmetic formulas with their independent Robinson-Q proof trees. -/
def qInference : InferenceSystemCat where
  Conclusion := Sentence
  Derivation φ := QProof [] φ

/-- The independent PA calculus on the same scoped arithmetic syntax. -/
def paInference : InferenceSystemCat where
  Conclusion := Sentence
  Derivation φ := PAProof [] φ

/-- The real Q-to-PA map replaces Q's predecessor axiom by a PA induction proof. -/
def qToPAInference : qInference ⟶ paInference where
  map := id
  mapDerivation := qToPA

/-- Q as an object with its identity arithmetic interpretation. -/
def robinson : System qInference := System.baseSystem qInference

/-- PA contains Q through the proved arithmetic proof translation. -/
def peano : System qInference where
  inference := paInference
  base := qToPAInference
  faithfulSyntax := Function.injective_id

/-- The canonical arithmetic-preserving Q-to-PA arrow. -/
def robinsonToPeano : robinson ⟶ peano := System.fromBase peano

@[simp] theorem forget_robinsonToPeano :
    System.forget.map robinsonToPeano = qToPAInference := rfl

@[simp] theorem robinsonToPeano_map (φ : Sentence) :
    robinsonToPeano.inference.map φ = φ := rfl

@[simp] theorem robinsonToPeano_proof (φ : Sentence) (d : QProof [] φ) :
    robinsonToPeano.inference.mapDerivation d = qToPA d := rfl

/-- This closed addition equality has an actual Q derivation tree. -/
def zeroAddZero : Sentence := .equal (.add .zero .zero) .zero

theorem robinson_zeroAddZero : robinson.inference.Provable (robinson.base.map zeroAddZero) :=
  ⟨qZeroAddZero⟩

/-- Transport the concrete arithmetic theorem using the structured category. -/
theorem peano_zeroAddZero : peano.inference.Provable (peano.base.map zeroAddZero) :=
  System.transport robinsonToPeano robinson_zeroAddZero

/-- The canonical inference functor carries precisely the same proof tree map. -/
theorem inference_zeroAddZero :
    (System.forget.map robinsonToPeano).mapDerivation qZeroAddZero = paZeroAddZero := rfl

/-- The common-arithmetic-fragment functor transports the same concrete proof. -/
theorem fragment_zeroAddZero :
    System.fragment.map robinsonToPeano zeroAddZero qZeroAddZero = paZeroAddZero := rfl

theorem q_arithmetic_extension_pa : System.ArithmeticExtension robinson peano :=
  System.arithmeticExtension_of_hom robinsonToPeano

theorem q_interpretable_pa : System.Interpretable robinson peano := ⟨robinsonToPeano⟩

/-- Truth of a scoped closed sentence in the standard natural-number model. -/
def TrueInNat (φ : Sentence) : Prop := φ.eval Fin.elim0

/-- Standard arithmetic soundness is independent of carrying the Q interpretation. -/
def StandardSound (S : System qInference) : Prop :=
  ∀ φ, S.inference.Provable (S.base.map φ) → TrueInNat φ

theorem robinson_standardSound : StandardSound robinson := by
  rintro φ ⟨d⟩
  exact qSound d Fin.elim0 (by simp [Satisfies])

theorem peano_standardSound : StandardSound peano := by
  rintro φ ⟨d⟩
  exact paSound d Fin.elim0 (by simp [Satisfies])

theorem StandardSound.pullback {S T : System qInference} (f : S ⟶ T)
    (h : StandardSound T) : StandardSound S := fun φ hφ => h φ (System.transport f hφ)

/-- Compatibility with an independently classified sentence hierarchy.
No Σ₁ classification is assumed or invented by the category. -/
def standardLanguage (isSigma1 : Sentence → Prop) : ArithLanguage where
  Sentence := Sentence
  IsSigma1 := isSigma1
  TrueInNat := TrueInNat

theorem standardSound_iff_arithmeticSound (isSigma1 : Sentence → Prop)
    (S : System qInference) :
    StandardSound S ↔ System.ArithmeticSound (standardLanguage isSigma1) id S := Iff.rfl

/-- Derivability of the actual arithmetic induction schema, with arbitrary body. -/
def ProvesInduction (S : System qInference) : Prop :=
  ∀ φ : Formula 1, S.inference.Provable (S.base.map (inductionSchema φ))

theorem peano_provesInduction : ProvesInduction peano := fun φ => ⟨.ax (.induction φ)⟩

theorem ProvesInduction.transport {S T : System qInference} (f : S ⟶ T)
    (h : ProvesInduction S) : ProvesInduction T := fun φ => System.transport f (h φ)

theorem q_forget_not_full : ¬ (System.forget (B := qInference)).Full :=
  System.forget_not_full qInference qZeroAddZero

end Silmaril.Logic.Metatheory.ArithmeticSystems
