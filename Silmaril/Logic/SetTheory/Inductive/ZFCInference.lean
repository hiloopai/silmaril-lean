module

public import Silmaril.Logic.SetTheory.Inductive.ZFC
public import Silmaril.Logic.SetTheory.Inductive.MetamathZFC
public import Silmaril.Logic.Metamath.Peano.ZFCSound
public import Silmaril.Logic.Metatheory.InferenceSystemCat.Fixed

@[expose] public section

/-!
# Proof-relevant inference objects and arithmetic views of choice extensions

The simple system uses the same scoped sentence language as its base. The
native system retains Metamath assertions, floating hypotheses and dummy
variables. An arithmetic view pulls a derivation family back along a stated
sentence interpretation; its truth theorem requires semantic correctness of
that interpretation. Constructing interpretations and proving arithmetic
conservativity of ZF in ZFC are separate obligations.
-/

namespace Silmaril.Logic.SetTheory.Inductive.ZFC

open Silmaril.Logic.Metatheory
open Silmaril.Logic.Metatheory.InferenceSystemCat
open Silmaril.Logic.Metamath Grammar
open CategoryTheory

/-- The independent base as a proof-relevant object on scoped sentences. -/
def baseInference (Base : Classical.AxiomFamily) : Fixed Sentence where
  Derivation p := Classical.Derivation Base [] p

/-- Its choice extension uses exactly the same sentence carrier. -/
def inference (Base : Classical.AxiomFamily) : Fixed Sentence where
  Derivation p := Classical.Derivation (extend Base) [] p

/-- The concrete shared independent ZFC theory on its scoped sentence language. -/
def simpleZFCInference : Fixed Sentence := inference ZF.axiomFamily

/-- The inclusion fixes sentences and transports the original derivation tree. -/
noncomputable def baseInclusion (Base : Classical.AxiomFamily) :
    (baseInference Base).toAmbient ⟶ (inference Base).toAmbient where
  map := id
  mapDerivation := fromBase

@[simp] theorem baseInclusion_sentence (Base : Classical.AxiomFamily) (p : Sentence) :
    (baseInclusion Base).map p = p := rfl

/-- The full native ZFC inference object, retaining genuine Metamath proof objects. -/
def nativeInference : Fixed (TAssertion Peano.ZF.L Peano.ZF.C Peano.ZF.V) where
  Derivation p := TProof Peano.ZF.grammar Peano.ZF.ZFC p

/-- A simple arithmetic view along an explicit interpretation into scoped sentences. -/
def arithmeticView (Base : Classical.AxiomFamily) (A : ArithLanguage)
    (tr : A.Sentence → Sentence) : Fixed A.Sentence where
  Derivation p := (inference Base).Derivation (tr p)

/-- The concrete simple ZFC arithmetic view requires its sentence interpretation explicitly. -/
def simpleZFCArithmeticView (A : ArithLanguage) (tr : A.Sentence → Sentence) :
    Fixed A.Sentence := arithmeticView ZF.axiomFamily A tr

/-- Soundness transfers only when the designated sentence meanings are established. -/
theorem arithmeticView_sound (Base : Classical.AxiomFamily) (A : ArithLanguage)
    (tr : A.Sentence → Sentence) {M : Type*} [Membership M M]
    (hBase : ∀ n p, Base n p → ∀ E : Fin n → M, p.eval E)
    (hChoice : ∀ x : M, Choice.AxAC x)
    (agree : ∀ p, (tr p).holds (M := M) → A.TrueInNat p) :
    A.ArithSound (arithmeticView Base A tr).toAmbient.Provable id := by
  intro p hp
  obtain ⟨d⟩ := hp
  exact agree p (sound hBase hChoice d Fin.elim0 (by simp))

/-- The native arithmetic view uses the already verified von Neumann interpretation. -/
def nativeArithmeticView : Fixed Peano.arithLanguage.Sentence where
  Derivation p := TProof Peano.ZF.grammar Peano.ZF.ZFC (Peano.ToZF.trSentence p.1)

/-- The native arithmetic view preserves the designated standard-model truth. -/
theorem nativeArithmeticView_sound :
    Peano.arithLanguage.ArithSound nativeArithmeticView.toAmbient.Provable id := by
  intro p hp
  exact Peano.ToZF.arithSound_ZFC p hp

open MetamathZF MetamathZFC

/-- The independently defined common choice/propositional language fragment. -/
def fragmentInference : Fixed (Named.Formula Native.V) where
  Derivation p := ChoiceHilbert [] p

/-- An actual native proof in a finite well-formed frame, with no essential premises. -/
structure NativeFragmentProof (p : Named.Formula Native.V)
    (Δ : Set (TAssertion Native.L Native.C Native.V) := choiceFragmentAxioms) where
  frame : TAssertion Native.L Native.C Native.V
  wellFormed : frame.WellFormed Native.grammar
  pure : ∀ i s, frame.ctx i s → s = .setvar
  conclusion : frame.concl = Peano.ZF.T.pf (encode p)
  noPremises : frame.essentials = []
  derivation : TDerivation Native.grammar Δ frame (Peano.ZF.T.pf (encode p))

/-- The native common-language view is indexed by the certified independent encoding. -/
def nativeFragmentInference : Fixed (Named.Formula Native.V) where
  Derivation p := NativeFragmentProof p

/-- Compile a common-fragment proof into a real finite native certificate. -/
noncomputable def fragmentNativeProof {p : Named.Formula Native.V}
    (d : ChoiceHilbert [] p) : NativeFragmentProof p := {
    frame := choiceProofFrame d.vars [] p
    wellFormed := choiceProofFrame_wellFormed d.vars [] p d.conclusion_vars (by simp)
    pure := fun i s hi => ((choiceProofFrame_ctx d.vars [] p i s).mp hi).2
    conclusion := rfl
    noPremises := by simp
    derivation := choiceHilbertToNative _ (choiceProofFrame_complete d.vars [] p)
      (by simp) d (fun i hi => (choiceProofFrame_ctx d.vars [] p i .setvar).mpr ⟨hi, rfl⟩)
  }

/-- The native compiler fixes the certified common-language formula index. -/
noncomputable def fragmentToNative :
    fragmentInference.toAmbient ⟶ nativeFragmentInference.toAmbient where
  map := id
  mapDerivation d := fragmentNativeProof d

/-- Reflect the native proof object using syntactic leaf decoding, without a truth premise. -/
theorem nativeFragmentToIndependent_nonempty {p : Named.Formula Native.V}
    (d : NativeFragmentProof p) : Nonempty (ChoiceHilbert [] p) := by
  obtain ⟨q, he, hd⟩ := nativeChoiceToHilbert (Γ := []) d.pure
    (by intro e he; rw [d.noPremises] at he; simp at he) d.derivation
  have hq : q = p := encode_injective (congrArg TExpr.tree he).symm
  exact hq ▸ hd

/-- Reverse proof translation need not invert individual proof fibers. -/
noncomputable def nativeToFragment :
    nativeFragmentInference.toAmbient ⟶ fragmentInference.toAmbient where
  map := id
  mapDerivation d := _root_.Classical.choice (nativeFragmentToIndependent_nonempty d)

@[simp] theorem fragmentToNative_sentence (p : Named.Formula Native.V) :
    fragmentToNative.map p = p := rfl

@[simp] theorem nativeToFragment_sentence (p : Named.Formula Native.V) :
    nativeToFragment.map p = p := rfl

/-- Bidirectional provability is established for this exact supported native fragment. -/
theorem fragmentInference_provable_iff (p : Named.Formula Native.V) :
    fragmentInference.toAmbient.Provable p ↔ nativeFragmentInference.toAmbient.Provable p := by
  constructor
  · rintro ⟨d⟩
    exact ⟨fragmentToNative.mapDerivation d⟩
  · rintro ⟨d⟩
    exact ⟨nativeToFragment.mapDerivation d⟩

/-- Open-context natural deduction permits a certified interpretation of named formulas. -/
def openInference (n : Nat) : Fixed (Formula n) where
  Derivation p := ZFC.Derivation [] p

/-- The fragment's independent proof translation commutes with named-to-scoped lowering. -/
noncomputable def fragmentToScoped {n : Nat} (ρ : Native.V → Fin n) :
    fragmentInference.toAmbient ⟶ (openInference n).toAmbient where
  map p := p.lower ρ
  mapDerivation d := choiceHilbertToSimple ρ d

@[simp] theorem fragmentToScoped_sentence {n : Nat} (ρ : Native.V → Fin n)
    (p : Named.Formula Native.V) : (fragmentToScoped ρ).map p = p.lower ρ := rfl

/-- The interpretation preserves every designated formula meaning under its assignment. -/
theorem fragmentToScoped_meaning {M : Type*} [Membership M M] {n : Nat}
    (ρ : Native.V → Fin n) (p : Named.Formula Native.V) (E : Fin n → M) :
    ((fragmentToScoped ρ).map p).eval E ↔ p.eval (E ∘ ρ) := p.eval_lower ρ E

/-- A nontrivial independent proof uses ax-ac and actual modus ponens to prefix an implication. -/
def choiceImplicationProof (q : Named.Formula Native.V) :
    ChoiceHilbert [] (.imp q canonicalChoice) :=
  .mp (.k canonicalChoice q) (.ax canonicalChoice_schema)

/-- The same example has an actual finite native certificate via the proved translation. -/
noncomputable def nativeChoiceImplicationProof (q : Named.Formula Native.V) :
    NativeFragmentProof (.imp q canonicalChoice) :=
  fragmentToNative.mapDerivation (choiceImplicationProof q)

/-- All nine ZF schemas plus choice, independently presented in the common named language. -/
def zfcCommonInference : Fixed (Named.Formula Native.V) where
  Derivation p := ZFCHilbert [] p

/-- The corresponding actual native ZFC fragment, retaining each native proof certificate. -/
def nativeZFCCommonInference : Fixed (Named.Formula Native.V) where
  Derivation p := NativeFragmentProof p zfcFragment

/-- Translate a whole common ZFC proof into a well-formed native frame and derivation. -/
noncomputable def zfcNativeProof {p : Named.Formula Native.V}
    (d : ZFCHilbert [] p) : NativeFragmentProof p zfcFragment := {
  frame := choiceProofFrame d.vars [] p
  wellFormed := choiceProofFrame_wellFormed d.vars [] p d.conclusion_vars (by simp)
  pure := fun i s hi => ((choiceProofFrame_ctx d.vars [] p i s).mp hi).2
  conclusion := rfl
  noPremises := by simp
  derivation := zfcHilbertToNative _ (choiceProofFrame_complete d.vars [] p)
    (by simp) d (fun i hi => (choiceProofFrame_ctx d.vars [] p i .setvar).mpr ⟨hi, rfl⟩)
}

noncomputable def zfcCommonToNative :
    zfcCommonInference.toAmbient ⟶ nativeZFCCommonInference.toAmbient where
  map := id
  mapDerivation d := zfcNativeProof d

/-- Native reflection uses both actual ZF and choice schema classifiers. -/
theorem nativeZFCCommon_nonempty {p : Named.Formula Native.V}
    (d : NativeFragmentProof p zfcFragment) : Nonempty (ZFCHilbert [] p) := by
  obtain ⟨q, he, hd⟩ := nativeToZFCHilbert (Γ := []) d.pure
    (by intro e he; rw [d.noPremises] at he; simp at he) d.derivation
  have hq : q = p := encode_injective (congrArg TExpr.tree he).symm
  exact hq ▸ hd

noncomputable def nativeToZFCCommon :
    nativeZFCCommonInference.toAmbient ⟶ zfcCommonInference.toAmbient where
  map := id
  mapDerivation d := _root_.Classical.choice (nativeZFCCommon_nonempty d)

/-- These translations preserve the named conclusion and prove supported-fragment equivalence. -/
theorem zfcCommonInference_provable_iff (p : Named.Formula Native.V) :
    zfcCommonInference.toAmbient.Provable p ↔ nativeZFCCommonInference.toAmbient.Provable p := by
  constructor
  · rintro ⟨d⟩
    exact ⟨zfcCommonToNative.mapDerivation d⟩
  · rintro ⟨d⟩
    exact ⟨nativeToZFCCommon.mapDerivation d⟩

/-- Finite named common-language ZFC has a direct interpretation in full scoped ZFC. -/
def finiteZFCCommonInference (n : Nat) : Fixed (Named.Formula (Fin n)) where
  Derivation p := ZFCHilbert [] p

noncomputable def finiteCommonToScoped (n : Nat) :
    (finiteZFCCommonInference n).toAmbient ⟶ (openInference n).toAmbient where
  map p := p.lower id
  mapDerivation d := zfcHilbertToScoped d

/-- The finite named/scoped bridge preserves its designated membership sentence meaning. -/
theorem finiteCommonToScoped_meaning {M : Type*} [Membership M M] (n : Nat)
    (p : Named.Formula (Fin n)) (E : Fin n → M) :
    ((finiteCommonToScoped n).map p).eval E ↔ p.eval E := by
  simpa [finiteCommonToScoped] using p.eval_lower id E

end Silmaril.Logic.SetTheory.Inductive.ZFC
