module

public import Silmaril.Logic.Metamath.Theory.Lattice
public import Silmaril.Logic.Metatheory.InferenceSystemCat.FixedSoundness

@[expose] public section

/-!
# Metamath axiom sets as inference systems

`system Γ` packages the CSLib inference system of an axiom set as an object
of `InferenceSystemCat`, and `fixedSystem Γ` as a proof family on the fixed
conclusion type of assertions. Their derivable conclusions are the theorems
of `Γ`.

The derivability preorder on axiom sets is the order of
`Fixed.DerivabilityOrder`: `Γ ≤ Δ` exactly when there is an
identity-on-conclusions map of proof families, or equivalently an
`InferenceSystemCat` morphism that is the identity on conclusions. Theories
embed into `DerivabilityOrder` as an order embedding.
-/

namespace Silmaril.Logic.Metamath

open CategoryTheory Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.InferenceSystemCat

universe u

variable {C V : Type u}

/-- The Metamath inference system of `Γ` as an object of `InferenceSystemCat`. -/
def system (Γ : Set (Assertion C V)) : InferenceSystemCat.{u, u + 1} :=
  InferenceSystemCat.of.{0, u, u + 1, 0} (System Γ) (Assertion C V)

@[simp] theorem system_provable_iff {Γ : Set (Assertion C V)} {A : Assertion C V} :
    (system Γ).Provable A ↔ Derivable Γ A :=
  InferenceSystemCat.of_derivable_iff _ _ A

/-- Axioms act on proofs monotonically; as a morphism, inclusion of axiom sets
is the identity on conclusions. -/
def systemMap {Γ Δ : Set (Assertion C V)} (h : Γ ⊆ Δ) : system Γ ⟶ system Δ where
  map A := A
  mapDerivation d := ⟨⟨⟨d.down.down.1, d.down.down.2.mono h⟩⟩⟩

@[simp] theorem systemMap_map {Γ Δ : Set (Assertion C V)} (h : Γ ⊆ Δ) (A : Assertion C V) :
    (systemMap h).map A = A := rfl

/-- The Metamath proofs from `Γ`, on the fixed conclusion type of assertions. -/
def fixedSystem (Γ : Set (Assertion C V)) : Fixed.{u, u} (Assertion C V) where
  Derivation A := Proof Γ A

@[simp] theorem mem_support_fixedSystem {Γ : Set (Assertion C V)} {A : Assertion C V} :
    A ∈ Fixed.support (fixedSystem Γ) ↔ Derivable Γ A := Iff.rfl

theorem support_fixedSystem (Γ : Set (Assertion C V)) :
    Fixed.support (fixedSystem Γ) = {A | Derivable Γ A} := rfl

/-- The derivability class of an axiom set: its set of theorems. -/
def derivabilityClass (Γ : Set (Assertion C V)) : Fixed.DerivabilityOrder.{u, u} (Assertion C V) :=
  Fixed.DerivabilityOrder.ofSystem (fixedSystem Γ)

@[simp] theorem toSet_derivabilityClass (Γ : Set (Assertion C V)) :
    (derivabilityClass Γ).toSet = {A | Derivable Γ A} := rfl

theorem derivabilityClass_le_iff {Γ Δ : Set (Assertion C V)} :
    derivabilityClass Γ ≤ derivabilityClass Δ ↔ ∀ A, Derivable Γ A → Derivable Δ A := Iff.rfl

theorem derivabilityClass_mono : Monotone (derivabilityClass (C := C) (V := V)) :=
  fun _ _ h _ hA => Derivable.mono h hA

/-- Adding theorems as axioms does not change the derivability class. -/
theorem derivabilityClass_union_of_derivable [Infinite V] {Γ Δ : Set (Assertion C V)}
    (h : ∀ B ∈ Δ, Derivable Γ B) : derivabilityClass (Γ ∪ Δ) = derivabilityClass Γ :=
  le_antisymm (fun _ hA => Derivable.cut h hA) (derivabilityClass_mono Set.subset_union_left)

namespace AxiomSet

open WFAssertion

variable [Infinite V]

/-- The derivability preorder on axiom sets is the order on derivability classes. -/
theorem le_iff_derivabilityClass {Γ Δ : AxiomSet C V} :
    Γ ≤ Δ ↔ derivabilityClass (toSet Γ.axioms) ≤ derivabilityClass (toSet Δ.axioms) :=
  le_iff_derivable

/-- `Γ ≤ Δ` exactly when there is a map of proof families at fixed conclusions. -/
theorem le_iff_nonempty_hom {Γ Δ : AxiomSet C V} :
    Γ ≤ Δ ↔ Nonempty (fixedSystem (toSet Γ.axioms) ⟶ fixedSystem (toSet Δ.axioms)) :=
  le_iff_derivable.trans
    (Fixed.nonempty_hom_iff (S := fixedSystem (toSet Γ.axioms))
      (T := fixedSystem (toSet Δ.axioms))).symm

/-- `Γ ≤ Δ` exactly when the packaged systems have a morphism that is the
identity on conclusions. -/
theorem le_iff_exists_hom {Γ Δ : AxiomSet C V} :
    Γ ≤ Δ ↔ ∃ f : system (toSet Γ.axioms) ⟶ system (toSet Δ.axioms), f.map = fun A => A := by
  refine le_iff_derivable.trans (Iff.trans ?_ (sound_iff_morphism _))
  exact forall_congr' fun A => imp_congr system_provable_iff.symm system_provable_iff.symm

/-- The derivability class of an axiom set, as a monotone map. -/
def toDerivabilityOrder : AxiomSet C V →o Fixed.DerivabilityOrder.{u, u} (Assertion C V) where
  toFun Γ := derivabilityClass (toSet Γ.axioms)
  monotone' _ _ h := le_iff_derivabilityClass.1 h

/-- Equivalent axiom sets have the same derivability class; the quotient
embeds into the derivability lattice. -/
def antisymmetrizationEmbedding :
    Antisymmetrization (AxiomSet C V) (· ≤ ·) ↪o Fixed.DerivabilityOrder.{u, u} (Assertion C V) :=
  OrderEmbedding.ofMapLEIff
    (Quotient.lift (fun Γ : AxiomSet C V => derivabilityClass (toSet Γ.axioms)) fun _ _ h =>
      le_antisymm (le_iff_derivabilityClass.1 h.1) (le_iff_derivabilityClass.1 h.2)) fun a b => by
    induction a using Quotient.inductionOn with
    | h Γ =>
      induction b using Quotient.inductionOn with
      | h Δ => exact le_iff_derivabilityClass.symm

end AxiomSet

namespace Theory

open WFAssertion

variable [Infinite V]

/-- The theorems of a theory's axioms are those of any axiom set generating it. -/
theorem derivabilityClass_of (Γ : Set (WFAssertion C V)) :
    derivabilityClass (toSet (of Γ).val) = derivabilityClass (toSet Γ) :=
  le_antisymm (fun _ hA => derivable_of_derivable_theorems hA)
    (derivabilityClass_mono (toSet_mono (subset_theorems Γ)))

/-- Theories embed into the derivability lattice of Metamath assertions. -/
def toDerivabilityOrder : Theory C V ↪o Fixed.DerivabilityOrder.{u, u} (Assertion C V) :=
  OrderEmbedding.ofMapLEIff (fun T => derivabilityClass (toSet T.val)) fun T T' => by
    constructor
    · intro h A hA
      exact (T'.mem_iff_derivable).2 (derivabilityClass_le_iff.1 h _ (T.mem_iff_derivable.1 hA))
    · intro h
      exact derivabilityClass_mono (toSet_mono h)

@[simp] theorem toDerivabilityOrder_apply (T : Theory C V) :
    toDerivabilityOrder T = derivabilityClass (toSet T.val) := rfl

theorem toDerivabilityOrder_of (Γ : Set (WFAssertion C V)) :
    toDerivabilityOrder (of Γ) = derivabilityClass (toSet Γ) :=
  derivabilityClass_of Γ

/-- The well-formed members of a theory's derivability class are the theory. -/
theorem wellFormed_mem_toDerivabilityOrder (T : Theory C V) (A : WFAssertion C V) :
    A.val ∈ (toDerivabilityOrder T).toSet ↔ A ∈ T.val :=
  T.mem_iff_derivable.symm

/-- The embedding of theories factors the embedding of axiom sets modulo
equivalence through `antisymmetrizationIso`. -/
theorem toDerivabilityOrder_antisymmetrizationIso
    (q : Antisymmetrization (AxiomSet C V) (· ≤ ·)) :
    toDerivabilityOrder (AxiomSet.antisymmetrizationIso q) =
      AxiomSet.antisymmetrizationEmbedding q := by
  induction q using Quotient.inductionOn with
  | h Γ =>
    change derivabilityClass (toSet (of Γ.axioms).val) = derivabilityClass (toSet Γ.axioms)
    exact derivabilityClass_of Γ.axioms

end Theory

end Silmaril.Logic.Metamath
