module

public import Silmaril.Logic.SetTheory.Defs
public import Silmaril.Logic.SetTheory.Inductive.ZFCInference

@[expose] public section

/-! Soundness and the exact common-language Metamath bridge. Consistency here
is relative to the ambient Lean development and its `ZFSet` model. The
Metamath equivalence covers the named common primitive/schema fragment; its
native predicate/equality calculus is a separate translation obligation. -/

namespace Silmaril.Logic.SetTheory.Theorems

/-- The independent ZF calculus is sound in every nonempty model of its schemas. -/
theorem zf_sound {M : Type*} [Membership M M] [Nonempty M]
    (model : ∀ n, ZF M (Fin n)) {n : Nat} {Γ : List (Inductive.Formula n)}
    {p : Inductive.Formula n} (d : Inductive.ZF.Derivation Γ p)
    (E : Fin n → M) (hΓ : ∀ q ∈ Γ, q.eval E) : p.eval E :=
  Inductive.ZF.sound model d E hΓ

/-- Every scoped ZFC derivation is valid in Lean's standard set universe. -/
theorem zfc_zfset_sound {n : Nat} {Γ : List (Inductive.Formula n)}
    {p : Inductive.Formula n} (d : Inductive.ZFC.Derivation Γ p)
    (E : Fin n → _root_.ZFSet) (hΓ : ∀ q ∈ Γ, q.eval E) : p.eval E :=
  Inductive.ZFC.zfSet_sound d E hΓ

/-- Lean's `ZFSet` model rules out a closed ZF derivation of falsehood. -/
theorem zf_consistent :
    ¬ Nonempty (Inductive.ZF.Derivation [] (.bot : Inductive.Sentence)) := by
  rintro ⟨d⟩
  exact Inductive.ZF.zfSet_sound d (Fin.elim0 : Fin 0 → _root_.ZFSet.{0}) (by simp)

/-- The model also validates choice, giving the same result for scoped ZFC. -/
theorem zfc_consistent :
    ¬ Nonempty (Inductive.ZFC.Derivation [] (.bot : Inductive.Sentence)) := by
  rintro ⟨d⟩
  exact Inductive.ZFC.zfSet_sound d (Fin.elim0 : Fin 0 → _root_.ZFSet.{0}) (by simp)

/-- Independent common-fragment proofs and certified native proofs have equal provability. -/
theorem zfc_common_fragment_iff
    (p : Inductive.Named.Formula Inductive.MetamathZF.Native.V) :
    Inductive.ZFC.zfcCommonInference.toAmbient.Provable p ↔
      Inductive.ZFC.nativeZFCCommonInference.toAmbient.Provable p :=
  Inductive.ZFC.zfcCommonInference_provable_iff p

end Silmaril.Logic.SetTheory.Theorems
