module

public import Silmaril.Logic.Metamath.SecondOrder.Soundness
public import Silmaril.Logic.Metamath.Model.Consistency

@[expose] public section

/-!
# Consistency of second-order arithmetic and its subsystems

The full model `𝒫(ℕ)` satisfies every axiom of `z2.mm` and is not trivial:
the formula `0 = S 0` is not valid in it. By soundness of Carneiro models
(`Model.sound`), `Z2`, `ACA0`, `WKL0` and `RCA0` are consistent: they do not
prove the falsum `|- ph` (`not_tderivable_falsum_Z2`), and in fact no
subset of the axioms of `z2.mm` proves `|- 0 = S 0`
(`not_tderivable_zeroEqOne`). The same holds for the string systems of the
syntax axioms and the flattened axioms (`nonUniversal_Z2`,
`not_derivable_zeroEqOne`), whose theories lie strictly below the top of the
lattice of theories (`theory_ne_top_Z2`), and in the lattice of tree theories
(`ttheory_ne_top_Z2`).

More generally a system is consistent as soon as it has an ω-model with a
nonempty second-order part (`tConsistent_of_isModel`).
-/

namespace Silmaril.Logic.Metamath.SecondOrder

open Grammar Sem Function

section Nontrivial

variable {𝒮 : Set (Set ℕ)} {N : Type} [DecidableEq N] [Infinite N]

/-- An environment giving every number name the value `0` and every set name
the value `A`. -/
def constEnv (A : ↥𝒮) : Env 𝒮 N
  | .inl _ => (0 : ℕ)
  | .inr _ => A

/-- An ω-model with a nonempty second-order part is not trivial: `0 = S 0` is
not valid. -/
theorem not_trivialAt (h𝒮 : 𝒮.Nonempty) :
    ¬ (model 𝒮 N).TrivialAt (c := .turnstile) (s := .wff) rfl := fun h => by
  obtain ⟨A, hA⟩ := h𝒮
  have : (0 : ℕ) = 0 + 1 :=
    h ⟨eq zero (succ zero), .eq .zero (.succ .zero)⟩ (constEnv ⟨A, hA⟩)
  omega

/-- A system with an ω-model whose second-order part is nonempty is
consistent. -/
theorem tConsistent_of_isModel {Γ : Set (TAssertion L C V)} (hΓ : ∀ B ∈ Γ, B.WellFormed grammar)
    (h𝒮 : 𝒮.Nonempty) (hM : (model 𝒮 N).IsModel Γ) : TConsistent grammar Γ .turnstile :=
  Model.tConsistent hΓ hM rfl (not_trivialAt h𝒮) .ph

end Nontrivial

theorem not_trivialAt_full :
    ¬ (fullModel ℕ).TrivialAt (c := .turnstile) (s := .wff) rfl :=
  not_trivialAt ⟨∅, trivial⟩

theorem isModel_full_Z2 : (fullModel ℕ).IsModel Z2 := isModel_full.mono Z2_subset_allAxioms

theorem isModel_full_ACA0 : (fullModel ℕ).IsModel ACA0 := isModel_full.mono ACA0_subset_allAxioms

theorem isModel_full_WKL0 : (fullModel ℕ).IsModel WKL0 := isModel_full.mono WKL0_subset_allAxioms

theorem isModel_full_RCA0 : (fullModel ℕ).IsModel RCA0 := isModel_full.mono RCA0_subset_allAxioms

/-! ## Consistency -/

/-- All axioms of `z2.mm` together are consistent. -/
theorem tConsistent_allAxioms : TConsistent grammar allAxioms .turnstile :=
  tConsistent_of_isModel (𝒮 := Set.univ) (N := ℕ) wellFormed_all ⟨∅, trivial⟩ isModel_full

/-- Second-order arithmetic is consistent. -/
theorem tConsistent_Z2 : TConsistent grammar Z2 .turnstile :=
  tConsistent_allAxioms.mono Z2_subset_allAxioms

theorem tConsistent_ACA0 : TConsistent grammar ACA0 .turnstile :=
  tConsistent_allAxioms.mono ACA0_subset_allAxioms

theorem tConsistent_WKL0 : TConsistent grammar WKL0 .turnstile :=
  tConsistent_allAxioms.mono WKL0_subset_allAxioms

theorem tConsistent_RCA0 : TConsistent grammar RCA0 .turnstile :=
  tConsistent_allAxioms.mono RCA0_subset_allAxioms

/-- `Z2` does not prove the falsum `|- ph`. -/
theorem not_tderivable_falsum_Z2 :
    ¬ TDerivable grammar Z2 (TAssertion.falsum .turnstile .wff .ph) :=
  Model.not_tderivable_falsum wellFormed_Z2 isModel_full_Z2 rfl not_trivialAt_full .ph

/-- The string system of `Z2` (syntax axioms and flattened axioms) is
consistent. -/
theorem nonUniversal_Z2 : (system (grammar.axioms Z2)).NonUniversal :=
  Model.nonUniversal_system unambiguous wellFormed_Z2 isModel_full_Z2 rfl not_trivialAt_full .ph

/-- The theory of the string axioms of `Z2` lies strictly below the top of
the lattice of theories. -/
theorem theory_ne_top_Z2 : Theory.of (grammar.wfAxioms Z2) ≠ ⊤ :=
  Model.theory_ne_top unambiguous wellFormed_Z2 isModel_full_Z2 rfl not_trivialAt_full .ph

/-- The tree theory of a system consistent at `|-` is not the top tree
theory. -/
theorem ttheory_ne_top {Γ : Set (TAssertion L C V)} (hΓ : ∀ B ∈ Γ, B.WellFormed grammar)
    (h : TConsistent grammar Γ .turnstile) : theory Γ ≠ ⊤ := by
  intro htop
  obtain ⟨A, hA, -, hn⟩ := h
  have hmem : (⟨A, hA⟩ : TWFAssertion grammar) ∈ (theory Γ).val := by
    rw [htop, TTheory.val_top]
    trivial
  rw [TTheory.mem_of, toSet_wf hΓ] at hmem
  exact hn hmem

theorem ttheory_ne_top_Z2 : theory Z2 ≠ ⊤ := ttheory_ne_top wellFormed_Z2 tConsistent_Z2

theorem ttheory_ne_top_RCA0 : theory RCA0 ≠ ⊤ := ttheory_ne_top wellFormed_RCA0 tConsistent_RCA0

/-! ## A concrete unprovable sentence -/

/-- The sentence `|- 0 = S 0`. -/
def zeroEqOne : TAssertion L C V :=
  ⟨[], [], ⟨.turnstile, .node .weq [.node .t0 [], .node .tS [.node .t0 []]]⟩⟩

theorem wellFormed_zeroEqOne : zeroEqOne.WellFormed grammar := .of_checkWF (by decide)

theorem not_satisfies_zeroEqOne : ¬ (fullModel ℕ).Satisfies zeroEqOne := by
  intro h
  obtain ⟨_, hv⟩ := valid_of_holds
    (h (fun _ _ h => absurd h.1 (by simp [TAssertion.ctx, zeroEqOne]))
      (by simp [Model.DVHolds, zeroEqOne]) (by simp [TAssertion.essentials, zeroEqOne]))
  z2_values at hv
  have : (0 : ℕ) = 0 + 1 := hv (constEnv ⟨∅, trivial⟩)
  omega

/-- No subset of the axioms of `z2.mm` proves `|- 0 = S 0`. -/
theorem not_tderivable_zeroEqOne {Γ : Set (TAssertion L C V)} (hΓ : Γ ⊆ allAxioms) :
    ¬ TDerivable grammar Γ zeroEqOne :=
  (fullModel ℕ).not_tderivable (fun B hB => wellFormed_all B (hΓ hB)) (isModel_full.mono hΓ)
    not_satisfies_zeroEqOne

/-- The string form: the syntax axioms and the flattened axioms of `Z2` do not
derive `|- 0 = S 0`. -/
theorem not_derivable_zeroEqOne :
    ¬ Derivable (grammar.axioms Z2) (zeroEqOne.flatten grammar) :=
  (fullModel ℕ).not_derivable unambiguous wellFormed_Z2 isModel_full_Z2 wellFormed_zeroEqOne
    not_satisfies_zeroEqOne

end Silmaril.Logic.Metamath.SecondOrder
