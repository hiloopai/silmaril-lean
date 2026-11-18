module

public import Silmaril.Logic.Consequence.FirstOrder.Derivation.Defs
public import Silmaril.Logic.Consequence.FirstOrder.Syntax.Thms

/-!
# Proofs for first-order natural deduction: every rule instance is valid in every structure
-/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.FirstOrder.Derivation

open Silmaril.Logic.Institution.Examples.UFOL Silmaril.Consequence.FirstOrder.ND

variable {Sg : Signature} [∀ n, DecidableEq (Sg.Op n)] [∀ n, DecidableEq (Sg.Rel n)]

omit [∀ n, DecidableEq (Sg.Op n)] [∀ n, DecidableEq (Sg.Rel n)] in
theorem holds_cons {M : Structure Sg} {k : ℕ} {η : Fin k → M.carrier} {φ : Formula Sg k}
    {Γ : List (Formula Sg k)} (hφ : φ.Holds M η) (hΓ : ∀ ψ ∈ Γ, ψ.Holds M η) :
    ∀ ψ ∈ φ :: Γ, ψ.Holds M η := by
  intro ψ hψ
  rcases List.mem_cons.1 hψ with rfl | hψ
  · exact hφ
  · exact hΓ _ hψ

theorem rule_valid (M : Structure Sg) {k : ℕ} (r : Rule Sg k) (hs : r.side = true)
    (hp : ∀ p ∈ r.prems, p.ValidIn M) : r.concl.ValidIn M := by
  cases r <;> simp only [Rule.prems, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq] at hp <;> simp only [Rule.side, decide_eq_true_eq] at hs <;>
    intro η hΓ
  case hyp => exact hΓ _ hs
  case weaken => exact hp η (fun ψ h => hΓ ψ (hs ψ h))
  case ttIntro => trivial
  case notIntro => exact fun hφ => hp.2 η (holds_cons hφ hΓ) (hp.1 η (holds_cons hφ hΓ))
  case notElim => exact (hp.2 η hΓ (hp.1 η hΓ)).elim
  case dne => exact Classical.byContradiction (hp η hΓ)
  case andIntro => exact ⟨hp.1 η hΓ, hp.2 η hΓ⟩
  case andLeft => exact (hp η hΓ).1
  case andRight => exact (hp η hΓ).2
  case allIntro =>
    intro x
    apply hp (Fin.cons x η)
    intro ψ hψ
    obtain ⟨ψ, h, rfl⟩ := List.mem_map.1 hψ
    exact (Formula.holds_shift M ψ η x).2 (hΓ ψ h)
  case allElim t => exact (Formula.holds_inst M _ t η).2 (hp η hΓ (t.eval M η))
  case eqRefl => rfl
  case eqElim φ s t =>
    have h := (Formula.holds_inst M φ s η).1 (hp.2 η hΓ)
    have heq : s.eval M η = t.eval M η := hp.1 η hΓ
    exact (Formula.holds_inst M φ t η).2 (heq ▸ h)

/-! ## Translation along signature morphisms -/

section Map

variable {Sg' : Signature} [∀ n, DecidableEq (Sg'.Op n)] [∀ n, DecidableEq (Sg'.Rel n)]
  (σ : Sg ⟶ Sg')

omit [∀ n, DecidableEq (Sg.Op n)] [∀ n, DecidableEq (Sg.Rel n)]
  [∀ n, DecidableEq (Sg'.Op n)] [∀ n, DecidableEq (Sg'.Rel n)] in
theorem rule_map_prems {k : ℕ} (r : Rule Sg k) : (r.map σ).prems = r.prems.map (Seq.map σ) := by
  cases r <;> simp [Rule.map, Rule.prems, Seq.map, Formula.map, Formula.map_shift,
    Formula.map_inst, List.map_map, Function.comp_def]

omit [∀ n, DecidableEq (Sg.Op n)] [∀ n, DecidableEq (Sg.Rel n)]
  [∀ n, DecidableEq (Sg'.Op n)] [∀ n, DecidableEq (Sg'.Rel n)] in
theorem rule_map_concl {k : ℕ} (r : Rule Sg k) : (r.map σ).concl = r.concl.map σ := by
  cases r <;> simp [Rule.map, Rule.concl, Seq.map, Formula.map, Formula.map_inst]

theorem rule_map_side {k : ℕ} (r : Rule Sg k) (h : r.side = true) : (r.map σ).side = true := by
  cases r <;> simp only [Rule.side, Rule.map, decide_eq_true_eq] at h ⊢
  case hyp => exact List.mem_map_of_mem h
  case weaken =>
    intro ψ hψ
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hψ
    exact List.mem_map_of_mem (h φ hφ)

end Map

end Silmaril.Proofs.Logic.Consequence.FirstOrder.Derivation
