module

public import Silmaril.Logic.Consequence.Arithmetic.Derivation.Defs
public import Silmaril.Logic.Consequence.Derivation.Thms
public import Silmaril.Logic.Arithmetic.Peano

/-!
# Proofs for the arithmetic derivation systems

Each rule instance is a `Derivation` step (`rule_derivable`) and is valid in ℕ (`rule_valid`);
every `Derivation` is a valid proof tree (`tree_of_derivation`).
-/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.Arithmetic.Derivation

open Silmaril.Consequence Silmaril.Consequence.Arithmetic.ND Silmaril.Logic.Arithmetic

variable {T : Theory} {n : ℕ}

/-- The basic axioms belong to both theories. -/
def ofBasic (T : Theory) {φ : Formula n} (b : BasicAxiom φ) : T.Ax φ :=
  match T with
  | .q => QAxiom.basic b
  | .pa => PAAxiom.basic b

theorem axiom_derivable (T : Theory) (Γ : Context n) :
    ∀ a : AxiomCode n, a.inTheory T = true → Nonempty (Derivation T.Ax Γ a.formula)
  | .succNonzero t, _ => ⟨.weaken (Γ := []) (by simp) (.ax (ofBasic T (.succNonzero t)))⟩
  | .succInjective s t, _ => ⟨.weaken (Γ := []) (by simp) (.ax (ofBasic T (.succInjective s t)))⟩
  | .addZero t, _ => ⟨.weaken (Γ := []) (by simp) (.ax (ofBasic T (.addZero t)))⟩
  | .addSucc s t, _ => ⟨.weaken (Γ := []) (by simp) (.ax (ofBasic T (.addSucc s t)))⟩
  | .mulZero t, _ => ⟨.weaken (Γ := []) (by simp) (.ax (ofBasic T (.mulZero t)))⟩
  | .mulSucc s t, _ => ⟨.weaken (Γ := []) (by simp) (.ax (ofBasic T (.mulSucc s t)))⟩
  | .pred t, h => match T, h with
    | .q, _ => ⟨.weaken (Γ := []) (by simp) (.ax (show QAxiom _ from .pred t))⟩
  | .induction φ, h => match T, h with
    | .pa, _ => ⟨.weaken (Γ := []) (by simp) (.ax (show PAAxiom _ from .induction φ))⟩

theorem axiom_valid (T : Theory) (a : AxiomCode n) (h : a.inTheory T = true) : Valid a.formula := by
  obtain ⟨d⟩ := axiom_derivable T [] a h
  intro e
  cases T
  · exact qSound d e (by simp [Satisfies])
  · exact paSound d e (by simp [Satisfies])

/-- **Each rule instance is a `Derivation` step.** -/
theorem rule_derivable (r : Rule n) (hs : r.side T = true)
    (hp : ∀ p ∈ r.prems, p.Derivable T) : r.concl.Derivable T := by
  cases r <;> simp only [Rule.prems, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq] at hp <;> simp only [Rule.side, decide_eq_true_eq] at hs
  case hyp => exact ⟨.hyp hs⟩
  case ax Γ a => exact axiom_derivable T Γ a hs
  case weaken => exact ⟨.weaken hs hp.some⟩
  case impIntro => exact ⟨.impIntro hp.some⟩
  case impElim => exact ⟨.impElim hp.1.some hp.2.some⟩
  case botElim => exact ⟨.botElim hp.some⟩
  case classical => exact ⟨.classical hp.some⟩
  case conjIntro => exact ⟨.conjIntro hp.1.some hp.2.some⟩
  case conjLeft => exact ⟨.conjLeft hp.some⟩
  case conjRight => exact ⟨.conjRight hp.some⟩
  case disjLeft => exact ⟨.disjLeft hp.some⟩
  case disjRight => exact ⟨.disjRight hp.some⟩
  case disjElim => exact ⟨.disjElim hp.1.some hp.2.1.some hp.2.2.some⟩
  case allIntro => exact ⟨.allIntro hp.some⟩
  case allElim t => exact ⟨.allElim hp.some t⟩
  case exIntro t => exact ⟨.exIntro t hp.some⟩
  case exElim => exact ⟨.exElim hp.1.some hp.2.some⟩
  case eqRefl t => exact ⟨.eqRefl t⟩
  case eqElim φ s t => exact ⟨.eqElim φ hp.1.some hp.2.some⟩

theorem satisfies_cons {e : Assignment n} {φ : Formula n} {Γ : Context n} (hφ : φ.eval e)
    (hΓ : Satisfies e Γ) : Satisfies e (φ :: Γ) := by
  intro χ hχ
  rcases List.mem_cons.1 hχ with rfl | hχ
  · exact hφ
  · exact hΓ _ hχ

theorem satisfies_shift {e : Assignment n} {Γ : Context n} (x : ℕ) (hΓ : Satisfies e Γ) :
    Satisfies (extend e x) (Γ.map Formula.shift) := by
  intro χ hχ
  obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hχ
  exact (Formula.eval_shift φ e x).2 (hΓ φ hφ)

/-- **Each rule instance is valid in ℕ**: valid premises give a valid conclusion. -/
theorem rule_valid (r : Rule n) (hs : r.side T = true) (hp : ∀ p ∈ r.prems, p.Valid) :
    r.concl.Valid := by
  cases r <;> simp only [Rule.prems, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq] at hp <;> simp only [Rule.side, decide_eq_true_eq] at hs <;>
    intro e hΓ
  case hyp => exact hΓ _ hs
  case ax a => exact axiom_valid T a hs e
  case weaken => exact hp e (fun φ hφ => hΓ φ (hs φ hφ))
  case impIntro => exact fun hφ => hp e (satisfies_cons hφ hΓ)
  case impElim => exact hp.1 e hΓ (hp.2 e hΓ)
  case botElim => exact (hp e hΓ).elim
  case classical => exact Classical.byContradiction (hp e hΓ)
  case conjIntro => exact ⟨hp.1 e hΓ, hp.2 e hΓ⟩
  case conjLeft => exact (hp e hΓ).1
  case conjRight => exact (hp e hΓ).2
  case disjLeft => exact Or.inl (hp e hΓ)
  case disjRight => exact Or.inr (hp e hΓ)
  case disjElim =>
    rcases hp.1 e hΓ with hφ | hψ
    · exact hp.2.1 e (satisfies_cons hφ hΓ)
    · exact hp.2.2 e (satisfies_cons hψ hΓ)
  case allIntro => exact fun x => hp (extend e x) (satisfies_shift x hΓ)
  case allElim t => exact (Formula.eval_inst _ t e).2 (hp e hΓ (t.eval e))
  case exIntro t => exact ⟨t.eval e, (Formula.eval_inst _ t e).1 (hp e hΓ)⟩
  case exElim =>
    obtain ⟨x, hx⟩ := hp.1 e hΓ
    exact (Formula.eval_shift _ e x).1 (hp.2 (extend e x) (satisfies_cons hx (satisfies_shift x hΓ)))
  case eqRefl => rfl
  case eqElim φ s t =>
    apply (Formula.eval_inst φ _ e).2
    have h := (Formula.eval_inst φ _ e).1 (hp.2 e hΓ)
    have heq := hp.1 e hΓ
    change _ = _ at heq
    rwa [heq] at h

/-- A rule instance with valid subproofs gives a valid tree. -/
theorem infer_valid {r : Rule n} (hs : r.side T = true) {ts : List (system T).Proof}
    (hts : ∀ t ∈ ts, (system T).Valid [] t) (hmap : ts.map ProofTree.concl = r.prems) :
    (system T).derives [] r.concl :=
  ⟨.infer ⟨n, r⟩ r.concl ts, .infer ⟨hs, hmap.symm, rfl⟩ hts, rfl⟩

theorem trees {ss : List Seq} (h : ∀ s ∈ ss, (system T).derives [] s) :
    ∃ ts : List (system T).Proof, (∀ t ∈ ts, (system T).Valid [] t) ∧
      ts.map ProofTree.concl = ss :=
  DerivationSystem.exists_trees h

theorem by_rule (r : Rule n) (hs : r.side T = true)
    (hp : ∀ p ∈ r.prems, (system T).derives [] p) : (system T).derives [] r.concl := by
  obtain ⟨ts, hts, hmap⟩ := trees hp
  exact infer_valid hs hts hmap

theorem basic_code {φ : Formula n} (b : BasicAxiom φ) :
    ∃ a : AxiomCode n, (∀ T, a.inTheory T = true) ∧ a.formula = φ := by
  cases b with
  | succNonzero t => exact ⟨.succNonzero t, fun T => by cases T <;> rfl, rfl⟩
  | succInjective s t => exact ⟨.succInjective s t, fun T => by cases T <;> rfl, rfl⟩
  | addZero t => exact ⟨.addZero t, fun T => by cases T <;> rfl, rfl⟩
  | addSucc s t => exact ⟨.addSucc s t, fun T => by cases T <;> rfl, rfl⟩
  | mulZero t => exact ⟨.mulZero t, fun T => by cases T <;> rfl, rfl⟩
  | mulSucc s t => exact ⟨.mulSucc s t, fun T => by cases T <;> rfl, rfl⟩

theorem axiom_code (T : Theory) {φ : Formula n} (h : T.Ax φ) :
    ∃ a : AxiomCode n, a.inTheory T = true ∧ a.formula = φ := by
  cases T
  · cases h with
    | basic h => obtain ⟨a, ha, hf⟩ := basic_code h; exact ⟨a, ha _, hf⟩
    | pred t => exact ⟨.pred t, rfl, rfl⟩
  · cases h with
    | basic h => obtain ⟨a, ha, hf⟩ := basic_code h; exact ⟨a, ha _, hf⟩
    | induction φ => exact ⟨.induction φ, rfl, rfl⟩

/-- **Every `Derivation` is a valid proof tree.** -/
theorem tree_of_derivation {Γ : Context n} {φ : Formula n} (d : Derivation T.Ax Γ φ) :
    (system T).derives [] ⟨n, Γ, φ⟩ := by
  induction d with
  | hyp h => exact by_rule (.hyp _ _) (by simpa [Rule.side] using h) (by simp [Rule.prems])
  | @ax n φ Γ h =>
    obtain ⟨a, ha, rfl⟩ := axiom_code T h
    exact by_rule (.ax Γ a) ha (by simp [Rule.prems])
  | weaken h _ ih => exact by_rule (.weaken _ _ _) (by simpa [Rule.side] using h) (by simpa [Rule.prems])
  | impIntro _ ih => exact by_rule (.impIntro _ _ _) rfl (by simpa [Rule.prems])
  | @impElim n φ ψ Γ _ _ ih₁ ih₂ => exact by_rule (.impElim Γ φ ψ) rfl (by simp [Rule.prems, ih₁, ih₂])
  | botElim _ ih => exact by_rule (.botElim _ _) rfl (by simpa [Rule.prems])
  | classical _ ih => exact by_rule (.classical _ _) rfl (by simpa [Rule.prems])
  | conjIntro _ _ ih₁ ih₂ => exact by_rule (.conjIntro _ _ _) rfl (by simp [Rule.prems, ih₁, ih₂])
  | conjLeft _ ih => exact by_rule (.conjLeft _ _ _) rfl (by simpa [Rule.prems])
  | conjRight _ ih => exact by_rule (.conjRight _ _ _) rfl (by simpa [Rule.prems])
  | disjLeft _ ih => exact by_rule (.disjLeft _ _ _) rfl (by simpa [Rule.prems])
  | disjRight _ ih => exact by_rule (.disjRight _ _ _) rfl (by simpa [Rule.prems])
  | @disjElim n φ ψ χ Γ _ _ _ ih₁ ih₂ ih₃ =>
    exact by_rule (.disjElim Γ φ ψ χ) rfl (by simp [Rule.prems, ih₁, ih₂, ih₃])
  | allIntro _ ih => exact by_rule (.allIntro _ _) rfl (by simpa [Rule.prems])
  | allElim _ t ih => exact by_rule (.allElim _ _ t) rfl (by simpa [Rule.prems])
  | exIntro t _ ih => exact by_rule (.exIntro _ _ t) rfl (by simpa [Rule.prems])
  | @exElim n Γ φ ψ _ _ ih₁ ih₂ => exact by_rule (.exElim Γ φ ψ) rfl (by simp [Rule.prems, ih₁, ih₂])
  | eqRefl t => exact by_rule (.eqRefl _ t) rfl (by simp [Rule.prems])
  | @eqElim n Γ s t φ _ _ ih₁ ih₂ => exact by_rule (.eqElim Γ φ s t) rfl (by simp [Rule.prems, ih₁, ih₂])

end Silmaril.Proofs.Logic.Consequence.Arithmetic.Derivation
