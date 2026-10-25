module

public import Silmaril.Logic.Metamath.Peano.Model

@[expose] public section

/-!
# Soundness and consistency of `peano.mm`

Every axiom of `peano.mm` holds in the standard model (`Peano.isModel_PA`).
The propositional and equality axioms are tautologies, the quantifier axioms
hold for arbitrary generalized quantifiers thanks to their disjoint-variable
conditions, and the arithmetic axioms and the induction scheme are facts about
ℕ.

Consequently every theorem of `PA` holds in the standard model, at the tree
level (`Peano.sound`) and at the string level (`Peano.sound_str`). The model is
not trivial, so `PA` is consistent: it does not prove the falsum `|- phi`
(`Peano.not_tderivable_falsum`), it is consistent at `|-` (`Peano.tConsistent`)
and as a string system (`Peano.nonUniversal`), and its theory lies strictly
below the top of the lattice of theories (`Peano.theory_ne_top`). It does not
prove `|- = 0 S 0` (`Peano.not_derivable_zero_eq_one`).
-/

namespace Silmaril.Logic.Metamath.Peano

open Silmaril.Logic.Metamath Grammar Grammar.TAssertion Silmaril.Logic.SetTheory Function Env

variable {N : Type} [DecidableEq N] [Infinite N]

theorem mem_axiomList {A : TAssertion L C V} (h : A ∈ axiomList.map Prod.snd) : A ∈ PA :=
  mem_PA.2 h

/-- Compute values in the standard model. -/
macro "value_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [value_tvar, value_tzero, value_tsucc,
  value_tbinop, value_binopPlus, value_binopTimes, value_wffAtom, value_binpredEquals,
  value_binpredLessThan, value_wffNot, value_wffLogbinop, value_logbinopOr, value_logbinopAnd,
  value_logbinopImplies, value_logbinopIff, value_wffQuant, value_quantAll, value_quantEx,
  Model.value_var, app₂_apply, opQuant_apply, const_apply, map_apply, name_apply, id, Valid]
  $[$loc]?)

/-! ## Disjoint-variable conditions -/

section DV

variable {A : TAssertion L C V} {ρ : (stdModel N).Valuation A.ctx}
  (hdv : (stdModel N).DVHolds ρ A.dv) {a b : V}

include hdv

theorem ne_of_dv (hab : (a, b) ∈ A.dv) (hne : a ≠ b) (ha : grammar.synCtx A.ctx a .var)
    (hb : grammar.synCtx A.ctx b .var) : (ρ a .var ha : N) ≠ ρ b .var hb :=
  Kind.fresh_name_name.1 (hdv a b hab hne _ _ ha hb)

theorem notFree_of_dv_wff (hab : (a, b) ∈ A.dv) (hne : a ≠ b) (ha : grammar.synCtx A.ctx a .wff)
    (hb : grammar.synCtx A.ctx b .var) :
    NotFree (ρ b .var hb : N) (ρ a .wff ha : Term ℕ N Prop).1 :=
  Kind.fresh_formula_name.1 (hdv a b hab hne _ _ ha hb)

theorem notFree_of_dv_var_wff (hab : (a, b) ∈ A.dv) (hne : a ≠ b)
    (ha : grammar.synCtx A.ctx a .var) (hb : grammar.synCtx A.ctx b .wff) :
    NotFree (ρ a .var ha : N) (ρ b .wff hb : Term ℕ N Prop).1 :=
  Kind.fresh_name_formula.1 (hdv a b hab hne _ _ ha hb)

theorem notFree_of_dv_term (hab : (a, b) ∈ A.dv) (hne : a ≠ b)
    (ha : grammar.synCtx A.ctx a .var) (hb : grammar.synCtx A.ctx b .term) :
    NotFree (ρ a .var ha : N) (ρ b .term hb : Term ℕ N ℕ).1 :=
  Kind.fresh_name_term.1 (hdv a b hab hne _ _ ha hb)

end DV

omit [Infinite N] in
theorem apply_update_update {R : Type} {f : Term ℕ N R} {a b : N} (hab : a ≠ b)
    (hf : NotFree a f.1) (E : SetTheory.Env ℕ N) (n m : ℕ) :
    f.1 (update (update E a n) b m) = f.1 (update E b m) := by
  rw [update_comm hab, hf]

/-! ## The axioms hold in the standard model -/

/-- The essential hypotheses of an axiom, as valid formulas. -/
theorem valid_of_holds {A : TAssertion L C V} {ρ : (stdModel N).Valuation A.ctx} {t : Tree L V}
    (h : (stdModel N).Holds ρ (T.pf t)) :
    ∃ ht : grammar.HasSort (grammar.synCtx A.ctx) t .wff,
      Valid ((stdModel N).value ρ t ht : Term ℕ N Prop).1 :=
  (holds_iff N ρ t).1 h

theorem sat_ax1 : (stdModel N).Satisfies ax1 :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; exact fun h _ => h

theorem sat_ax2 : (stdModel N).Satisfies ax2 :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; exact fun h₁ h₂ h₃ => h₁ h₃ (h₂ h₃)

theorem sat_ax3 : (stdModel N).Satisfies ax3 :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by
      value_simp
      exact fun h hψ => Classical.byContradiction fun hφ => h hφ hψ

theorem sat_axMp : (stdModel N).Satisfies axMp :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ hess ht E => by
      obtain ⟨_, h₁⟩ := valid_of_holds (hess (T.pf (T.mv .phi)) (by simp [axMp, essentials]))
      obtain ⟨_, h₂⟩ := valid_of_holds (hess (T.pf (T.imp (T.mv .phi) (T.mv .psi)))
        (by simp [axMp, essentials]))
      value_simp at h₁ h₂ ⊢
      exact h₂ E (h₁ E)

theorem sat_bi1 : (stdModel N).Satisfies bi1 :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; exact fun h => h.1

theorem sat_bi2 : (stdModel N).Satisfies bi2 :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; exact fun h => h.2

theorem sat_bi3 : (stdModel N).Satisfies bi3 :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; exact fun h₁ h₂ => ⟨h₁, h₂⟩

theorem sat_dfAn : (stdModel N).Satisfies dfAn :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; tauto

theorem sat_dfOr : (stdModel N).Satisfies dfOr :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; tauto

theorem sat_eqRefl : (stdModel N).Satisfies eqRefl :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp

theorem sat_eqSym : (stdModel N).Satisfies eqSym :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; exact Eq.symm

theorem sat_eqTrans : (stdModel N).Satisfies eqTrans :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; exact fun h => h.1.trans h.2

theorem sat_eqCongr : (stdModel N).Satisfies eqCongr :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; rintro ⟨h₁, h₂⟩; rw [h₁, h₂]

theorem sat_eqSuc : (stdModel N).Satisfies eqSuc :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; exact congrArg Nat.succ

theorem sat_eqBinop : (stdModel N).Satisfies eqBinop :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; rintro ⟨h₁, h₂⟩; rw [h₁, h₂]

theorem sat_alpha1 : (stdModel N).Satisfies alpha1 :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ hdv hess ht E => by
      obtain ⟨_, h⟩ := valid_of_holds
        (hess (T.pf (T.imp (T.mv .phi) (T.iff (T.mv .psi) (T.mv .chi))))
          (by simp [alpha1, essentials]))
      have hx : grammar.synCtx alpha1.ctx .x .var := ⟨by simp [alpha1, ctx], rfl⟩
      have hphi : grammar.synCtx alpha1.ctx .phi .wff := ⟨by simp [alpha1, ctx], rfl⟩
      have hpx := notFree_of_dv_wff hdv (by simp [alpha1]) (by decide) hphi hx
      value_simp at h ⊢
      generalize ρ .x .var hx = a at *
      generalize ρ .phi .wff hphi = φ at *
      intro hφ
      exact iff_of_eq (congrArg _ (funext fun m => propext (h _ ((hpx E m).symm ▸ hφ))))

theorem sat_alpha2 : (stdModel N).Satisfies alpha2 :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ hdv hess ht E => by
      obtain ⟨_, h⟩ := valid_of_holds (hess (T.pf (T.imp (T.mv .phi) (T.mv .chi)))
        (by simp [alpha2, essentials]))
      have hx : grammar.synCtx alpha2.ctx .x .var := ⟨by simp [alpha2, ctx], rfl⟩
      have hphi : grammar.synCtx alpha2.ctx .phi .wff := ⟨by simp [alpha2, ctx], rfl⟩
      have hpx := notFree_of_dv_wff hdv (by simp [alpha2]) (by decide) hphi hx
      value_simp at h ⊢
      generalize ρ .x .var hx = a at *
      generalize ρ .phi .wff hphi = φ at *
      exact fun hφ m => h _ ((hpx E m).symm ▸ hφ)

theorem sat_alpha3 : (stdModel N).Satisfies alpha3 :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ hdv _ ht E => by
      have hx : grammar.synCtx alpha3.ctx .x .var := ⟨by simp [alpha3, ctx], rfl⟩
      have hy : grammar.synCtx alpha3.ctx .y .var := ⟨by simp [alpha3, ctx], rfl⟩
      have hphi : grammar.synCtx alpha3.ctx .phi .wff := ⟨by simp [alpha3, ctx], rfl⟩
      have hpsi : grammar.synCtx alpha3.ctx .psi .wff := ⟨by simp [alpha3, ctx], rfl⟩
      have hxy := ne_of_dv hdv (by simp [alpha3]) (by decide) hx hy
      have hpy := notFree_of_dv_wff hdv (by simp [alpha3]) (by decide) hphi hy
      have hqx := notFree_of_dv_wff hdv (by simp [alpha3]) (by decide) hpsi hx
      value_simp
      generalize ρ .x .var hx = a at *
      generalize ρ .y .var hy = b at *
      generalize ρ .phi .wff hphi = φ at *
      generalize ρ .psi .wff hpsi = ψ at *
      intro h
      refine iff_of_eq (congrArg _ (funext fun m => propext ?_))
      have := h m m (by simp [update_of_ne hxy])
      rwa [hpy, apply_update_update hxy hqx] at this

theorem sat_allElim : (stdModel N).Satisfies allElim :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; exact fun h n _ => h n

theorem sat_allElim2 : (stdModel N).Satisfies allElim2 :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ hdv hess ht E => by
      obtain ⟨_, h⟩ := valid_of_holds
        (hess (T.pf (T.imp (T.eq (T.tv .x) (T.mv .t)) (T.iff (T.mv .phi) (T.mv .chi))))
          (by simp [allElim2, essentials]))
      have hx : grammar.synCtx allElim2.ctx .x .var := ⟨by simp [allElim2, ctx], rfl⟩
      have hy : grammar.synCtx allElim2.ctx .y .var := ⟨by simp [allElim2, ctx], rfl⟩
      have ht : grammar.synCtx allElim2.ctx .t .term := ⟨by simp [allElim2, ctx], rfl⟩
      have hxy := ne_of_dv hdv (by simp [allElim2]) (by decide) hx hy
      have hyt := notFree_of_dv_term hdv (by simp [allElim2]) (by decide) hy ht
      value_simp at h ⊢
      generalize ρ .x .var hx = a at *
      generalize ρ .y .var hy = b at *
      generalize ρ .t .term ht = τ at *
      intro he
      refine iff_of_eq (congrArg _ (funext fun m => propext (h _ ?_)))
      rw [update_of_ne hxy, hyt]
      exact he

theorem sat_allElim3 : (stdModel N).Satisfies allElim3 :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ hdv hess ht E => by
      obtain ⟨_, h⟩ := valid_of_holds
        (hess (T.pf (T.imp (T.eq (T.tv .x) (T.mv .t)) (T.iff (T.mv .phi) (T.mv .chi))))
          (by simp [allElim3, essentials]))
      have hx : grammar.synCtx allElim3.ctx .x .var := ⟨by simp [allElim3, ctx], rfl⟩
      have hchi : grammar.synCtx allElim3.ctx .chi .wff := ⟨by simp [allElim3, ctx], rfl⟩
      have ht : grammar.synCtx allElim3.ctx .t .term := ⟨by simp [allElim3, ctx], rfl⟩
      have hxc := notFree_of_dv_var_wff hdv (by simp [allElim3]) (by decide) hx hchi
      have hxt := notFree_of_dv_term hdv (by simp [allElim3]) (by decide) hx ht
      value_simp at h ⊢
      generalize ρ .x .var hx = a at *
      generalize ρ .chi .wff hchi = χ at *
      generalize ρ .t .term ht = τ at *
      intro hall
      have he : update E a (τ.1 E) a = τ.1 (update E a (τ.1 E)) := by rw [update_self, hxt]
      have := (h _ he).1 (hall _ he)
      rwa [hxc] at this

theorem sat_existsDef : (stdModel N).Satisfies existsDef :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; exact not_forall_not.symm

theorem sat_paAx1 : (stdModel N).Satisfies paAx1 :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; exact (Nat.succ_ne_zero _).symm

theorem sat_paAx2 : (stdModel N).Satisfies paAx2 :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; exact Nat.succ.inj

theorem sat_paAx3 : (stdModel N).Satisfies paAx3 :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; exact (Nat.add_zero _).symm

theorem sat_paAx4 : (stdModel N).Satisfies paAx4 :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; exact (Nat.add_succ _ _).symm

theorem sat_paAx5 : (stdModel N).Satisfies paAx5 :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; exact (Nat.mul_zero _).symm

theorem sat_paAx6 : (stdModel N).Satisfies paAx6 :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ _ _ ht E => by value_simp; exact (Nat.mul_succ _ _).symm

theorem sat_paAx7 : (stdModel N).Satisfies paAx7 :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ hdv _ ht E => by
      have hx : grammar.synCtx paAx7.ctx .x .var := ⟨by simp [paAx7, ctx], rfl⟩
      have hy : grammar.synCtx paAx7.ctx .y .var := ⟨by simp [paAx7, ctx], rfl⟩
      have hz : grammar.synCtx paAx7.ctx .z .var := ⟨by simp [paAx7, ctx], rfl⟩
      have hzx := ne_of_dv hdv (by simp [paAx7]) (by decide) hz hx
      have hzy := ne_of_dv hdv (by simp [paAx7]) (by decide) hz hy
      value_simp
      generalize ρ .x .var hx = a at *
      generalize ρ .y .var hy = b at *
      generalize ρ .z .var hz = c at *
      simp only [update_of_ne hzx.symm, update_of_ne hzy.symm, update_self]
      constructor
      · intro h
        exact ⟨E b - E a - 1, by omega⟩
      · rintro ⟨n, h⟩
        omega

theorem sat_induction : (stdModel N).Satisfies induction :=
  satisfies_of_valid N (wellFormed_PA _ (mem_axiomList (by simp [axiomList]))) rfl
    fun ρ hdv _ ht E => by
      have hx : grammar.synCtx induction.ctx .x .var := ⟨by simp [induction, ctx], rfl⟩
      have hy : grammar.synCtx induction.ctx .y .var := ⟨by simp [induction, ctx], rfl⟩
      have hphi : grammar.synCtx induction.ctx .phi .wff := ⟨by simp [induction, ctx], rfl⟩
      have hxy := ne_of_dv hdv (by simp [induction]) (by decide) hx hy
      have hpx := notFree_of_dv_wff hdv (by simp [induction]) (by decide) hphi hx
      value_simp
      generalize ρ .x .var hx = a at *
      generalize ρ .y .var hy = b at *
      generalize ρ .phi .wff hphi = φ at *
      simp only [update_self, update_of_ne hxy, apply_update_update hxy hpx]
      rintro ⟨h₀, hs⟩ n m rfl
      induction m with
      | zero => exact h₀ 0 rfl
      | succ m ih => exact hs m (fun k hk => hk ▸ ih) (m + 1) rfl

/-- The standard model is a model of `PA`. -/
theorem isModel_PA : (stdModel N).IsModel PA := by
  intro B hB
  rw [mem_PA] at hB
  simp only [axiomList, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  exacts [sat_ax1, sat_ax2, sat_ax3, sat_axMp, sat_bi1, sat_bi2, sat_bi3, sat_dfAn, sat_dfOr,
    sat_eqRefl, sat_eqSym, sat_eqTrans, sat_eqCongr, sat_eqSuc, sat_eqBinop, sat_alpha1,
    sat_alpha2, sat_alpha3, sat_allElim, sat_allElim2, sat_allElim3, sat_existsDef, sat_paAx1,
    sat_paAx2, sat_paAx3, sat_paAx4, sat_paAx5, sat_paAx6, sat_paAx7, sat_induction]

/-! ## Soundness and consistency -/

/-- Soundness: every tree theorem of `PA` holds in the standard model. -/
theorem sound {A : TAssertion L C V} (h : TDerivable grammar PA A) : (stdModel N).Satisfies A :=
  (stdModel N).sound wellFormed_PA isModel_PA h

/-- Soundness for string theorems: every string theorem of the syntax axioms
and the flattened axioms of `PA` holds in the standard model. -/
theorem sound_str {A : Assertion C V} (h : Derivable (grammar.axioms PA) A) :
    (stdModel N).SatisfiesStr A :=
  (stdModel N).sound_str unambiguous wellFormed_PA isModel_PA h

/-- The standard model is not trivial: the constantly false formula is not valid. -/
theorem not_trivialAt : ¬ (stdModel N).TrivialAt (c := .turnstile) (s := .wff) rfl :=
  fun h => h (Term.const False) fun _ => 0

/-- `PA` does not prove the falsum `|- phi`. -/
theorem not_tderivable_falsum : ¬ TDerivable grammar PA (falsum .turnstile .wff .phi) :=
  Model.not_tderivable_falsum (M := stdModel ℕ) wellFormed_PA isModel_PA rfl not_trivialAt .phi

/-- `PA` is consistent at `|-`. -/
theorem tConsistent : TConsistent grammar PA .turnstile :=
  Model.tConsistent (M := stdModel ℕ) wellFormed_PA isModel_PA rfl not_trivialAt .phi

/-- The string system of `PA` is consistent. -/
theorem nonUniversal : (system (grammar.axioms PA)).NonUniversal :=
  Model.nonUniversal_system (M := stdModel ℕ) unambiguous wellFormed_PA isModel_PA rfl
    not_trivialAt .phi

/-- The theory of `PA` lies strictly below the top of the lattice of theories. -/
theorem theory_ne_top : Theory.of (grammar.wfAxioms PA) ≠ ⊤ :=
  Model.theory_ne_top (M := stdModel ℕ) unambiguous wellFormed_PA isModel_PA rfl
    not_trivialAt .phi

/-- The assertion `|- = 0 S 0`. -/
def zeroEqOne : TAssertion L C V := ⟨[], [], T.pf (T.eq T.zero (T.succ T.zero))⟩

theorem wellFormed_zeroEqOne : zeroEqOne.WellFormed grammar := .of_checkWF (by decide)

theorem not_satisfies_zeroEqOne : ¬ (stdModel N).Satisfies zeroEqOne := by
  intro h
  obtain ⟨_, h⟩ := valid_of_holds (h (fun _ _ h => absurd h.1 (by simp [zeroEqOne, ctx]))
    (by simp [Model.DVHolds, zeroEqOne]) (by simp [zeroEqOne, essentials]))
  value_simp at h
  exact Nat.zero_ne_one (h fun _ => 0)

/-- `PA` does not prove `|- = 0 S 0`, as a string theorem. -/
theorem not_derivable_zero_eq_one :
    ¬ Derivable (grammar.axioms PA) (zeroEqOne.flatten grammar) :=
  Model.not_derivable (M := stdModel ℕ) unambiguous wellFormed_PA isModel_PA
    wellFormed_zeroEqOne not_satisfies_zeroEqOne

end Silmaril.Logic.Metamath.Peano
