module

public import Silmaril.Logic.Metamath.SecondOrder.Model
public import Silmaril.Logic.Metamath.SecondOrder.Validity
public import Silmaril.Logic.Metamath.SecondOrder.Systems

@[expose] public section

/-!
# The axioms of second-order arithmetic in ω-models

Every axiom of `base` (predicate calculus, definitions, equality, basic
arithmetic, formation rules of the formula classes) and each induction
schema holds in every ω-model `model 𝒮 N` (`isModel_base`, `sat_axInd`,
`sat_axIndSig1`). The comprehension schemes hold when `𝒮` is closed under the
corresponding comprehension (`ComprehensionClosed`, `Delta1Closed`,
`SeparationClosed`), so an ω-model closed under
Δ⁰₁-comprehension is a model of `RCA0` (`isModel_RCA0`), and similarly for
`WKL0`, `ACA0` and `Z2`. The full model `𝒮 = 𝒫(ℕ)` is closed under all of them
and satisfies every axiom of `z2.mm` (`isModel_full`).
-/

namespace Silmaril.Logic.Metamath.SecondOrder

open Grammar Sem Function

variable {𝒮 : Set (Set ℕ)} {N : Type} [DecidableEq N] [Infinite N]

/-! ## Truth of expressions -/

section Truth

variable {ctx : V → C → Prop} (ρ : (model 𝒮 N).Valuation ctx)

theorem holds_iff {c : C} (hc : grammar.prov c = some .wff) (t : Tree L V) :
    (model 𝒮 N).Holds ρ ⟨c, t⟩ ↔ ∃ h : grammar.HasSort (grammar.synCtx ctx) t .wff,
      (model 𝒮 N).IsTrue hc ((model 𝒮 N).value ρ t h) := by
  constructor
  · rintro ⟨s, hs, h, ht⟩
    obtain rfl : .wff = s := Option.some.inj (hc.symm.trans hs)
    exact ⟨h, ht⟩
  · rintro ⟨h, ht⟩
    exact ⟨_, hc, h, ht⟩

variable {ρ}

theorem valid_of_holds {t : Tree L V} (h : (model 𝒮 N).Holds ρ ⟨.turnstile, t⟩) :
    ∃ ht : grammar.HasSort (grammar.synCtx ctx) t .wff,
      Valid ((model 𝒮 N).value ρ t ht).1 :=
  (holds_iff ρ rfl t).1 h

theorem isBnd_of_holds {t : Tree L V} (h : (model 𝒮 N).Holds ρ ⟨.bnd, t⟩) :
    ∃ ht : grammar.HasSort (grammar.synCtx ctx) t .wff,
      IsBnd ((model 𝒮 N).value ρ t ht).1 :=
  (holds_iff ρ rfl t).1 h

theorem isSig1_of_holds {t : Tree L V} (h : (model 𝒮 N).Holds ρ ⟨.sig1, t⟩) :
    ∃ ht : grammar.HasSort (grammar.synCtx ctx) t .wff,
      IsSig1 ((model 𝒮 N).value ρ t ht).1 :=
  (holds_iff ρ rfl t).1 h

theorem isPi1_of_holds {t : Tree L V} (h : (model 𝒮 N).Holds ρ ⟨.pi1, t⟩) :
    ∃ ht : grammar.HasSort (grammar.synCtx ctx) t .wff,
      IsPi1 ((model 𝒮 N).value ρ t ht).1 :=
  (holds_iff ρ rfl t).1 h

theorem isArith_of_holds {t : Tree L V} (h : (model 𝒮 N).Holds ρ ⟨.arith, t⟩) :
    ∃ ht : grammar.HasSort (grammar.synCtx ctx) t .wff,
      IsArith ((model 𝒮 N).value ρ t ht).1 :=
  (holds_iff ρ rfl t).1 h

end Truth

/-- An assertion holds when its conclusion is true under every valuation
satisfying its hypotheses. -/
theorem satisfies_of_isTrue {A : TAssertion L C V} {c : C} {t : Tree L V}
    (hA : A.WellFormed grammar) (hc : A.concl = ⟨c, t⟩) (hs : grammar.prov c = some .wff)
    (h : ∀ ρ : (model 𝒮 N).Valuation A.ctx, (model 𝒮 N).DVHolds ρ A.dv →
      (∀ e ∈ A.essentials, (model 𝒮 N).Holds ρ e) →
      ∀ ht : grammar.HasSort (grammar.synCtx A.ctx) t .wff,
        (model 𝒮 N).IsTrue hs ((model 𝒮 N).value ρ t ht)) :
    (model 𝒮 N).Satisfies A := by
  intro ρ hdv hess
  obtain ⟨s, hs', ht⟩ := hA.concl_wellTyped
  rw [hc] at hs' ht ⊢
  obtain rfl : .wff = s := Option.some.inj (hs.symm.trans hs')
  exact (holds_iff ρ hs t).2 ⟨ht.synCtx rfl, h ρ hdv hess _⟩

/-- An assertion at `|-` holds when its conclusion is valid under every
valuation satisfying its hypotheses. -/
theorem satisfies_of_valid {A : TAssertion L C V} {t : Tree L V} (hA : A.WellFormed grammar)
    (hc : A.concl = ⟨.turnstile, t⟩)
    (h : ∀ ρ : (model 𝒮 N).Valuation A.ctx, (model 𝒮 N).DVHolds ρ A.dv →
      (∀ e ∈ A.essentials, (model 𝒮 N).Holds ρ e) →
      ∀ ht : grammar.HasSort (grammar.synCtx A.ctx) t .wff,
        Valid ((model 𝒮 N).value ρ t ht).1) :
    (model 𝒮 N).Satisfies A :=
  satisfies_of_isTrue hA hc rfl h

theorem satisfies_of_isBnd {A : TAssertion L C V} {t : Tree L V} (hA : A.WellFormed grammar)
    (hc : A.concl = ⟨.bnd, t⟩)
    (h : ∀ ρ : (model 𝒮 N).Valuation A.ctx, (model 𝒮 N).DVHolds ρ A.dv →
      (∀ e ∈ A.essentials, (model 𝒮 N).Holds ρ e) →
      ∀ ht : grammar.HasSort (grammar.synCtx A.ctx) t .wff,
        IsBnd ((model 𝒮 N).value ρ t ht).1) :
    (model 𝒮 N).Satisfies A :=
  satisfies_of_isTrue hA hc rfl h

theorem satisfies_of_isSig1 {A : TAssertion L C V} {t : Tree L V} (hA : A.WellFormed grammar)
    (hc : A.concl = ⟨.sig1, t⟩)
    (h : ∀ ρ : (model 𝒮 N).Valuation A.ctx, (model 𝒮 N).DVHolds ρ A.dv →
      (∀ e ∈ A.essentials, (model 𝒮 N).Holds ρ e) →
      ∀ ht : grammar.HasSort (grammar.synCtx A.ctx) t .wff,
        IsSig1 ((model 𝒮 N).value ρ t ht).1) :
    (model 𝒮 N).Satisfies A :=
  satisfies_of_isTrue hA hc rfl h

theorem satisfies_of_isPi1 {A : TAssertion L C V} {t : Tree L V} (hA : A.WellFormed grammar)
    (hc : A.concl = ⟨.pi1, t⟩)
    (h : ∀ ρ : (model 𝒮 N).Valuation A.ctx, (model 𝒮 N).DVHolds ρ A.dv →
      (∀ e ∈ A.essentials, (model 𝒮 N).Holds ρ e) →
      ∀ ht : grammar.HasSort (grammar.synCtx A.ctx) t .wff,
        IsPi1 ((model 𝒮 N).value ρ t ht).1) :
    (model 𝒮 N).Satisfies A :=
  satisfies_of_isTrue hA hc rfl h

theorem satisfies_of_isArith {A : TAssertion L C V} {t : Tree L V} (hA : A.WellFormed grammar)
    (hc : A.concl = ⟨.arith, t⟩)
    (h : ∀ ρ : (model 𝒮 N).Valuation A.ctx, (model 𝒮 N).DVHolds ρ A.dv →
      (∀ e ∈ A.essentials, (model 𝒮 N).Holds ρ e) →
      ∀ ht : grammar.HasSort (grammar.synCtx A.ctx) t .wff,
        IsArith ((model 𝒮 N).value ρ t ht).1) :
    (model 𝒮 N).Satisfies A :=
  satisfies_of_isTrue hA hc rfl h

/-! ## Disjoint-variable conditions -/

theorem ne_of_fresh {x y : N} (h : (model 𝒮 N).Fresh (s := .nvar) (t := .nvar) x y) : x ≠ y :=
  fun e => h.1 _ rfl _ rfl (congrArg Sum.inl e)

theorem ignores_of_fresh_wff {x : N} {φ : (model 𝒮 N).Carrier .wff}
    (h : (model 𝒮 N).Fresh (s := .nvar) (t := .wff) x φ) : Ignores φ.1 (.inl x) :=
  h.2.1 _ rfl

theorem ignores_of_fresh_term {x : N} {a : (model 𝒮 N).Carrier .term}
    (h : (model 𝒮 N).Fresh (s := .nvar) (t := .term) x a) : Ignores a.1 (.inl x) :=
  h.2.1 _ rfl

theorem ignores_of_fresh_svar_wff {X : N} {φ : (model 𝒮 N).Carrier .wff}
    (h : (model 𝒮 N).Fresh (s := .svar) (t := .wff) X φ) : Ignores φ.1 (.inr X) :=
  h.2.1 _ rfl

/-- Compute the values of the trees of an assertion of `z2.mm`. -/
macro "z2_values" : tactic => `(tactic| simp only [val_tvar, val_t0, val_tS, val_tpl,
  val_tmu, val_wn, val_wi, val_wb, val_wa, val_wal, val_wex, val_wsal, val_wsex, val_weq, val_wlt,
  val_wel, val_wseq, val_var])

/-- Compute the values of the trees of an assertion of `z2.mm` in a hypothesis. -/
macro "z2_values" " at " h:ident : tactic => `(tactic| simp only [val_tvar, val_t0,
  val_tS, val_tpl, val_tmu, val_wn, val_wi, val_wb, val_wa, val_wal, val_wex, val_wsal, val_wsex,
  val_weq, val_wlt, val_wel, val_wseq, val_var] at $h:ident)

/-! ## Predicate calculus -/

section Logic

theorem sat_axMp : (model 𝒮 N).Satisfies axMp :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ hess _ => by
    obtain ⟨_, h₁⟩ := valid_of_holds (hess ⟨.turnstile, .var .ph⟩ (by decide))
    obtain ⟨_, h₂⟩ := valid_of_holds (hess ⟨.turnstile, .node .wi [.var .ph, .var .ps]⟩
      (by decide))
    z2_values at h₁
    z2_values at h₂
    z2_values
    exact valid_mp h₁ h₂

theorem sat_ax1 : (model 𝒮 N).Satisfies ax1 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_ax1 _ _

theorem sat_ax2 : (model 𝒮 N).Satisfies ax2 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_ax2 _ _ _

theorem sat_ax3 : (model 𝒮 N).Satisfies ax3 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_ax3 _ _

theorem sat_dfBi1 : (model 𝒮 N).Satisfies dfBi1 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_dfBi1 _ _

theorem sat_dfBi2 : (model 𝒮 N).Satisfies dfBi2 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_dfBi2 _ _

theorem sat_dfBi3 : (model 𝒮 N).Satisfies dfBi3 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_dfBi3 _ _

theorem sat_dfAn : (model 𝒮 N).Satisfies dfAn :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_dfAn _ _

theorem sat_ax4 : (model 𝒮 N).Satisfies ax4 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_ax4 _ _ _

theorem sat_ax6 : (model 𝒮 N).Satisfies ax6 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_ax6 _ _

theorem sat_ax7 : (model 𝒮 N).Satisfies ax7 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_ax7 _ _ _

theorem sat_ax10 : (model 𝒮 N).Satisfies ax10 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_ax10 _ _

theorem sat_ax11 : (model 𝒮 N).Satisfies ax11 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_ax11 _ _ _

theorem sat_ax12 : (model 𝒮 N).Satisfies ax12 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_ax12 _ _ _

theorem sat_ax13 : (model 𝒮 N).Satisfies ax13 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_ax13 _ _ _

theorem sat_dfEx : (model 𝒮 N).Satisfies dfEx :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_dfEx _ _

theorem sat_axS4 : (model 𝒮 N).Satisfies axS4 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_s4 _ _ _

theorem sat_axS6 : (model 𝒮 N).Satisfies axS6 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_s6 _ _

theorem sat_axS7 : (model 𝒮 N).Satisfies axS7 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_s7 _ _ _

theorem sat_axS10 : (model 𝒮 N).Satisfies axS10 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_s10 _ _

theorem sat_axS11 : (model 𝒮 N).Satisfies axS11 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_s11 _ _ _

theorem sat_axS12 : (model 𝒮 N).Satisfies axS12 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_s12 _ _ _

theorem sat_axS13 : (model 𝒮 N).Satisfies axS13 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_s13 _ _ _

theorem sat_axNs11 : (model 𝒮 N).Satisfies axNs11 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_ns11 _ _ _

theorem sat_axSn11 : (model 𝒮 N).Satisfies axSn11 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_sn11 _ _ _

theorem sat_dfSex : (model 𝒮 N).Satisfies dfSex :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_dfSex _ _

theorem sat_dfSeq : (model 𝒮 N).Satisfies dfSeq :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_dfSeq _ _ _

theorem sat_axEqS : (model 𝒮 N).Satisfies axEqS :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_eqS _ _

theorem sat_axEqpl1 : (model 𝒮 N).Satisfies axEqpl1 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_eqpl1 _ _ _

theorem sat_axEqpl2 : (model 𝒮 N).Satisfies axEqpl2 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_eqpl2 _ _ _

theorem sat_axEqmu1 : (model 𝒮 N).Satisfies axEqmu1 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_eqmu1 _ _ _

theorem sat_axEqmu2 : (model 𝒮 N).Satisfies axEqmu2 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_eqmu2 _ _ _

theorem sat_axEqlt1 : (model 𝒮 N).Satisfies axEqlt1 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_eqlt1 _ _ _

theorem sat_axEqlt2 : (model 𝒮 N).Satisfies axEqlt2 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_eqlt2 _ _ _

theorem sat_axEqel1 : (model 𝒮 N).Satisfies axEqel1 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_eqel1 _ _ _

theorem sat_axEqel2 : (model 𝒮 N).Satisfies axEqel2 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_eqel2 _ _ _

theorem sat_axS0 : (model 𝒮 N).Satisfies axS0 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_S0 _

theorem sat_axSinj : (model 𝒮 N).Satisfies axSinj :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_Sinj _ _

theorem sat_axPl0 : (model 𝒮 N).Satisfies axPl0 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_pl0 _

theorem sat_axPlS : (model 𝒮 N).Satisfies axPlS :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_plS _ _

theorem sat_axMu0 : (model 𝒮 N).Satisfies axMu0 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_mu0 _

theorem sat_axMuS : (model 𝒮 N).Satisfies axMuS :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_muS _ _

theorem sat_axLt0 : (model 𝒮 N).Satisfies axLt0 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_lt0 _

theorem sat_axLtS : (model 𝒮 N).Satisfies axLtS :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact valid_ltS _ _

theorem sat_axGen : (model 𝒮 N).Satisfies axGen :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ hess _ => by
    obtain ⟨_, h⟩ := valid_of_holds (hess ⟨.turnstile, .var .ph⟩ (by decide))
    z2_values at h
    z2_values
    exact valid_gen _ h

theorem sat_axSgen : (model 𝒮 N).Satisfies axSgen :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ hess _ => by
    obtain ⟨_, h⟩ := valid_of_holds (hess ⟨.turnstile, .var .ph⟩ (by decide))
    z2_values at h
    z2_values
    exact valid_sgen _ h

theorem sat_ax5 : (model 𝒮 N).Satisfies ax5 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ hdv _ _ => by
    z2_values
    exact valid_ax5 (ignores_of_fresh_wff (hdv .x .ph (by decide) (by decide) .nvar .wff _ _))

theorem sat_axS5 : (model 𝒮 N).Satisfies axS5 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ hdv _ _ => by
    z2_values
    exact valid_s5 (ignores_of_fresh_svar_wff (hdv .X .ph (by decide) (by decide) .svar .wff _ _))

theorem sat_axTex : (model 𝒮 N).Satisfies axTex :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ hdv _ _ => by
    z2_values
    exact valid_tex (ignores_of_fresh_term (hdv .x .t (by decide) (by decide) .nvar .term _ _))

end Logic

/-! ## Formula classes -/

section Classes

theorem sat_bndEq : (model 𝒮 N).Satisfies bndEq :=
  satisfies_of_isBnd (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact .eq (Subtype.property _) (Subtype.property _)

theorem sat_bndLt : (model 𝒮 N).Satisfies bndLt :=
  satisfies_of_isBnd (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact .lt (Subtype.property _) (Subtype.property _)

theorem sat_bndEl : (model 𝒮 N).Satisfies bndEl :=
  satisfies_of_isBnd (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact .mem _ (Subtype.property _)

theorem sat_arithEq : (model 𝒮 N).Satisfies arithEq :=
  satisfies_of_isArith (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact .eq (Subtype.property _) (Subtype.property _)

theorem sat_arithLt : (model 𝒮 N).Satisfies arithLt :=
  satisfies_of_isArith (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact .lt (Subtype.property _) (Subtype.property _)

theorem sat_arithEl : (model 𝒮 N).Satisfies arithEl :=
  satisfies_of_isArith (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact .mem _ (Subtype.property _)

theorem sat_arithSeq : (model 𝒮 N).Satisfies arithSeq :=
  satisfies_of_isArith (.of_checkWF (by decide)) rfl fun _ _ _ _ => by
    z2_values
    exact .seq _ _

theorem sat_bndN : (model 𝒮 N).Satisfies bndN :=
  satisfies_of_isBnd (.of_checkWF (by decide)) rfl fun ρ _ hess _ => by
    obtain ⟨_, h⟩ := isBnd_of_holds (hess ⟨.bnd, .var .ph⟩ (by decide))
    z2_values at h
    z2_values
    exact .not h

theorem sat_sig1Bnd : (model 𝒮 N).Satisfies sig1Bnd :=
  satisfies_of_isSig1 (.of_checkWF (by decide)) rfl fun ρ _ hess _ => by
    obtain ⟨_, h⟩ := isBnd_of_holds (hess ⟨.bnd, .var .ph⟩ (by decide))
    z2_values at h
    z2_values
    exact .bnd h

theorem sat_sig1Ex : (model 𝒮 N).Satisfies sig1Ex :=
  satisfies_of_isSig1 (.of_checkWF (by decide)) rfl fun ρ _ hess _ => by
    obtain ⟨_, h⟩ := isBnd_of_holds (hess ⟨.bnd, .var .ph⟩ (by decide))
    z2_values at h
    z2_values
    exact .ex _ h

theorem sat_pi1Bnd : (model 𝒮 N).Satisfies pi1Bnd :=
  satisfies_of_isPi1 (.of_checkWF (by decide)) rfl fun ρ _ hess _ => by
    obtain ⟨_, h⟩ := isBnd_of_holds (hess ⟨.bnd, .var .ph⟩ (by decide))
    z2_values at h
    z2_values
    exact .bnd h

theorem sat_pi1Al : (model 𝒮 N).Satisfies pi1Al :=
  satisfies_of_isPi1 (.of_checkWF (by decide)) rfl fun ρ _ hess _ => by
    obtain ⟨_, h⟩ := isBnd_of_holds (hess ⟨.bnd, .var .ph⟩ (by decide))
    z2_values at h
    z2_values
    exact .all _ h

theorem sat_arithN : (model 𝒮 N).Satisfies arithN :=
  satisfies_of_isArith (.of_checkWF (by decide)) rfl fun ρ _ hess _ => by
    obtain ⟨_, h⟩ := isArith_of_holds (hess ⟨.arith, .var .ph⟩ (by decide))
    z2_values at h
    z2_values
    exact .not h

theorem sat_arithAl : (model 𝒮 N).Satisfies arithAl :=
  satisfies_of_isArith (.of_checkWF (by decide)) rfl fun ρ _ hess _ => by
    obtain ⟨_, h⟩ := isArith_of_holds (hess ⟨.arith, .var .ph⟩ (by decide))
    z2_values at h
    z2_values
    exact .all _ h

theorem sat_arithEx : (model 𝒮 N).Satisfies arithEx :=
  satisfies_of_isArith (.of_checkWF (by decide)) rfl fun ρ _ hess _ => by
    obtain ⟨_, h⟩ := isArith_of_holds (hess ⟨.arith, .var .ph⟩ (by decide))
    z2_values at h
    z2_values
    exact .ex _ h

theorem sat_arithSig1 : (model 𝒮 N).Satisfies arithSig1 :=
  satisfies_of_isArith (.of_checkWF (by decide)) rfl fun ρ _ hess _ => by
    obtain ⟨_, h⟩ := isSig1_of_holds (hess ⟨.sig1, .var .ph⟩ (by decide))
    z2_values at h
    z2_values
    exact h.isArith

theorem sat_arithPi1 : (model 𝒮 N).Satisfies arithPi1 :=
  satisfies_of_isArith (.of_checkWF (by decide)) rfl fun ρ _ hess _ => by
    obtain ⟨_, h⟩ := isPi1_of_holds (hess ⟨.pi1, .var .ph⟩ (by decide))
    z2_values at h
    z2_values
    exact h.isArith

theorem sat_bndI : (model 𝒮 N).Satisfies bndI :=
  satisfies_of_isBnd (.of_checkWF (by decide)) rfl fun ρ _ hess _ => by
    obtain ⟨_, h⟩ := isBnd_of_holds (hess ⟨.bnd, .var .ph⟩ (by decide))
    obtain ⟨_, h'⟩ := isBnd_of_holds (hess ⟨.bnd, .var .ps⟩ (by decide))
    z2_values at h
    z2_values at h'
    z2_values
    exact .imp h h'

theorem sat_bndB : (model 𝒮 N).Satisfies bndB :=
  satisfies_of_isBnd (.of_checkWF (by decide)) rfl fun ρ _ hess _ => by
    obtain ⟨_, h⟩ := isBnd_of_holds (hess ⟨.bnd, .var .ph⟩ (by decide))
    obtain ⟨_, h'⟩ := isBnd_of_holds (hess ⟨.bnd, .var .ps⟩ (by decide))
    z2_values at h
    z2_values at h'
    z2_values
    exact .iff h h'

theorem sat_bndA : (model 𝒮 N).Satisfies bndA :=
  satisfies_of_isBnd (.of_checkWF (by decide)) rfl fun ρ _ hess _ => by
    obtain ⟨_, h⟩ := isBnd_of_holds (hess ⟨.bnd, .var .ph⟩ (by decide))
    obtain ⟨_, h'⟩ := isBnd_of_holds (hess ⟨.bnd, .var .ps⟩ (by decide))
    z2_values at h
    z2_values at h'
    z2_values
    exact .and h h'

theorem sat_arithI : (model 𝒮 N).Satisfies arithI :=
  satisfies_of_isArith (.of_checkWF (by decide)) rfl fun ρ _ hess _ => by
    obtain ⟨_, h⟩ := isArith_of_holds (hess ⟨.arith, .var .ph⟩ (by decide))
    obtain ⟨_, h'⟩ := isArith_of_holds (hess ⟨.arith, .var .ps⟩ (by decide))
    z2_values at h
    z2_values at h'
    z2_values
    exact .imp h h'

theorem sat_arithB : (model 𝒮 N).Satisfies arithB :=
  satisfies_of_isArith (.of_checkWF (by decide)) rfl fun ρ _ hess _ => by
    obtain ⟨_, h⟩ := isArith_of_holds (hess ⟨.arith, .var .ph⟩ (by decide))
    obtain ⟨_, h'⟩ := isArith_of_holds (hess ⟨.arith, .var .ps⟩ (by decide))
    z2_values at h
    z2_values at h'
    z2_values
    exact .iff h h'

theorem sat_arithA : (model 𝒮 N).Satisfies arithA :=
  satisfies_of_isArith (.of_checkWF (by decide)) rfl fun ρ _ hess _ => by
    obtain ⟨_, h⟩ := isArith_of_holds (hess ⟨.arith, .var .ph⟩ (by decide))
    obtain ⟨_, h'⟩ := isArith_of_holds (hess ⟨.arith, .var .ps⟩ (by decide))
    z2_values at h
    z2_values at h'
    z2_values
    exact .and h h'

theorem sat_bndRal : (model 𝒮 N).Satisfies bndRal :=
  satisfies_of_isBnd (.of_checkWF (by decide)) rfl fun ρ hdv hess _ => by
    obtain ⟨_, h⟩ := isBnd_of_holds (hess ⟨.bnd, .var .ph⟩ (by decide))
    z2_values at h
    z2_values
    exact .ball _ (Subtype.property _)
      (ignores_of_fresh_term (hdv .x .t (by decide) (by decide) .nvar .term _ _)) h

theorem sat_bndRex : (model 𝒮 N).Satisfies bndRex :=
  satisfies_of_isBnd (.of_checkWF (by decide)) rfl fun ρ hdv hess _ => by
    obtain ⟨_, h⟩ := isBnd_of_holds (hess ⟨.bnd, .var .ph⟩ (by decide))
    z2_values at h
    z2_values
    exact .bex _ (Subtype.property _)
      (ignores_of_fresh_term (hdv .x .t (by decide) (by decide) .nvar .term _ _)) h

end Classes

theorem isModel_base : (model 𝒮 N).IsModel base := by
  have h₁ : logicList.Forall (model 𝒮 N).Satisfies :=
    ⟨sat_axMp, sat_ax1, sat_ax2, sat_ax3, sat_dfBi1, sat_dfBi2, sat_dfBi3, sat_dfAn, sat_axGen,
      sat_ax4, sat_ax5, sat_ax6, sat_ax7, sat_ax10, sat_ax11, sat_ax12, sat_ax13, sat_axTex,
      sat_dfEx, sat_axSgen, sat_axS4, sat_axS5, sat_axS6, sat_axS7, sat_axS10, sat_axS11,
      sat_axS12, sat_axS13, sat_axNs11, sat_axSn11, sat_dfSex, sat_dfSeq, sat_axEqS,
      sat_axEqpl1, sat_axEqpl2, sat_axEqmu1, sat_axEqmu2, sat_axEqlt1, sat_axEqlt2, sat_axEqel1,
      sat_axEqel2⟩
  have h₂ : basicList.Forall (model 𝒮 N).Satisfies :=
    ⟨sat_axS0, sat_axSinj, sat_axPl0, sat_axPlS, sat_axMu0, sat_axMuS, sat_axLt0, sat_axLtS⟩
  have h₃ : classList.Forall (model 𝒮 N).Satisfies :=
    ⟨sat_bndEq, sat_bndLt, sat_bndEl, sat_bndN, sat_bndI, sat_bndB, sat_bndA, sat_bndRal,
      sat_bndRex, sat_sig1Bnd, sat_sig1Ex, sat_pi1Bnd, sat_pi1Al, sat_arithEq, sat_arithLt,
      sat_arithEl, sat_arithSeq, sat_arithN, sat_arithAl, sat_arithEx, sat_arithI, sat_arithB,
      sat_arithA, sat_arithSig1, sat_arithPi1⟩
  intro B hB
  simp only [base, Set.mem_ofPred_eq, List.mem_append] at hB
  rcases hB with (hB | hB) | hB
  exacts [List.forall_iff_forall_mem.1 h₁ B hB, List.forall_iff_forall_mem.1 h₂ B hB,
    List.forall_iff_forall_mem.1 h₃ B hB]

/-! ## Induction -/

/-- Full induction holds in every ω-model. -/
theorem sat_axInd : (model 𝒮 N).Satisfies axInd :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ hdv _ _ => by
    z2_values
    exact valid_ind (ne_of_fresh (hdv .x .y (by decide) (by decide) .nvar .nvar _ _))
      (ignores_of_fresh_wff (hdv .y .ph (by decide) (by decide) .nvar .wff _ _))

/-- Σ⁰₁-induction holds in every ω-model. -/
theorem sat_axIndSig1 : (model 𝒮 N).Satisfies axIndSig1 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ hdv _ _ => by
    z2_values
    exact valid_ind (ne_of_fresh (hdv .x .y (by decide) (by decide) .nvar .nvar _ _))
      (ignores_of_fresh_wff (hdv .y .ph (by decide) (by decide) .nvar .wff _ _))

/-! ## Comprehension -/

variable (𝒮 N) in
/-- `𝒮` contains every set defined by a formula of the class `P`, with number
and set parameters. -/
def ComprehensionClosed (P : (Env 𝒮 N → Prop) → Prop) : Prop :=
  ∀ φ, P φ → ∀ (x : N) (ρ : Env 𝒮 N), {n : ℕ | φ (update ρ (.inl x) n)} ∈ 𝒮

variable (𝒮 N) in
/-- `𝒮` contains every set defined by a Σ⁰₁ formula that is equivalent to a
Π⁰₁ formula. -/
def Delta1Closed : Prop :=
  ∀ φ ψ, IsSig1 φ → IsPi1 ψ → ∀ (x : N) (ρ : Env 𝒮 N),
    (∀ n : ℕ, φ (update ρ (.inl x) n) ↔ ψ (update ρ (.inl x) n)) →
    {n : ℕ | φ (update ρ (.inl x) n)} ∈ 𝒮

variable (𝒮 N) in
/-- `𝒮` separates any two disjoint sets defined by Σ⁰₁ formulas. -/
def SeparationClosed : Prop :=
  ∀ φ ψ, IsSig1 φ → IsSig1 ψ → ∀ (x : N) (ρ : Env 𝒮 N),
    (∀ n : ℕ, ¬ (φ (update ρ (.inl x) n) ∧ ψ (update ρ (.inl x) n))) →
    ∃ A ∈ 𝒮, ∀ n : ℕ, (φ (update ρ (.inl x) n) → n ∈ A) ∧ (ψ (update ρ (.inl x) n) → n ∉ A)

omit [Infinite N] in
theorem ComprehensionClosed.mono {P Q : (Env 𝒮 N → Prop) → Prop} (hPQ : ∀ φ, P φ → Q φ)
    (h : ComprehensionClosed 𝒮 N Q) : ComprehensionClosed 𝒮 N P :=
  fun φ hφ => h φ (hPQ φ hφ)

omit [Infinite N] in
/-- Arithmetical comprehension gives Δ⁰₁-comprehension. -/
theorem ComprehensionClosed.delta1Closed (h : ComprehensionClosed 𝒮 N IsArith) :
    Delta1Closed 𝒮 N :=
  fun φ _ hφ _ x ρ _ => h φ hφ.isArith x ρ

omit [Infinite N] in
/-- Arithmetical comprehension gives Σ⁰₁ separation. -/
theorem ComprehensionClosed.separationClosed (h : ComprehensionClosed 𝒮 N IsArith) :
    SeparationClosed 𝒮 N :=
  fun φ _ hφ _ x ρ hd => ⟨_, h φ hφ.isArith x ρ, fun n => ⟨id, fun hψ hφ' => hd n ⟨hφ', hψ⟩⟩⟩

omit [Infinite N] in
/-- The full second-order part is closed under every comprehension. -/
theorem comprehensionClosed_univ (P : (Env Set.univ N → Prop) → Prop) :
    ComprehensionClosed Set.univ N P :=
  fun _ _ _ _ => trivial

theorem sat_axComp (h : ComprehensionClosed 𝒮 N IsDef) : (model 𝒮 N).Satisfies axComp :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ hdv _ _ => by
    z2_values
    exact valid_comp (ignores_of_fresh_svar_wff (hdv .X .ph (by decide) (by decide) .svar .wff _ _))
      (h _ (Subtype.property _) _)

theorem sat_axAcomp (h : ComprehensionClosed 𝒮 N IsArith) : (model 𝒮 N).Satisfies axAcomp :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ hdv hess _ => by
    obtain ⟨_, hφ⟩ := isArith_of_holds (hess ⟨.arith, .var .ph⟩ (by decide))
    z2_values at hφ
    z2_values
    exact valid_comp (ignores_of_fresh_svar_wff (hdv .X .ph (by decide) (by decide) .svar .wff _ _))
      (h _ hφ _)

theorem sat_axDcomp (h : Delta1Closed 𝒮 N) : (model 𝒮 N).Satisfies axDcomp :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ hdv hess _ => by
    obtain ⟨_, hφ⟩ := isSig1_of_holds (hess ⟨.sig1, .var .ph⟩ (by decide))
    obtain ⟨_, hψ⟩ := isPi1_of_holds (hess ⟨.pi1, .var .ps⟩ (by decide))
    z2_values at hφ
    z2_values at hψ
    z2_values
    exact valid_dcomp
      (ignores_of_fresh_svar_wff (hdv .X .ph (by decide) (by decide) .svar .wff _ _))
      (h _ _ hφ hψ _)

theorem sat_axSep1 (h : SeparationClosed 𝒮 N) : (model 𝒮 N).Satisfies axSep1 :=
  satisfies_of_valid (.of_checkWF (by decide)) rfl fun _ hdv hess _ => by
    obtain ⟨_, hφ⟩ := isSig1_of_holds (hess ⟨.sig1, .var .ph⟩ (by decide))
    obtain ⟨_, hψ⟩ := isSig1_of_holds (hess ⟨.sig1, .var .ps⟩ (by decide))
    z2_values at hφ
    z2_values at hψ
    z2_values
    exact valid_sep
      (ignores_of_fresh_svar_wff (hdv .X .ph (by decide) (by decide) .svar .wff _ _))
      (ignores_of_fresh_svar_wff (hdv .X .ps (by decide) (by decide) .svar .wff _ _))
      (h _ _ hφ hψ _)

/-! ## Models of the subsystems -/

/-- An ω-model closed under Δ⁰₁-comprehension is a model of `RCA0`. -/
theorem isModel_RCA0 (h : Delta1Closed 𝒮 N) : (model 𝒮 N).IsModel RCA0 := by
  rintro B (hB | rfl | rfl)
  exacts [isModel_base B hB, sat_axIndSig1, sat_axDcomp h]

/-- An ω-model closed under Δ⁰₁-comprehension and Σ⁰₁ separation is a model of
`WKL0`. -/
theorem isModel_WKL0 (h : Delta1Closed 𝒮 N) (h' : SeparationClosed 𝒮 N) :
    (model 𝒮 N).IsModel WKL0 := by
  rintro B (hB | rfl)
  exacts [isModel_RCA0 h B hB, sat_axSep1 h']

/-- An ω-model closed under arithmetical comprehension is a model of `ACA0`. -/
theorem isModel_ACA0 (h : ComprehensionClosed 𝒮 N IsArith) : (model 𝒮 N).IsModel ACA0 := by
  rintro B (hB | rfl | rfl)
  exacts [isModel_base B hB, sat_axIndSig1, sat_axAcomp h]

/-- An ω-model closed under comprehension for all formulas is a model of `Z2`. -/
theorem isModel_Z2 (h : ComprehensionClosed 𝒮 N IsDef) : (model 𝒮 N).IsModel Z2 := by
  rintro B (hB | rfl | rfl)
  exacts [isModel_ACA0 (h.mono fun _ hφ => hφ.isDef) B hB, sat_axInd, sat_axComp h]

/-- An ω-model closed under comprehension for all formulas satisfies all
axioms of `z2.mm`. -/
theorem isModel_allAxioms (h : ComprehensionClosed 𝒮 N IsDef) :
    (model 𝒮 N).IsModel allAxioms := by
  have ha : ComprehensionClosed 𝒮 N IsArith := h.mono fun _ hφ => hφ.isDef
  intro B hB
  simp only [allAxioms, Set.mem_ofPred_eq, axiomList_eq] at hB
  rcases List.mem_append.1 hB with hB | hB
  · exact isModel_base B hB
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [sat_axIndSig1, sat_axDcomp ha.delta1Closed, sat_axSep1 ha.separationClosed,
      sat_axAcomp ha, sat_axInd, sat_axComp h]

/-- The full model satisfies every axiom of `z2.mm`. -/
theorem isModel_full : (fullModel N).IsModel allAxioms :=
  isModel_allAxioms (comprehensionClosed_univ _)

end Silmaril.Logic.Metamath.SecondOrder
