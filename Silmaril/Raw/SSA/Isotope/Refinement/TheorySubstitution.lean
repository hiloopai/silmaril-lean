module

public import Silmaril.Raw.SSA.Isotope.Refinement.Structural
public import Silmaril.Raw.SSA.Isotope.Refinement.SubstitutionStructural

/-! # Pure substitution in the written directed theory

The primitive rewrite family must be stable under native renaming and native
pure substitutions. Binder normalization is handled by the derived admissible
substitution presentation, without adding rules to the written judgments.
-/

@[expose] public section

noncomputable section

namespace Silmaril.Isotope.Refinement

universe u v w

open LetIter.LocallyNameless (Tm)

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {n m : Nat} {Δ : QCtx τ n} {Γ : QCtx τ m}
variable {a b : Term Φ n} {A : τ} {σ : Fin n → Term Φ m}

def Substitution.Admissible.pureTyping (hσ : Admissible F Γ (⊥ : ε) σ Δ)
    {e : ε} (h : HasType F Δ e a A) : HasType F Γ e (Tm.bsubst σ a) A :=
  (hσ.effectMono bot_le).typing h

theorem WellTyped.bsubstAdmissible (h : WellTyped (ε := ε) F Δ a A)
    (hσ : Substitution.Admissible F Γ (⊥ : ε) σ Δ) :
    WellTyped (ε := ε) F Γ (Tm.bsubst σ a) A := by
  obtain ⟨h⟩ := h
  exact ⟨hσ.pureTyping h⟩

theorem EquationAxiom.bsubstAdmissible (h : EquationAxiom (ε := ε) F Δ a b A)
    (hσ : Substitution.Admissible F Γ (⊥ : ε) σ Δ) :
    EquationAxiom (ε := ε) F Γ (Tm.bsubst σ a) (Tm.bsubst σ b) A := by
  cases h with
  | letOp s hf ha hc =>
    obtain ⟨Γl, Γr, hs, hl, hr, _⟩ := hσ.split s
    simpa [Tm.bsubst, Tm.upSub] using
      EquationAxiom.letOp hs hf (hr.pureTyping ha) ((hl.up _).pureTyping hc)
  | letLet so si ha hb hc =>
    obtain ⟨Γc, Γr, hso, hcS, hrS, _⟩ := hσ.split so
    obtain ⟨Γl, Γm, hsi, hlS, hmS, _⟩ := hcS.split si
    simpa [Tm.bsubst, Tm.upSub] using EquationAxiom.letLet hso hsi
      (hrS.pureTyping ha) ((hmS.up _).pureTyping hb) ((hlS.up _).pureTyping hc)
  | letLetPair so si ha hc hd =>
    obtain ⟨Γc, Γr, hso, hcS, hrS, _⟩ := hσ.split so
    obtain ⟨Γl, Γm, hsi, hlS, hmS, _⟩ := hcS.split si
    simpa [Tm.bsubst, Tm.upSub] using EquationAxiom.letLetPair hso hsi
      (hrS.pureTyping ha) (((hmS.up _).up _).pureTyping hc) ((hlS.up _).pureTyping hd)
  | letCase f so si ha hl hr hd =>
    obtain ⟨Γc, Γr, hso, hcS, hrS, _⟩ := hσ.split so
    obtain ⟨Γl, Γm, hsi, hlS, hmS, _⟩ := hcS.split si
    simpa [Tm.bsubst, Tm.upSub] using EquationAxiom.letCase f hso hsi
      (hmS.pureTyping ha) ((hlS.up _).pureTyping hl)
      ((hlS.up _).pureTyping hr) ((hrS.up _).pureTyping hd)
  | pairBind s ha hc =>
    obtain ⟨Γl, Γr, hs, hl, hr, _⟩ := hσ.split s
    simpa [Tm.bsubst, Tm.upSub] using EquationAxiom.pairBind hs (hr.pureTyping ha)
      (((hl.up _).up _).pureTyping hc)
  | caseBind f s ha hl hr =>
    obtain ⟨Γl, Γr, hs, hlS, hrS, _⟩ := hσ.split s
    simpa [Tm.bsubst, Tm.upSub] using EquationAxiom.caseBind f hs (hrS.pureTyping ha)
      ((hlS.up _).pureTyping hl) ((hlS.up _).pureTyping hr)
  | iterBind f s hu hi ha hb =>
    obtain ⟨Γl, Γr, hs, hl, hr, hlin⟩ := hσ.split s
    simpa [Tm.bsubst, Tm.upSub] using EquationAxiom.iterBind f hs (top_le_iff.mp (hu ▸ hlin)) hi
      (hr.pureTyping ha) ((hl.up _).pureTyping hb)
  | term ha => simpa [Tm.bsubst, Tm.upSub] using EquationAxiom.term (hσ.pureTyping ha)
  | initial f s ha hb hc =>
    obtain ⟨Γl, Γr, hs, hl, hr, _⟩ := hσ.split s
    simpa [Tm.bsubst, Tm.upSub] using EquationAxiom.initial f hs (hr.pureTyping ha)
      ((hl.up _).pureTyping hb) ((hl.up _).pureTyping hc)
  | pairEta ha =>
    have h1 : Tm.upSub (Tm.upSub σ) (1 : Fin (n + 2)) = .bv 1 := by
      change Tm.lift (Tm.upSub σ 0) = .bv 1
      rfl
    have h0 : Tm.upSub (Tm.upSub σ) 0 = .bv 0 := rfl
    simpa only [Tm.bsubst, h1, h0] using EquationAxiom.pairEta (hσ.pureTyping ha)
  | pairBeta so si ha hb hc =>
    obtain ⟨Γl, Γr, hso, hlS, hrS, _⟩ := hσ.split so
    obtain ⟨Γa, Γb, hsi, haS, hbS, _⟩ := hlS.split si
    simpa [Tm.bsubst, Tm.upSub] using EquationAxiom.pairBeta hso hsi
      (haS.pureTyping ha) (hbS.pureTyping hb) (((hrS.up _).up _).pureTyping hc)
  | caseBetaL f s ha hl hr =>
    obtain ⟨Γl, Γr, hs, hlS, hrS, _⟩ := hσ.split s
    simpa [Tm.bsubst, Tm.upSub] using EquationAxiom.caseBetaL f hs (hrS.pureTyping ha)
      ((hlS.up _).pureTyping hl) ((hlS.up _).pureTyping hr)
  | caseBetaR f s ha hl hr =>
    obtain ⟨Γl, Γr, hs, hlS, hrS, _⟩ := hσ.split s
    simpa [Tm.bsubst, Tm.upSub] using EquationAxiom.caseBetaR f hs (hrS.pureTyping ha)
      ((hlS.up _).pureTyping hl) ((hlS.up _).pureTyping hr)
  | caseEta f ha =>
    simpa [Tm.bsubst, Tm.upSub] using EquationAxiom.caseEta f (hσ.pureTyping ha)
  | fixpoint f s hu hi ha hb =>
    obtain ⟨Γl, Γr, hs, hl, hr, hlin⟩ := hσ.split s
    simpa [Tm.bsubst, Tm.upSub] using EquationAxiom.fixpoint f hs (top_le_iff.mp (hu ▸ hlin)) hi
      (hr.pureTyping ha) ((hl.up _).pureTyping hb)
  | naturality f so si hul hum ha hb hc =>
    obtain ⟨Γl, Γc, hso, hlS, hcS, hlinl⟩ := hσ.split so
    obtain ⟨Γm, Γr, hsi, hmS, hrS, hlinm⟩ := hcS.split si
    simpa [Tm.bsubst, Tm.upSub] using EquationAxiom.naturality f hso hsi
      (top_le_iff.mp (hul ▸ hlinl)) (top_le_iff.mp (hum ▸ hlinm))
      (hrS.pureTyping ha) ((hmS.up _).pureTyping hb) ((hlS.up _).pureTyping hc)
  | codiagonal f s hu hi ha hb =>
    obtain ⟨Γl, Γr, hs, hl, hr, hlin⟩ := hσ.split s
    simpa [Tm.bsubst, Tm.upSub] using EquationAxiom.codiagonal f hs (top_le_iff.mp (hu ▸ hlin)) hi
      (hr.pureTyping ha) ((hl.up _).pureTyping hb)

theorem DirectionalAxiom.bsubstAdmissible {p : Polarity}
    (h : DirectionalAxiom (ε := ε) F p Δ a b A)
    (hσ : Substitution.Admissible F Γ (⊥ : ε) σ Δ) :
    DirectionalAxiom (ε := ε) F p Γ (Tm.bsubst σ a) (Tm.bsubst σ b) A := by
  cases h with
  | eliminate s ha hd hb =>
    obtain ⟨Γl, hs, hl, _⟩ := hσ.selfSplit s
    simpa [Tm.bsubst, Tm.upSub] using DirectionalAxiom.eliminate hs
      (hl.pureTyping ha) hd (hσ.pureTyping hb)
  | beta s ha hb hd hm hq =>
    obtain ⟨Γl, Γr, hs, hl, hr, hlin⟩ := hσ.split s
    have hq' := hq.trans (show Usage.used _ ≤ Usage.used _ from inf_le_inf hlin le_rfl)
    simpa [Tm.bsubst, Tm.upSub] using DirectionalAxiom.beta hs (hl.pureTyping ha)
      ((hr.up _ _).pureTyping hb) ((hr.up _).pureTyping hd) hm hq'

theorem UniformityRule.bsubstAdmissible {p : Polarity} {k : Nat} {Ξ : QCtx τ k}
    {c d : Term Φ k} {B : τ} {σ : Fin k → Term Φ m}
    (h : UniformityRule (ε := ε) F p Δ a b A Ξ c d B)
    (hσ : Substitution.Admissible F Γ (⊥ : ε) σ Ξ) :
    ∃ (l : Nat) (Θ : QCtx τ l) (κ : Fin n → Term Φ l),
      Substitution.Admissible F Θ (⊥ : ε) κ Δ ∧
      UniformityRule (ε := ε) F p Θ (Tm.bsubst κ a) (Tm.bsubst κ b) A
        Γ (Tm.bsubst σ c) (Tm.bsubst σ d) B := by
  cases h with
  | square f so si hu hi ha hs hb hb' hc hm =>
    obtain ⟨Γc, Γr, hso, hcS, hrS, _⟩ := hσ.split so
    obtain ⟨Γl, hsi, hlS, hlin⟩ := hcS.selfSplit si
    refine ⟨m + 1, Γc.snoc _, Tm.upSub σ, hcS.up _, ?_⟩
    simpa [Tm.bsubst, Tm.upSub] using UniformityRule.square f hso hsi
      (top_le_iff.mp (hu ▸ hlin)) hi (hrS.pureTyping ha)
      ((hcS.up _).pureTyping hs) ((hlS.up _).pureTyping hb)
      ((hlS.up _).pureTyping hb') ((hcS.up _).pureTyping hc) hm

/-- Stability under precisely the native pure substitutions of the paper. -/
def Relation.PureSubstitutionClosed (F : Fragment) (R : Relation τ Φ) : Prop :=
  ∀ {n m : Nat} {Δ : QCtx τ n} {Γ : QCtx τ m} {a b : Term Φ n} {A : τ}
    {σ : Fin n → Term Φ m}, Substitution F Γ (⊥ : ε) σ Δ → R Δ a b A →
      R Γ (Tm.bsubst σ a) (Tm.bsubst σ b) A

theorem Relation.PureSubstitutionClosed.admissible {R : Relation τ Φ}
    (hS : Relation.PureSubstitutionClosed (ε := ε) F R) (hR : R.RenamingClosed)
    (hσ : Substitution.Admissible F Γ (⊥ : ε) σ Δ) (h : R Δ a b A) :
    R Γ (Tm.bsubst σ a) (Tm.bsubst σ b) A := by
  obtain ⟨Θ, hw, ⟨hs⟩⟩ := hσ
  have h' := hR id hw h
  rw [show Tm.rename id a = a from Tm.rename_id a,
    show Tm.rename id b = b from Tm.rename_id b] at h'
  exact hS hs h'

namespace Polarity

@[simp] theorem source_bsubst (p : Polarity) (σ : Fin n → Term Φ m) (a b : Term Φ n) :
    p.source (Tm.bsubst σ a) (Tm.bsubst σ b) = Tm.bsubst σ (p.source a b) := by
  cases p <;> rfl

@[simp] theorem target_bsubst (p : Polarity) (σ : Fin n → Term Φ m) (a b : Term Φ n) :
    p.target (Tm.bsubst σ a) (Tm.bsubst σ b) = Tm.bsubst σ (p.target a b) := by
  cases p <;> rfl

end Polarity

/-- Admissible pure substitutions act on the entire generated directed theory,
including the recursive uniformity premise and both polarity orientations. -/
theorem Refines.bsubstAdmissible {R : Relation τ Φ}
    (h : Refines (ε := ε) F R Δ a b A)
    (hσ : Substitution.Admissible F Γ (⊥ : ε) σ Δ)
    (hR : R.RenamingClosed) (hS : Relation.PureSubstitutionClosed (ε := ε) F R) :
    Refines (ε := ε) F R Γ (Tm.bsubst σ a) (Tm.bsubst σ b) A := by
  induction h generalizing m with
  | base h ha hb =>
    exact .base (hS.admissible hR hσ h) (ha.bsubstAdmissible hσ) (hb.bsubstAdmissible hσ)
  | refl h => exact .refl (h.bsubstAdmissible hσ)
  | trans _ _ ih ik => exact .trans (ih hσ) (ik hσ)
  | equation p h ha hb =>
    simpa only [Polarity.source_bsubst, Polarity.target_bsubst] using
      Refines.equation p (h.bsubstAdmissible hσ)
        (ha.bsubstAdmissible hσ) (hb.bsubstAdmissible hσ)
  | directional p h ha hb =>
    simpa only [Polarity.source_bsubst, Polarity.target_bsubst] using
      Refines.directional p (h.bsubstAdmissible hσ)
        (ha.bsubstAdmissible hσ) (hb.bsubstAdmissible hσ)
  | uniformity p r hc hd _ ih =>
    obtain ⟨l, Θ, κ, hk, r'⟩ := r.bsubstAdmissible hσ
    apply (by simpa only [Polarity.source_bsubst, Polarity.target_bsubst] using
      Refines.uniformity (R := R) p r' (hc.bsubstAdmissible hσ) (hd.bsubstAdmissible hσ))
    simpa only [Polarity.source_bsubst, Polarity.target_bsubst] using ih hk
  | op _ ih => exact .op (ih hσ)
  | let₁ s _ _ ih ik =>
    obtain ⟨Γl, Γr, hs, hl, hr, _⟩ := hσ.split s
    exact .let₁ hs (ih hr) (ik (hl.up _))
  | pair s _ _ ih ik =>
    obtain ⟨Γl, Γr, hs, hl, hr, _⟩ := hσ.split s
    exact .pair hs (ih hl) (ik hr)
  | let₂ s _ _ ih ik =>
    obtain ⟨Γl, Γr, hs, hl, hr, _⟩ := hσ.split s
    exact .let₂ hs (ih hr) (ik ((hl.up _).up _))
  | inl f _ ih => exact .inl f (ih hσ)
  | inr f _ ih => exact .inr f (ih hσ)
  | case f s _ _ _ ih il ir =>
    obtain ⟨Γl, Γr, hs, hl, hr, _⟩ := hσ.split s
    exact .case f hs (ih hr) (il (hl.up _)) (ir (hl.up _))
  | abort f _ ih => exact .abort f (ih hσ)
  | iter f s hu _ _ ih ik =>
    obtain ⟨Γl, Γr, hs, hl, hr, hlin⟩ := hσ.split s
    exact .iter f hs (top_le_iff.mp (hu ▸ hlin)) (ih hr) (ik (hl.up _))

/-- Native pure substitution closure is a theorem of the generated calculus. -/
theorem Refines.bsubst {R : Relation τ Φ} (h : Refines (ε := ε) F R Δ a b A)
    (hσ : Substitution F Γ (⊥ : ε) σ Δ)
    (hR : R.RenamingClosed) (hS : Relation.PureSubstitutionClosed (ε := ε) F R) :
    Refines (ε := ε) F R Γ (Tm.bsubst σ a) (Tm.bsubst σ b) A :=
  h.bsubstAdmissible hσ.admissible hR hS

theorem Equates.bsubst {R : Relation τ Φ} (h : Equates (ε := ε) F R Δ a b A)
    (hσ : Substitution F Γ (⊥ : ε) σ Δ)
    (hR : R.RenamingClosed) (hS : Relation.PureSubstitutionClosed (ε := ε) F R) :
    Equates (ε := ε) F R Γ (Tm.bsubst σ a) (Tm.bsubst σ b) A :=
  ⟨h.1.bsubst hσ hR hS, h.2.bsubst hσ hR hS⟩

/-- Closing a structurally stable primitive relation preserves its native
pure-substitution stability. -/
theorem Relation.PureSubstitutionClosed.refines {R : Relation τ Φ}
    (hS : Relation.PureSubstitutionClosed (ε := ε) F R) (hR : R.RenamingClosed) :
    Relation.PureSubstitutionClosed (ε := ε) F (Refines (ε := ε) F R) :=
  fun hσ h => h.bsubst hσ hR hS

end Silmaril.Isotope.Refinement
