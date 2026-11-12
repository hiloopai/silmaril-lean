module

public import Silmaril.Raw.SSA.Isotope.Refinement.Derivation
public import Silmaril.Raw.SSA.Isotope.Refinement.ContextSplitting

@[expose] public section

noncomputable section

namespace Silmaril.Isotope.Refinement

universe u v w

open LetIter.LocallyNameless (Tm)

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]

variable {F : Fragment} {n m : Nat} {Γ : QCtx τ n} {Θ : QCtx τ m}
variable {a b : Term Φ n} {A : τ} {ρ : Fin n → Fin m}

theorem WellTyped.rename (h : WellTyped (ε := ε) F Γ a A) (hw : QCtx.Weakening Θ Γ ρ) :
    WellTyped (ε := ε) F Θ (Tm.rename ρ a) A := by
  obtain ⟨h⟩ := h
  exact ⟨h.rename ρ hw⟩

/-- Primitive equations preserve all quantitative and effect guards under
native context weakening. -/
theorem EquationAxiom.rename (h : EquationAxiom (ε := ε) F Γ a b A)
    (hw : QCtx.Weakening Θ Γ ρ) :
    EquationAxiom (ε := ε) F Θ (Tm.rename ρ a) (Tm.rename ρ b) A := by
  cases h with
  | letOp s hf ha hc =>
    obtain ⟨Θl, Θr, hs, hl, hr, _⟩ := hw.split s
    simpa [Tm.rename, Tm.up] using
      EquationAxiom.letOp hs hf (ha.rename ρ hr) (hc.rename (Tm.up ρ) (hl.up _))
  | letLet so si ha hb hc =>
    obtain ⟨Θc, Θr, hso, hcW, hrW, _⟩ := hw.split so
    obtain ⟨Θl, Θm, hsi, hlW, hmW, _⟩ := hcW.split si
    simpa [Tm.rename, Tm.up] using EquationAxiom.letLet hso hsi
      (ha.rename ρ hrW) (hb.rename (Tm.up ρ) (hmW.up _)) (hc.rename (Tm.up ρ) (hlW.up _))
  | letLetPair so si ha hc hd =>
    obtain ⟨Θc, Θr, hso, hcW, hrW, _⟩ := hw.split so
    obtain ⟨Θl, Θm, hsi, hlW, hmW, _⟩ := hcW.split si
    simpa [Tm.rename, Tm.up] using EquationAxiom.letLetPair hso hsi
      (ha.rename ρ hrW) (hc.rename (Tm.up (Tm.up ρ)) ((hmW.up _).up _))
      (hd.rename (Tm.up ρ) (hlW.up _))
  | letCase f so si ha hl hr hd =>
    obtain ⟨Θc, Θr, hso, hcW, hrW, _⟩ := hw.split so
    obtain ⟨Θl, Θm, hsi, hlW, hmW, _⟩ := hcW.split si
    simpa [Tm.rename, Tm.up] using EquationAxiom.letCase f hso hsi
      (ha.rename ρ hmW) (hl.rename (Tm.up ρ) (hlW.up _))
      (hr.rename (Tm.up ρ) (hlW.up _)) (hd.rename (Tm.up ρ) (hrW.up _))
  | pairBind s ha hc =>
    obtain ⟨Θl, Θr, hs, hl, hr, _⟩ := hw.split s
    simpa [Tm.rename, Tm.up] using EquationAxiom.pairBind hs (ha.rename ρ hr)
      (hc.rename (Tm.up (Tm.up ρ)) ((hl.up _).up _))
  | caseBind f s ha hl hr =>
    obtain ⟨Θl, Θr, hs, hlW, hrW, _⟩ := hw.split s
    simpa [Tm.rename, Tm.up] using EquationAxiom.caseBind f hs (ha.rename ρ hrW)
      (hl.rename (Tm.up ρ) (hlW.up _)) (hr.rename (Tm.up ρ) (hlW.up _))
  | iterBind f s hu hi ha hb =>
    obtain ⟨Θl, Θr, hs, hl, hr, ht⟩ := hw.split s
    simpa [Tm.rename, Tm.up] using EquationAxiom.iterBind f hs (ht hu) hi
      (ha.rename ρ hr) (hb.rename (Tm.up ρ) (hl.up _))
  | term ha => simpa [Tm.rename, Tm.up] using EquationAxiom.term (ha.rename ρ hw)
  | initial f s ha hb hc =>
    obtain ⟨Θl, Θr, hs, hl, hr, _⟩ := hw.split s
    simpa [Tm.rename, Tm.up] using EquationAxiom.initial f hs (ha.rename ρ hr)
      (hb.rename (Tm.up ρ) (hl.up _)) (hc.rename (Tm.up ρ) (hl.up _))
  | pairEta ha =>
    have h1 : Tm.up (Tm.up ρ) (1 : Fin (n + 2)) = 1 := by
      change Fin.succ (Tm.up ρ 0) = 1
      rfl
    have h0 : Tm.up (Tm.up ρ) 0 = 0 := rfl
    simpa only [Tm.rename, h1, h0] using EquationAxiom.pairEta (ha.rename ρ hw)
  | pairBeta so si ha hb hc =>
    obtain ⟨Θl, Θr, hso, hlW, hrW, _⟩ := hw.split so
    obtain ⟨Θa, Θb, hsi, haW, hbW, _⟩ := hlW.split si
    simpa [Tm.rename, Tm.up] using EquationAxiom.pairBeta hso hsi
      (ha.rename ρ haW) (hb.rename ρ hbW) (hc.rename (Tm.up (Tm.up ρ)) ((hrW.up _).up _))
  | caseBetaL f s ha hl hr =>
    obtain ⟨Θl, Θr, hs, hlW, hrW, _⟩ := hw.split s
    simpa [Tm.rename, Tm.up] using EquationAxiom.caseBetaL f hs (ha.rename ρ hrW)
      (hl.rename (Tm.up ρ) (hlW.up _)) (hr.rename (Tm.up ρ) (hlW.up _))
  | caseBetaR f s ha hl hr =>
    obtain ⟨Θl, Θr, hs, hlW, hrW, _⟩ := hw.split s
    simpa [Tm.rename, Tm.up] using EquationAxiom.caseBetaR f hs (ha.rename ρ hrW)
      (hl.rename (Tm.up ρ) (hlW.up _)) (hr.rename (Tm.up ρ) (hlW.up _))
  | caseEta f ha => simpa [Tm.rename, Tm.up] using EquationAxiom.caseEta f (ha.rename ρ hw)
  | fixpoint f s hu hi ha hb =>
    obtain ⟨Θl, Θr, hs, hl, hr, ht⟩ := hw.split s
    simpa [Tm.rename, Tm.up] using EquationAxiom.fixpoint f hs (ht hu) hi
      (ha.rename ρ hr) (hb.rename (Tm.up ρ) (hl.up _))
  | naturality f so si hul hum ha hb hc =>
    obtain ⟨Θl, Θc, hso, hlW, hcW, htl⟩ := hw.split so
    obtain ⟨Θm, Θr, hsi, hmW, hrW, htm⟩ := hcW.split si
    simpa [Tm.rename, Tm.up] using EquationAxiom.naturality f hso hsi (htl hul) (htm hum)
      (ha.rename ρ hrW) (hb.rename (Tm.up ρ) (hmW.up _)) (hc.rename (Tm.up ρ) (hlW.up _))
  | codiagonal f s hu hi ha hb =>
    obtain ⟨Θl, Θr, hs, hl, hr, ht⟩ := hw.split s
    simpa [Tm.rename, Tm.up] using EquationAxiom.codiagonal f hs (ht hu) hi
      (ha.rename ρ hr) (hb.rename (Tm.up ρ) (hl.up _))

theorem DirectionalAxiom.rename {p : Polarity} (h : DirectionalAxiom (ε := ε) F p Γ a b A)
    (hw : QCtx.Weakening Θ Γ ρ) :
    DirectionalAxiom (ε := ε) F p Θ (Tm.rename ρ a) (Tm.rename ρ b) A := by
  cases h with
  | eliminate s ha hd hb =>
    obtain ⟨Θl, hs, hl, _⟩ := hw.selfSplit s
    simpa [Tm.rename, Tm.up] using DirectionalAxiom.eliminate hs (ha.rename ρ hl) hd (hb.rename ρ hw)
  | beta s ha hb hd hm hq =>
    obtain ⟨Θl, Θr, hs, hl, hr, hlin⟩ := hw.split_linearity s
    have hq' := hq.trans (show Usage.used _ ≤ Usage.used _ from inf_le_inf hlin le_rfl)
    simpa [Tm.rename, Tm.up] using DirectionalAxiom.beta hs (ha.rename ρ hl)
      (hb.rename (Tm.up ρ) (hr.up _ _)) (hd.rename (Tm.up ρ) (hr.up _)) hm hq'

/-- Weakening a uniformity conclusion determines a weakened commuting square. -/
theorem UniformityRule.rename {p : Polarity} {k : Nat} {Δ : QCtx τ k}
    {c d : Term Φ k} {B : τ} {ρ : Fin k → Fin m}
    (h : UniformityRule (ε := ε) F p Γ a b A Δ c d B) (hw : QCtx.Weakening Θ Δ ρ) :
    ∃ (l : Nat) (Ξ : QCtx τ l) (κ : Fin n → Fin l), QCtx.Weakening Ξ Γ κ ∧
      UniformityRule (ε := ε) F p Ξ (Tm.rename κ a) (Tm.rename κ b) A
        Θ (Tm.rename ρ c) (Tm.rename ρ d) B := by
  cases h with
  | square f so si hu hi ha hs hb hb' hc hm =>
    obtain ⟨Θc, Θr, hso, hcW, hrW, _⟩ := hw.split so
    obtain ⟨Θl, hsi, hlW, hlin⟩ := hcW.selfSplit si
    have htop : Θl.linearity = ⊤ := top_le_iff.mp (hu ▸ hlin)
    refine ⟨m + 1, Θc.snoc _, Tm.up ρ, hcW.up _, ?_⟩
    simpa [Tm.rename, Tm.up] using UniformityRule.square f hso hsi htop hi
      (ha.rename ρ hrW) (hs.rename (Tm.up ρ) (hcW.up _))
      (hb.rename (Tm.up ρ) (hlW.up _)) (hb'.rename (Tm.up ρ) (hlW.up _))
      (hc.rename (Tm.up ρ) (hcW.up _)) hm

/-- Stability of primitive rewrites under native quantitative weakening.
This is an explicit structural assumption: pure substitution closure alone does
not supply the paper's missing identity substitutions at every quantity. -/
def Relation.RenamingClosed (R : Relation τ Φ) : Prop :=
  ∀ {n m : Nat} {Γ : QCtx τ n} {Θ : QCtx τ m} {a b : Term Φ n} {A : τ}
    (ρ : Fin n → Fin m), QCtx.Weakening Θ Γ ρ →
      R Γ a b A → R Θ (Tm.rename ρ a) (Tm.rename ρ b) A

namespace Polarity

@[simp] theorem source_rename (p : Polarity) (ρ : Fin n → Fin m) (a b : Term Φ n) :
    p.source (Tm.rename ρ a) (Tm.rename ρ b) = Tm.rename ρ (p.source a b) := by
  cases p <;> rfl

@[simp] theorem target_rename (p : Polarity) (ρ : Fin n → Fin m) (a b : Term Φ n) :
    p.target (Tm.rename ρ a) (Tm.rename ρ b) = Tm.rename ρ (p.target a b) := by
  cases p <;> rfl

end Polarity

/-- Native weakening is admissible for the full generated theory, including
the recursive directed uniformity rule. -/
theorem Refines.rename {R : Relation τ Φ} (h : Refines (ε := ε) F R Γ a b A)
    (ρ : Fin n → Fin m) (hw : QCtx.Weakening Θ Γ ρ) (hR : R.RenamingClosed) :
    Refines (ε := ε) F R Θ (Tm.rename ρ a) (Tm.rename ρ b) A := by
  induction h generalizing m with
  | base h ha hb => exact .base (hR ρ hw h) (ha.rename hw) (hb.rename hw)
  | refl h => exact .refl (h.rename hw)
  | trans _ _ ih ik => exact .trans (ih ρ hw) (ik ρ hw)
  | equation p h ha hb =>
    simpa only [Polarity.source_rename, Polarity.target_rename] using
      Refines.equation p (h.rename hw) (ha.rename hw) (hb.rename hw)
  | directional p h ha hb =>
    simpa only [Polarity.source_rename, Polarity.target_rename] using
      Refines.directional p (h.rename hw) (ha.rename hw) (hb.rename hw)
  | uniformity p r hc hd _ ih =>
    obtain ⟨l, Ξ, κ, hk, r'⟩ := r.rename hw
    apply (by simpa only [Polarity.source_rename, Polarity.target_rename] using
      Refines.uniformity (R := R) p r' (hc.rename hw) (hd.rename hw))
    simpa only [Polarity.source_rename, Polarity.target_rename] using ih κ hk
  | op _ ih => exact .op (ih ρ hw)
  | let₁ s _ _ ih ik =>
    obtain ⟨Θl, Θr, hs, hl, hr, _⟩ := hw.split s
    exact .let₁ hs (ih ρ hr) (ik (Tm.up ρ) (hl.up _))
  | pair s _ _ ih ik =>
    obtain ⟨Θl, Θr, hs, hl, hr, _⟩ := hw.split s
    exact .pair hs (ih ρ hl) (ik ρ hr)
  | let₂ s _ _ ih ik =>
    obtain ⟨Θl, Θr, hs, hl, hr, _⟩ := hw.split s
    exact .let₂ hs (ih ρ hr) (ik (Tm.up (Tm.up ρ)) ((hl.up _).up _))
  | inl f _ ih => exact .inl f (ih ρ hw)
  | inr f _ ih => exact .inr f (ih ρ hw)
  | case f s _ _ _ ih il ir =>
    obtain ⟨Θl, Θr, hs, hl, hr, _⟩ := hw.split s
    exact .case f hs (ih ρ hr) (il (Tm.up ρ) (hl.up _)) (ir (Tm.up ρ) (hl.up _))
  | abort f _ ih => exact .abort f (ih ρ hw)
  | iter f s hu _ _ ih ik =>
    obtain ⟨Θl, Θr, hs, hl, hr, ht⟩ := hw.split s
    exact .iter f hs (ht hu) (ih ρ hr) (ik (Tm.up ρ) (hl.up _))

/-- Mutual refinement inherits admissible native weakening. -/
theorem Equates.rename {R : Relation τ Φ} (h : Equates (ε := ε) F R Γ a b A)
    (ρ : Fin n → Fin m) (hw : QCtx.Weakening Θ Γ ρ) (hR : R.RenamingClosed) :
    Equates (ε := ε) F R Θ (Tm.rename ρ a) (Tm.rename ρ b) A :=
  ⟨h.1.rename ρ hw hR, h.2.rename ρ hw hR⟩

/-- Generating a theory preserves primitive renaming stability. -/
theorem Relation.RenamingClosed.refines {R : Relation τ Φ} (hR : R.RenamingClosed) :
    Relation.RenamingClosed (Refines (ε := ε) F R) := fun ρ hw h => h.rename ρ hw hR

end Silmaril.Isotope.Refinement
