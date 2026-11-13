module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Substitution

/-! # Effect allowances under quantitative substitution operations -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Substitution

universe u v w
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ] {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment}
open LetIter.LocallyNameless

/-- Renaming does not alter the effects of retained substitution entries. -/
theorem EffectAllowed.rename_nonempty {p : Polarity} {η : ε}
    {n m : Nat} {Γ : QCtx τ m} {Δ : QCtx τ n} {e : ε} {σ : Fin n → Term Φ m}
    {hσ : Substitution F Γ e σ Δ} (hh : EffectAllowed p η hσ) :
    ∀ {k : Nat} {Θ : QCtx τ k} (ρ : Fin m → Fin k), QCtx.Weakening Θ Γ ρ →
      ∃ h : Substitution F Θ e (fun i => Tm.rename ρ (σ i)) Δ, EffectAllowed p η h := by
  induction hσ with
  | nil hd =>
    intro k Θ ρ hw
    have hempty : (fun i : Fin 0 => Tm.rename ρ (Fin.elim0 i)) =
        (Fin.elim0 : Fin 0 → Term Φ k) := funext (fun i => Fin.elim0 i)
    rw [hempty]
    exact ⟨.nil (hw.discardable hd), trivial⟩
  | @zero m n Γ Δ e σ hσ a A ih =>
    intro k Θ ρ hw
    obtain ⟨h, ha⟩ := ih hh ρ hw
    have hfun : (fun i => Tm.rename ρ (Fin.cases a σ i)) =
        Fin.cases (Tm.rename ρ a) (fun i => Tm.rename ρ (σ i)) :=
      funext (fun i => Fin.cases rfl (fun _ => rfl) i)
    rw [hfun]
    exact ⟨.zero h (Tm.rename ρ a) A, ha⟩
  | @cons m n Γ Γl Γr Δ e el er σ a A q hs hσ ha hq hc hl hr ih =>
    intro k Θ ρ hw
    obtain ⟨Θr, Θl, hsplit, wr, wl, hlin⟩ := hw.split_linearity hs.symm
    obtain ⟨h, hg⟩ := ih hh.1 ρ wl
    have hfun : (fun i => Tm.rename ρ (Fin.cases a σ i)) =
        Fin.cases (Tm.rename ρ a) (fun i => Tm.rename ρ (σ i)) :=
      funext (fun i => Fin.cases rfl (fun _ => rfl) i)
    rw [hfun]
    exact ⟨.cons hsplit.symm h (ha.rename ρ wr) (hq.trans hlin) hc hl hr,
      hg, hh.2⟩

/-- Destination splitting preserves the entrywise effect allowances, including
when a relevant entry is used in both output substitutions. -/
theorem EffectAllowed.split_linearity {p : Polarity} {η : ε}
    {n m : Nat} {Γ : QCtx τ m} {Δ : QCtx τ n} {e : ε} {σ : Fin n → Term Φ m}
    {hσ : Substitution F Γ e σ Δ} (hh : EffectAllowed p η hσ) :
    ∀ {Δl Δr : QCtx τ n}, Δ.Split Δl Δr →
      ∃ Γl Γr, ∃ _hs : Γ.Split Γl Γr,
        ∃ hl : Substitution F Γl e σ Δl, ∃ hr : Substitution F Γr e σ Δr,
          EffectAllowed p η hl ∧ EffectAllowed p η hr ∧ Δl.linearity ≤ Γl.linearity := by
  induction hσ with
  | @nil m Γ e hd =>
    intro Δl Δr hs
    have hl : Δl = QCtx.nil := funext (fun i => Fin.elim0 i)
    have hr : Δr = QCtx.nil := funext (fun i => Fin.elim0 i)
    subst Δl
    subst Δr
    exact ⟨Γ.zero, Γ, .zero_left Γ, .nil (QCtx.zero_discardable Γ), .nil hd,
      trivial, trivial, by rw [QCtx.zero_linearity]; exact le_top⟩
  | @zero m n Γ Δ e σ hσ a A ih =>
    intro Δl Δr hs
    obtain ⟨ΔL, ql, rfl⟩ := QCtx.exists_snoc_type Δl A (hs 0).1
    obtain ⟨ΔR, qr, rfl⟩ := QCtx.exists_snoc_type Δr A (hs 0).2.1
    have hhead : QCtx.SlotSplit A .zero ql qr := (hs 0).2.2
    obtain ⟨Γl, Γr, hg, hl, hr, hhl, hhr, ht⟩ := ih hh (fun i => hs i.succ)
    cases hhead with
    | left =>
      exact ⟨Γl, Γr, hg, .zero hl a A, .zero hr a A, hhl, hhr,
        by rw [QCtx.linearity_snoc]; exact inf_le_right.trans ht⟩
    | right =>
      exact ⟨Γl, Γr, hg, .zero hl a A, .zero hr a A, hhl, hhr,
        by rw [QCtx.linearity_snoc]; exact inf_le_right.trans ht⟩
    | both hc => exact False.elim hc
  | @cons m n Γ Γl Γr Δ e el er σ a A q hs hσ ha hq hc hel her ih =>
    intro Δl Δr hsplit
    obtain ⟨ΔL, ql, rfl⟩ := QCtx.exists_snoc_type Δl A (hsplit 0).1
    obtain ⟨ΔR, qr, rfl⟩ := QCtx.exists_snoc_type Δr A (hsplit 0).2.1
    have hhead : QCtx.SlotSplit A (.used q) ql qr := (hsplit 0).2.2
    obtain ⟨ΓL, ΓR, hg, hl, hr, hhl, hhr, ht⟩ := ih hh.1 (fun i => hsplit i.succ)
    have hlin : (ΔL.snoc A (.used q)).linearity ≤ Γr.linearity := by
      rw [QCtx.linearity_snoc, Usage.linearity_used]
      exact (inf_le_left.trans inf_le_right).trans hq
    have htailLin : (ΔL.snoc A (.used q)).linearity ≤ ΓL.linearity := by
      rw [QCtx.linearity_snoc]
      exact inf_le_right.trans ht
    cases hhead with
    | left =>
      obtain ⟨ΓL', hp, hleft⟩ := hs.swapAssoc hg
      exact ⟨ΓL', ΓR, hp, .cons hleft hl ha hq hc hel her,
        .zero (hr.effectMono hel) a A, ⟨hhl, hh.2⟩, hhr.effectMono hel,
        hleft.le_linearity htailLin hlin⟩
    | right =>
      obtain ⟨ΓR', hp, hright⟩ := hs.swapAssoc hg.symm
      exact ⟨ΓL, ΓR', hp.symm, .zero (hl.effectMono hel) a A,
        .cons hright hr ha hq hc hel her, hhl.effectMono hel, ⟨hhr, hh.2⟩,
        by rw [QCtx.linearity_snoc]; exact inf_le_right.trans ht⟩
    | both hcopy =>
      have hrel : Quantity.relevant ≤ Γr.linearity :=
        ((show Quantity.relevant ≤ q ⊓ quantity A from hcopy).trans inf_le_left).trans hq
      obtain ⟨ΓL', ΓR', hp, hleft, hright⟩ := hs.distribute hg hrel
      exact ⟨ΓL', ΓR', hp, .cons hleft hl ha hq hc hel her,
        .cons hright hr ha hq hc hel her, ⟨hhl, hh.2⟩, ⟨hhr, hh.2⟩,
        hleft.le_linearity htailLin hlin⟩

end Silmaril.Isotope.Refinement.Substitution
