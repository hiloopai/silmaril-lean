module

public import Silmaril.Raw.SSA.Isotope.Refinement.TypingSubstitution

@[expose] public section

noncomputable section

namespace Silmaril.Isotope.Refinement

universe u v w

open LetIter.LocallyNameless (Tm)

namespace QCtx

variable {τ : Type u} [HasQuantity τ] {n : Nat}

theorem SlotSplit.parent_unique {A : τ} {q q' ql qr : Usage}
    (h : SlotSplit A q ql qr) (k : SlotSplit A q' ql qr) : q = q' := by
  cases h <;> cases k <;> rfl

theorem Split.parent_unique {Γ Θ Γl Γr : QCtx τ n}
    (h : Γ.Split Γl Γr) (k : Θ.Split Γl Γr) : Γ = Θ := by
  funext i
  apply Prod.ext
  · exact (h i).1.symm.trans (k i).1
  · have ki := (k i).2.2
    rw [← (k i).1, (h i).1] at ki
    exact (h i).2.2.parent_unique ki

theorem SlotSplit.retain {A : τ} {q ql qr qs : Usage}
    (h : SlotSplit A q ql qr) (k : SlotSplit A ql qs ql) : SlotSplit A q qs q := by
  cases h with
  | left => exact k
  | right =>
    cases k with
    | left => exact .right _
    | right => exact .right _
    | both hc => exact False.elim hc
  | both => exact k

theorem Split.retain {Γ Γl Γr Θ : QCtx τ n}
    (h : Γ.Split Γl Γr) (k : Γl.Split Θ Γl) : Γ.Split Θ Γ := by
  intro i
  have ki := (k i).2.2
  rw [(h i).1] at ki
  exact ⟨(k i).1.trans (h i).1, rfl, (h i).2.2.retain ki⟩

end QCtx

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]

namespace Substitution

variable {F : Fragment} {n m : Nat} {Γ : QCtx τ m} {Δ : QCtx τ n}
variable {e : ε} {σ : Fin n → Term Φ m}

/-- Restriction along a split that retains the entire destination can retain
the entire source as well. This is needed by elimination and uniformity. -/
theorem selfSplit_nonempty (hσ : Substitution F Γ e σ Δ) :
    ∀ {Δl : QCtx τ n}, Δ.Split Δl Δ →
      ∃ Γl, Γ.Split Γl Γ ∧ Nonempty (Substitution F Γl e σ Δl) ∧
        Δl.linearity ≤ Γl.linearity := by
  induction hσ with
  | @nil m Γ e hd =>
    intro Δl hs
    have hl : Δl = QCtx.nil := funext fun i => Fin.elim0 i
    subst Δl
    exact ⟨Γ.zero, .zero_left Γ, ⟨.nil (QCtx.zero_discardable Γ)⟩,
      by rw [QCtx.zero_linearity]; exact le_top⟩
  | @zero m n Γ Δ e σ hσ a A ih =>
    intro Δl hs
    obtain ⟨ΔL, ql, rfl⟩ := QCtx.exists_snoc_type Δl A (hs 0).1
    have hhead : QCtx.SlotSplit A .zero ql .zero := (hs 0).2.2
    have htail : Δ.Split ΔL Δ := fun i => hs i.succ
    obtain ⟨Γl, hg, ⟨hl⟩, hlin⟩ := ih htail
    cases hhead with
    | left | right =>
      exact ⟨Γl, hg, ⟨.zero hl a A⟩,
        by rw [QCtx.linearity_snoc]; exact inf_le_right.trans hlin⟩
    | both hc => exact False.elim hc
  | @cons m n Γ Γl Γr Δ e el er σ a A q hs hσ ha hq hc hel her ih =>
    intro Δl hsplit
    obtain ⟨ΔL, ql, rfl⟩ := QCtx.exists_snoc_type Δl A (hsplit 0).1
    have hhead : QCtx.SlotSplit A (.used q) ql (.used q) := (hsplit 0).2.2
    have htail : Δ.Split ΔL Δ := fun i => hsplit i.succ
    obtain ⟨ΓL, hg, ⟨hl⟩, hlin⟩ := ih htail
    cases hhead with
    | right =>
      exact ⟨ΓL, hs.retain hg, ⟨.zero (hl.effectMono hel) a A⟩,
        by rw [QCtx.linearity_snoc]; exact inf_le_right.trans hlin⟩
    | both hcopy =>
      have hrel : Quantity.relevant ≤ Γr.linearity :=
        ((show Quantity.relevant ≤ q ⊓ quantity A from hcopy).trans inf_le_left).trans hq
      obtain ⟨ΓL', ΓR', hp, hleft, hright⟩ := hs.distribute hg hrel
      have heq := hright.parent_unique hs
      subst ΓR'
      refine ⟨ΓL', hp, ⟨.cons hleft hl ha hq hc hel her⟩, ?_⟩
      apply hleft.le_linearity
      · rw [QCtx.linearity_snoc]
        exact inf_le_right.trans hlin
      · rw [QCtx.linearity_snoc, Usage.linearity_used]
        exact (inf_le_left.trans inf_le_right).trans hq

/-- A native substitution preceded by an identity-index quantitative weakening
of its target. This derived presentation supports binder normalization without
strengthening the written substitution rules. -/
def Admissible (F : Fragment) (Γ : QCtx τ m) (e : ε)
    (σ : Fin n → Term Φ m) (Δ : QCtx τ n) : Prop :=
  ∃ Θ : QCtx τ n, QCtx.Weakening Θ Δ id ∧ Nonempty (Substitution F Γ e σ Θ)

theorem admissible (hσ : Substitution F Γ e σ Δ) : Admissible F Γ e σ Δ :=
  ⟨Δ, .refl Δ, ⟨hσ⟩⟩

/-- Lifting at an arbitrary binder allowance normalizes that allowance by the
type quantity. Zero-use binders still require no typing of their entry. -/
def upAtNormalized (hσ : Substitution F Γ e σ Δ) (A : τ) (q : Usage) :
    Substitution F (Γ.snoc A q) e (Tm.upSub σ)
      (Δ.snoc A (Usage.effective q (quantity A))) := by
  cases q with
  | zero =>
    exact .zero (hσ.rename Fin.succ (.insertZero Γ A)) (.bv 0) A
  | used q =>
    have hv : (Γ.zero.snoc A (.used q)).VarAllowed 0 := by
      constructor
      · change Usage.effective (.used .linear) (quantity A) ≤
          Usage.effective (.used q) (quantity A)
        change Quantity.linear ⊓ quantity A ≤ q ⊓ quantity A
        exact inf_le_inf bot_le le_rfl
      · intro i hi
        cases i using Fin.cases with
        | zero => exact False.elim (hi rfl)
        | succ j => exact le_rfl
    exact .cons ((QCtx.Split.zero_right Γ).snoc (.right _))
      (hσ.rename Fin.succ (.insertZero Γ A)) (.var (e := ⊥) 0 hv)
      (by rw [QCtx.linearity_snoc, QCtx.zero_linearity, inf_top_eq,
        Usage.linearity_used, inf_comm])
      (EffectSystem.pure_commutes e).symm le_rfl bot_le

namespace Admissible

theorem effectMono (hσ : Admissible F Γ e σ Δ) {e' : ε} (he : e ≤ e') :
    Admissible F Γ e' σ Δ := by
  obtain ⟨Θ, hw, ⟨hs⟩⟩ := hσ
  exact ⟨Θ, hw, ⟨hs.effectMono he⟩⟩

theorem hasType (hσ : Admissible F Γ e σ Δ) {a : Term Φ n} {A : τ}
    (h : HasType F Δ e a A) : Nonempty (HasType F Γ e (Tm.bsubst σ a) A) := by
  obtain ⟨Θ, hw, ⟨hs⟩⟩ := hσ
  have h' := h.rename id hw
  rw [show Tm.rename id a = a from Tm.rename_id a] at h'
  exact ⟨h'.bsubst hs⟩

def typing (hσ : Admissible F Γ e σ Δ) {a : Term Φ n} {A : τ}
    (h : HasType F Δ e a A) : HasType F Γ e (Tm.bsubst σ a) A :=
  Classical.choice (hσ.hasType h)

theorem up (hσ : Admissible F Γ e σ Δ) (A : τ) (q : Usage := .used ⊤) :
    Admissible F (Γ.snoc A q) e (Tm.upSub σ) (Δ.snoc A q) := by
  obtain ⟨Θ, hw, ⟨hs⟩⟩ := hσ
  refine ⟨Θ.snoc A (Usage.effective q (quantity A)), ?_, ⟨hs.upAtNormalized A q⟩⟩
  have hq : Usage.effective q (quantity A) ≤
      Usage.effective (Usage.effective q (quantity A)) (quantity A) := by
    rw [Usage.effective_idem]
  convert QCtx.Weakening.cons hw hq using 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem split (hσ : Admissible F Γ e σ Δ) {Δl Δr : QCtx τ n}
    (s : Δ.Split Δl Δr) :
    ∃ Γl Γr, Γ.Split Γl Γr ∧ Admissible F Γl e σ Δl ∧
      Admissible F Γr e σ Δr ∧ Δl.linearity ≤ Γl.linearity := by
  obtain ⟨Θ, hw, ⟨hs⟩⟩ := hσ
  obtain ⟨Θl, Θr, hsplit, hwl, hwr, hlin⟩ := hw.split_linearity s
  obtain ⟨Γl, Γr, hg, hl, hr, hlin'⟩ := hs.split_linearity_nonempty hsplit
  exact ⟨Γl, Γr, hg, ⟨Θl, hwl, hl⟩, ⟨Θr, hwr, hr⟩, hlin.trans hlin'⟩

theorem selfSplit (hσ : Admissible F Γ e σ Δ) {Δl : QCtx τ n}
    (s : Δ.Split Δl Δ) :
    ∃ Γl, Γ.Split Γl Γ ∧ Admissible F Γl e σ Δl ∧ Δl.linearity ≤ Γl.linearity := by
  obtain ⟨Θ, hw, ⟨hs⟩⟩ := hσ
  obtain ⟨Θl, hsplit, hwl, hlin⟩ := hw.selfSplit s
  obtain ⟨Γl, hg, hl, hlin'⟩ := hs.selfSplit_nonempty hsplit
  exact ⟨Γl, hg, ⟨Θl, hwl, hl⟩, hlin.trans hlin'⟩

end Admissible
end Substitution
end Silmaril.Isotope.Refinement
