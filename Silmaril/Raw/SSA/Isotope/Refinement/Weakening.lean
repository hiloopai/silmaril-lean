module

public import Silmaril.Raw.SSA.Isotope.Refinement.ContextWeakening
public import Silmaril.Raw.SSA.Isotope.Refinement.Typing

@[expose] public section

noncomputable section

namespace Silmaril.Isotope.Refinement

universe u v w

namespace Usage

/-- Effective weakening increases linearity for an actually used slot. The
nonzero premise is essential: unused slots always have top linearity. -/
theorem linearity_le_of_effective_le (a b : Usage) (A : Quantity) (ha : a ≠ zero)
    (h : effective a A ≤ effective b A) : linearity a A ≤ linearity b A := by
  revert h ha a b A
  decide

end Usage

namespace QCtx

variable {τ : Type u} [HasQuantity τ]

theorem Weakening.refl {n : Nat} (Γ : QCtx τ n) : Weakening Γ Γ id := by
  induction n with
  | zero =>
    have hΓ : Γ = QCtx.nil := funext (fun i => Fin.elim0 i)
    subst Γ
    convert Weakening.nil using 1
  | succ n ih =>
    have h := Weakening.cons (ih (fun i => Γ i.succ))
      (le_refl (Usage.effective (Γ 0).2 (quantity (Γ 0).1)))
    rw [snoc_tail Γ] at h
    convert h using 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

theorem Weakening.up {n m : Nat} {Γ : QCtx τ n} {Δ : QCtx τ m}
    {ρ : Fin m → Fin n} (h : Weakening Γ Δ ρ) (A : τ) (q : Usage := .used ⊤) :
    Weakening (Γ.snoc A q) (Δ.snoc A q) (LetIter.LocallyNameless.Tm.up ρ) := .cons h le_rfl

theorem Weakening.insertZero {n : Nat} (Γ : QCtx τ n) (A : τ) :
    Weakening (Γ.snoc A .zero) Γ Fin.succ := .skip (.refl Γ) le_rfl

/-- Resplitting reserves an unused left slot for the right context. This
choice preserves unrestricted loop-body contexts during weakening. -/
theorem SlotSplit.weaken {A : τ} {q q' ql qr : Usage}
    (hs : SlotSplit A q' ql qr)
    (h : Usage.effective q' (quantity A) ≤ Usage.effective q (quantity A)) :
    ∃ qL qR, SlotSplit A q qL qR ∧
      Usage.effective ql (quantity A) ≤ Usage.effective qL (quantity A) ∧
      Usage.effective qr (quantity A) ≤ Usage.effective qR (quantity A) ∧
      Usage.linearity ql (quantity A) ≤ Usage.linearity qL (quantity A) := by
  cases hs with
  | left =>
    by_cases hz : q' = .zero
    · subst q'
      exact ⟨.zero, q, .right q, le_rfl, h, le_rfl⟩
    · refine ⟨q, .zero, .left q, h, le_rfl, ?_⟩
      exact Usage.linearity_le_of_effective_le _ _ _ hz h
  | right => exact ⟨.zero, q, .right q, le_rfl, h, le_rfl⟩
  | both hc =>
    have hz : q' ≠ .zero := by
      intro hz
      subst q'
      exact hc
    refine ⟨q, q, .both q (hc.trans h), h, h, ?_⟩
    exact Usage.linearity_le_of_effective_le _ _ _ hz h

theorem linearity_snoc {n : Nat} (Γ : QCtx τ n) (A : τ) (q : Usage) :
    (Γ.snoc A q).linearity = Usage.linearity q (quantity A) ⊓ Γ.linearity := by
  apply le_antisymm
  · apply le_inf
    · exact (le_linearity_iff.mp le_rfl) 0
    · apply le_linearity_iff.mpr
      intro i
      exact (le_linearity_iff.mp le_rfl) i.succ
  · apply le_linearity_iff.mpr
    intro i
    exact Fin.cases inf_le_left
      (fun j => inf_le_right.trans ((le_linearity_iff.mp le_rfl) j)) i

theorem Weakening.split_linearity {n m : Nat} {Γ : QCtx τ n} {Δ Δl Δr : QCtx τ m}
    {ρ : Fin m → Fin n} (h : Weakening Γ Δ ρ) (s : Δ.Split Δl Δr) :
    ∃ Γl Γr, Γ.Split Γl Γr ∧ Weakening Γl Δl ρ ∧ Weakening Γr Δr ρ ∧
      Δl.linearity ≤ Γl.linearity := by
  induction h with
  | nil =>
    have hl : Δl = QCtx.nil := by funext i; exact Fin.elim0 i
    have hr : Δr = QCtx.nil := by funext i; exact Fin.elim0 i
    subst Δl
    subst Δr
    exact ⟨QCtx.nil, QCtx.nil, .nil, .nil, .nil, le_rfl⟩
  | @cons n m Γ Δ ρ A q q' h hq ih =>
    have hs : (Δl 0).1 = A ∧ (Δr 0).1 = A ∧ SlotSplit A q' (Δl 0).2 (Δr 0).2 := s 0
    obtain ⟨qL, qR, hsplit, hl, hr, htop⟩ := hs.2.2.weaken hq
    have stail : Δ.Split (fun i => Δl i.succ) (fun i => Δr i.succ) := fun i => s i.succ
    obtain ⟨Γl, Γr, sg, wl, wr, ht⟩ := ih stail
    refine ⟨Γl.snoc A qL, Γr.snoc A qR, sg.snoc hsplit, ?_, ?_, ?_⟩
    · have htarget : QCtx.snoc (fun i : Fin m => Δl i.succ) A (Δl 0).2 = Δl := by
        rw [← hs.1]
        exact snoc_tail Δl
      rw [← htarget]
      exact .cons wl hl
    · have htarget : QCtx.snoc (fun i : Fin m => Δr i.succ) A (Δr 0).2 = Δr := by
        rw [← hs.2.1]
        exact snoc_tail Δr
      rw [← htarget]
      exact .cons wr hr
    · rw [linearity_snoc]
      apply le_inf
      · apply le_trans _ htop
        simpa only [hs.1] using
          ((le_linearity_iff.mp (le_rfl : Δl.linearity ≤ Δl.linearity)) (0 : Fin (m + 1)))
      · apply le_trans _ ht
        apply le_linearity_iff.mpr
        intro i
        exact (le_linearity_iff.mp le_rfl) i.succ
  | @skip n m Γ Δ ρ A q h hq ih =>
    obtain ⟨Γl, Γr, sg, wl, wr, ht⟩ := ih s
    exact ⟨Γl.snoc A .zero, Γr.snoc A q, sg.snoc (.right q),
      .skip wl le_rfl, .skip wr hq, by
        rw [linearity_snoc, Usage.linearity_zero]
        exact ht⟩

/-- The loop-body form of split transport follows from the stronger linearity bound. -/
theorem Weakening.split {n m : Nat} {Γ : QCtx τ n} {Δ Δl Δr : QCtx τ m}
    {ρ : Fin m → Fin n} (h : Weakening Γ Δ ρ) (s : Δ.Split Δl Δr) :
    ∃ Γl Γr, Γ.Split Γl Γr ∧ Weakening Γl Δl ρ ∧ Weakening Γr Δr ρ ∧
      (Δl.linearity = ⊤ → Γl.linearity = ⊤) := by
  obtain ⟨Γl, Γr, hs, hl, hr, hq⟩ := h.split_linearity s
  exact ⟨Γl, Γr, hs, hl, hr, fun ht => top_le_iff.mp (ht ▸ hq)⟩

theorem Weakening.discardable {n m : Nat} {Γ : QCtx τ n} {Δ : QCtx τ m}
    {ρ : Fin m → Fin n} (h : Weakening Γ Δ ρ) (hd : Δ.Discardable) : Γ.Discardable := by
  intro j
  by_cases hj : ∃ i, ρ i = j
  · obtain ⟨i, rfl⟩ := hj
    exact (hd i).trans (h.effective_le i)
  · exact h.omitted j (fun i hi => hj ⟨i, hi⟩)

theorem Weakening.varAllowed {n m : Nat} {Γ : QCtx τ n} {Δ : QCtx τ m}
    {ρ : Fin m → Fin n} (h : Weakening Γ Δ ρ) {i : Fin m} (hv : Δ.VarAllowed i) :
    Γ.VarAllowed (ρ i) := by
  unfold VarAllowed at hv
  constructor
  · rw [Usage.effective_linear] at hv ⊢
    exact hv.1.trans (h.effective_le i)
  · intro j hji
    by_cases hj : ∃ k, ρ k = j
    · obtain ⟨k, rfl⟩ := hj
      exact (hv.2 k (fun he => hji (congrArg ρ he))).trans (h.effective_le k)
    · exact h.omitted j (fun k hk => hj ⟨k, hk⟩)

end QCtx

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]

namespace HasType

open LetIter.LocallyNameless

variable {F : Fragment} {n : Nat} {Δ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ}

/-- The written weakening lemma, retaining the actual finite-index renaming.
Resource splitting and the unrestricted loop-body condition are transported. -/
theorem rename_nonempty (ht : HasType F Δ e t A) :
    ∀ {m : Nat} {Γ : QCtx τ m} (ρ : Fin n → Fin m), QCtx.Weakening Γ Δ ρ →
      Nonempty (HasType F Γ e (Tm.rename ρ t) A) := by
  induction ht with
  | var i hv =>
    intro m Γ ρ hw
    rw [← hw.types i]
    exact ⟨.var (ρ i) (hw.varAllowed hv)⟩
  | op hf _ ih =>
    intro m Γ ρ hw
    obtain ⟨h⟩ := ih ρ hw
    exact ⟨.op hf h⟩
  | let₁ split _ _ iha ihb =>
    intro m Γ ρ hw
    obtain ⟨Γl, Γr, hs, hl, hr, _⟩ := hw.split split
    obtain ⟨ha⟩ := iha ρ hr
    obtain ⟨hb⟩ := ihb (Tm.up ρ) (.cons hl le_rfl)
    exact ⟨.let₁ hs ha hb⟩
  | unit hd =>
    intro m Γ ρ hw
    exact ⟨.unit (hw.discardable hd)⟩
  | pair split _ _ iha ihb =>
    intro m Γ ρ hw
    obtain ⟨Γl, Γr, hs, hl, hr, _⟩ := hw.split split
    obtain ⟨ha⟩ := iha ρ hl
    obtain ⟨hb⟩ := ihb ρ hr
    exact ⟨.pair hs ha hb⟩
  | let₂ split _ _ iha ihb =>
    intro m Γ ρ hw
    obtain ⟨Γl, Γr, hs, hl, hr, _⟩ := hw.split split
    obtain ⟨ha⟩ := iha ρ hr
    obtain ⟨hb⟩ := ihb (Tm.up (Tm.up ρ)) (.cons (.cons hl le_rfl) le_rfl)
    exact ⟨.let₂ hs ha hb⟩
  | inl f _ ih =>
    intro m Γ ρ hw
    obtain ⟨h⟩ := ih ρ hw
    exact ⟨.inl f h⟩
  | inr f _ ih =>
    intro m Γ ρ hw
    obtain ⟨h⟩ := ih ρ hw
    exact ⟨.inr f h⟩
  | case f split _ _ _ iha ihl ihr =>
    intro m Γ ρ hw
    obtain ⟨Γl, Γr, hs, hl, hr, _⟩ := hw.split split
    obtain ⟨ha⟩ := iha ρ hr
    obtain ⟨hleft⟩ := ihl (Tm.up ρ) (.cons hl le_rfl)
    obtain ⟨hright⟩ := ihr (Tm.up ρ) (.cons hl le_rfl)
    exact ⟨.case f hs ha hleft hright⟩
  | abort f _ ih =>
    intro m Γ ρ hw
    obtain ⟨h⟩ := ih ρ hw
    exact ⟨.abort f h⟩
  | iter f split hu hi _ _ iha ihb =>
    intro m Γ ρ hw
    obtain ⟨Γl, Γr, hs, hl, hr, htop⟩ := hw.split split
    obtain ⟨ha⟩ := iha ρ hr
    obtain ⟨hb⟩ := ihb (Tm.up ρ) (.cons hl le_rfl)
    exact ⟨.iter f hs (htop hu) hi ha hb⟩

/-- Choose a native derivation of the weakening theorem. -/
def rename (ht : HasType F Δ e t A) {m : Nat} {Γ : QCtx τ m}
    (ρ : Fin n → Fin m) (hw : QCtx.Weakening Γ Δ ρ) :
    HasType F Γ e (Tm.rename ρ t) A := Classical.choice (ht.rename_nonempty ρ hw)

end HasType
end Silmaril.Isotope.Refinement
