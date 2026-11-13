module

public import Silmaril.Raw.SSA.Isotope.Refinement.Weakening
public import Silmaril.Raw.SSA.Isotope.Refinement.Substitution
public import Silmaril.Raw.SSA.Isotope.Refinement.ContextSplitting
public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.TheorySubstitution

@[expose] public section

noncomputable section

namespace Silmaril.Isotope.Refinement

universe u v w

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]

open LetIter.LocallyNameless

namespace Substitution

variable {F : Fragment} {n m : Nat} {Γ : QCtx τ m} {Δ : QCtx τ n}
variable {e : ε} {σ : Fin n → Term Φ m}

/-- Weakening a substitution preserves its independent entry effects and
the linearity bounds on every reused entry. -/
theorem rename_nonempty (hσ : Substitution F Γ e σ Δ) :
    ∀ {k : Nat} {Θ : QCtx τ k} (ρ : Fin m → Fin k), QCtx.Weakening Θ Γ ρ →
      Nonempty (Substitution F Θ e (fun i => Tm.rename ρ (σ i)) Δ) := by
  induction hσ with
  | nil hd =>
    intro k Θ ρ hw
    have hempty : (fun i : Fin 0 => Tm.rename ρ (Fin.elim0 i)) =
        (Fin.elim0 : Fin 0 → Term Φ k) :=
      funext (fun i => Fin.elim0 i)
    rw [hempty]
    exact ⟨.nil (hw.discardable hd)⟩
  | @zero m n Γ Δ e σ hσ a A ih =>
    intro k Θ ρ hw
    obtain ⟨h⟩ := ih ρ hw
    have hfun : (fun i => Tm.rename ρ (Fin.cases a σ i)) =
        Fin.cases (Tm.rename ρ a) (fun i => Tm.rename ρ (σ i)) :=
      funext (fun i => Fin.cases rfl (fun _ => rfl) i)
    rw [hfun]
    exact ⟨.zero h (Tm.rename ρ a) A⟩
  | @cons m n Γ Γl Γr Δ e el er σ a A q hs hσ ha hq hc hl hr ih =>
    intro k Θ ρ hw
    obtain ⟨Θr, Θl, hsplit, wr, wl, hlin⟩ := hw.split_linearity hs.symm
    obtain ⟨h⟩ := ih ρ wl
    have hfun : (fun i => Tm.rename ρ (Fin.cases a σ i)) =
        Fin.cases (Tm.rename ρ a) (fun i => Tm.rename ρ (σ i)) :=
      funext (fun i => Fin.cases rfl (fun _ => rfl) i)
    rw [hfun]
    exact ⟨.cons hsplit.symm h (ha.rename ρ wr) (hq.trans hlin) hc hl hr⟩

def rename (hσ : Substitution F Γ e σ Δ) {k : Nat} {Θ : QCtx τ k}
    (ρ : Fin m → Fin k) (hw : QCtx.Weakening Θ Γ ρ) :
    Substitution F Θ e (fun i => Tm.rename ρ (σ i)) Δ :=
  Classical.choice (hσ.rename_nonempty ρ hw)

/-- Restrict a substitution to a resource split of its destination. A relevant
entry is shared using its actual context-linearity premise; zero entries retain
their arbitrary syntax without acquiring a typing obligation. -/
theorem split_linearity_nonempty (hσ : Substitution F Γ e σ Δ) :
    ∀ {Δl Δr : QCtx τ n}, Δ.Split Δl Δr →
      ∃ Γl Γr, Γ.Split Γl Γr ∧
        Nonempty (Substitution F Γl e σ Δl) ∧ Nonempty (Substitution F Γr e σ Δr) ∧
        Δl.linearity ≤ Γl.linearity := by
  induction hσ with
  | @nil m Γ e hd =>
    intro Δl Δr hs
    have hl : Δl = QCtx.nil := funext (fun i => Fin.elim0 i)
    have hr : Δr = QCtx.nil := funext (fun i => Fin.elim0 i)
    subst Δl
    subst Δr
    exact ⟨Γ.zero, Γ, .zero_left Γ, ⟨.nil (QCtx.zero_discardable Γ)⟩,
      ⟨.nil hd⟩, by rw [QCtx.zero_linearity]; exact le_top⟩
  | @zero m n Γ Δ e σ hσ a A ih =>
    intro Δl Δr hs
    obtain ⟨ΔL, ql, rfl⟩ := QCtx.exists_snoc_type Δl A (hs 0).1
    obtain ⟨ΔR, qr, rfl⟩ := QCtx.exists_snoc_type Δr A (hs 0).2.1
    have hhead : QCtx.SlotSplit A .zero ql qr := (hs 0).2.2
    have htail : Δ.Split ΔL ΔR := fun i => hs i.succ
    obtain ⟨Γl, Γr, hg, ⟨hl⟩, ⟨hr⟩, ht⟩ := ih htail
    cases hhead with
    | left =>
      exact ⟨Γl, Γr, hg, ⟨.zero hl a A⟩, ⟨.zero hr a A⟩,
        by rw [QCtx.linearity_snoc]; exact inf_le_right.trans ht⟩
    | right =>
      exact ⟨Γl, Γr, hg, ⟨.zero hl a A⟩, ⟨.zero hr a A⟩,
        by rw [QCtx.linearity_snoc]; exact inf_le_right.trans ht⟩
    | both hc => exact False.elim hc
  | @cons m n Γ Γl Γr Δ e el er σ a A q hs hσ ha hq hc hel her ih =>
    intro Δl Δr hsplit
    obtain ⟨ΔL, ql, rfl⟩ := QCtx.exists_snoc_type Δl A (hsplit 0).1
    obtain ⟨ΔR, qr, rfl⟩ := QCtx.exists_snoc_type Δr A (hsplit 0).2.1
    have hhead : QCtx.SlotSplit A (.used q) ql qr := (hsplit 0).2.2
    have htail : Δ.Split ΔL ΔR := fun i => hsplit i.succ
    obtain ⟨ΓL, ΓR, hg, ⟨hl⟩, ⟨hr⟩, ht⟩ := ih htail
    have hlin : (ΔL.snoc A (.used q)).linearity ≤ Γr.linearity := by
      rw [QCtx.linearity_snoc, Usage.linearity_used]
      exact (inf_le_left.trans inf_le_right).trans hq
    have htailLin : (ΔL.snoc A (.used q)).linearity ≤ ΓL.linearity := by
      rw [QCtx.linearity_snoc]
      exact inf_le_right.trans ht
    cases hhead with
    | left =>
      obtain ⟨ΓL', hp, hleft⟩ := hs.swapAssoc hg
      refine ⟨ΓL', ΓR, hp, ⟨.cons hleft hl ha hq hc hel her⟩,
        ⟨.zero (hr.effectMono hel) a A⟩, ?_⟩
      exact hleft.le_linearity htailLin hlin
    | right =>
      obtain ⟨ΓR', hp, hright⟩ := hs.swapAssoc hg.symm
      exact ⟨ΓL, ΓR', hp.symm, ⟨.zero (hl.effectMono hel) a A⟩,
        ⟨.cons hright hr ha hq hc hel her⟩,
        by rw [QCtx.linearity_snoc]; exact inf_le_right.trans ht⟩
    | both hcopy =>
      have hrel : Quantity.relevant ≤ Γr.linearity := by
        have hrelq : Quantity.relevant ≤ q :=
          (show Quantity.relevant ≤ q ⊓ quantity A from hcopy).trans inf_le_left
        exact hrelq.trans hq
      obtain ⟨ΓL', ΓR', hp, hleft, hright⟩ := hs.distribute hg hrel
      refine ⟨ΓL', ΓR', hp, ⟨.cons hleft hl ha hq hc hel her⟩,
        ⟨.cons hright hr ha hq hc hel her⟩, ?_⟩
      exact hleft.le_linearity htailLin hlin

/-- The unrestricted-context specialization used by iteration typing. -/
theorem split_nonempty (hσ : Substitution F Γ e σ Δ) {Δl Δr : QCtx τ n}
    (s : Δ.Split Δl Δr) :
    ∃ Γl Γr, Γ.Split Γl Γr ∧
      Nonempty (Substitution F Γl e σ Δl) ∧ Nonempty (Substitution F Γr e σ Δr) ∧
      (Δl.linearity = ⊤ → Γl.linearity = ⊤) := by
  obtain ⟨Γl, Γr, hs, hl, hr, hlin⟩ := hσ.split_linearity_nonempty s
  exact ⟨Γl, Γr, hs, hl, hr, fun h => top_le_iff.mp (h ▸ hlin)⟩

/-- A substitution into a discardable context has a discardable source. -/
theorem discardable (hσ : Substitution F Γ e σ Δ) (hd : Δ.Discardable) :
    Γ.Discardable := by
  induction hσ with
  | nil h => exact h
  | zero hσ a A ih => exact ih (fun i => hd i.succ)
  | @cons m n Γ Γl Γr Δ e el er σ a A q hs hσ ha hq hc hel her ih =>
    apply QCtx.discardable_iff_linearity.mpr
    apply hs.le_linearity
    · exact QCtx.discardable_iff_linearity.mp (ih (fun i => hd i.succ))
    · have he : Usage.zero ≤ Usage.effective (.used q) (quantity A) := hd 0
      have hqa : Quantity.affine ≤ q :=
        (show Quantity.affine ≤ q ⊓ quantity A from (Usage.zero_le_used _).mp he).trans inf_le_left
      exact hqa.trans hq

/-- A variable that can actually be used has a typed substitution entry;
zero-usage entries remain unrestricted syntax. -/
theorem lookup_nonempty (hσ : Substitution F Γ e σ Δ) :
    ∀ i, Δ.VarAllowed i → Nonempty (HasType F Γ e (σ i) (Δ i).1) := by
  induction hσ with
  | nil hd => exact fun i => Fin.elim0 i
  | @zero m n Γ Δ e σ hσ a A ih =>
    intro i
    refine Fin.cases ?_ (fun i hi => ?_) i
    · intro hi
      have bad : (Usage.used Quantity.linear : Usage) ≤ Usage.zero := by
        simpa [QCtx.VarAllowed, QCtx.effective, Usage.effective_linear] using hi.1
      exact False.elim bad
    · exact ih i ⟨hi.1, fun j hj => hi.2 j.succ (fun h => hj (Fin.succ_injective _ h))⟩
  | @cons m n Γ Γl Γr Δ e el er σ a A q hs hσ ha hq hc hel her ih =>
    intro i
    refine Fin.cases ?_ (fun i hi => ?_) i
    · intro hi
      have hd : Δ.Discardable := fun j => hi.2 j.succ (Fin.succ_ne_zero j)
      have ht := (ha.rename id (hs.weakenRight (hσ.discardable hd))).effectMono her
      simpa only [show Tm.rename id a = a from Tm.rename_id a, Fin.cases_zero, QCtx.snoc_zero] using
        (show Nonempty _ from ⟨ht⟩)
    · have he : Usage.zero ≤ Usage.effective (.used q) (quantity A) :=
        hi.2 0 (Ne.symm (Fin.succ_ne_zero i))
      have hqa : Quantity.affine ≤ q :=
        (show Quantity.affine ≤ q ⊓ quantity A from (Usage.zero_le_used _).mp he).trans inf_le_left
      have hd : Γr.Discardable := QCtx.discardable_iff_linearity.mpr (hqa.trans hq)
      obtain ⟨ht⟩ := ih i ⟨hi.1, fun j hj => hi.2 j.succ (fun h => hj (Fin.succ_injective _ h))⟩
      have ht' := (ht.rename id (hs.weakenLeft hd)).effectMono hel
      simpa only [show Tm.rename id (σ i) = σ i from Tm.rename_id (σ i),
        Fin.cases_succ, QCtx.snoc_succ] using
        (show Nonempty _ from ⟨ht'⟩)

def lookup (hσ : Substitution F Γ e σ Δ) (i : Fin n) (hi : Δ.VarAllowed i) :
    HasType F Γ e (σ i) (Δ i).1 := Classical.choice (hσ.lookup_nonempty i hi)

/-- Lift through a binder at the type's own quantity. The effective allowance
is identical to an unrestricted annotation, while the literal substitution
rule can prove this target quantity even for a linear type. -/
def upNormalized (hσ : Substitution F Γ e σ Δ) (A : τ) :
    Substitution F (Γ.snoc A) e (Tm.upSub σ) (Δ.snoc A (.used (quantity A))) := by
  have hv : (Γ.zero.snoc A).VarAllowed 0 := by
    constructor
    · change Usage.effective (.used .linear) (quantity A) ≤
        Usage.effective (.used ⊤) (quantity A)
      change Quantity.linear ⊓ quantity A ≤ ⊤ ⊓ quantity A
      exact inf_le_inf bot_le le_rfl
    · intro i hi
      cases i using Fin.cases with
      | zero => exact False.elim (hi rfl)
      | succ j => exact le_rfl
  exact .cons ((QCtx.Split.zero_right Γ).snoc (.right _))
    (hσ.rename Fin.succ (QCtx.Weakening.insertZero Γ A))
    (.var (e := ⊥) 0 hv)
    (by simp only [QCtx.linearity_snoc, QCtx.zero_linearity, Usage.linearity_used,
      inf_top_eq]; exact le_rfl)
    (EffectSystem.pure_commutes e).symm le_rfl bot_le

end Substitution

namespace HasType

variable {F : Fragment} {n : Nat} {Γ : QCtx τ n} {e : ε}
variable {a : Term Φ (n + 1)} {A B : τ}

/-- Normalize a binder annotation without changing its effective allowance. -/
def normalizeBinder (h : HasType F (Γ.snoc A) e a B) :
    HasType F (Γ.snoc A (.used (quantity A))) e a B := by
  have hw : QCtx.Weakening (Γ.snoc A (.used (quantity A))) (Γ.snoc A) id :=
    .ofPointwise (fun i => Fin.cases rfl (fun _ => rfl) i) (fun i => by
      cases i using Fin.cases with
      | zero => simp [QCtx.effective]
      | succ j => exact le_rfl)
  simpa only [show Tm.rename id a = a from Tm.rename_id a] using h.rename id hw

end HasType

namespace HasType

/-- Normalize both freshly bound variables of product elimination. -/
def normalizeBinders₂ {F : Fragment} {n : Nat} {Γ : QCtx τ n} {e : ε}
    {a : Term Φ (n + 2)} {A B C : τ}
    (h : HasType F ((Γ.snoc A).snoc B) e a C) :
    HasType F ((Γ.snoc A (.used (quantity A))).snoc B (.used (quantity B))) e a C := by
  have hw : QCtx.Weakening
      ((Γ.snoc A (.used (quantity A))).snoc B (.used (quantity B)))
      ((Γ.snoc A).snoc B) id :=
    .ofPointwise (fun i => Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i)
      (fun i => by
        cases i using Fin.cases with
        | zero => simp [QCtx.effective]
        | succ j =>
          cases j using Fin.cases with
          | zero =>
            change Usage.effective (.used ⊤) (quantity A) ≤
              Usage.effective (.used (quantity A)) (quantity A)
            simp
          | succ k => exact le_rfl)
  simpa only [show Tm.rename id a = a from Tm.rename_id a] using h.rename id hw

/-- Simultaneous substitution preserves native quantitative typing. The proof
splits the substitution's resources and lifts it at normalized binder quantities;
it does not assume pointwise typing of zero-use entries. -/
theorem bsubst_nonempty {n : Nat} (a : Term Φ n) :
    ∀ {F : Fragment} {Δ : QCtx τ n} {e : ε} {A : τ}, HasType F Δ e a A →
      ∀ {m : Nat} {Γ : QCtx τ m} {σ : Fin n → Term Φ m},
        Substitution F Γ e σ Δ → Nonempty (HasType F Γ e (Tm.bsubst σ a) A) := by
  induction a with
  | fv x => exact nomatch x
  | bv i =>
    intro F Δ e A ht m Γ σ hσ
    cases ht with
    | var _ hi => exact ⟨hσ.lookup i hi⟩
  | op f a ih =>
    intro F Δ e A ht m Γ σ hσ
    cases ht with
    | op hf ha =>
      obtain ⟨h⟩ := ih ha hσ
      exact ⟨.op hf h⟩
  | let₁ a b ih ik =>
    intro F Δ e A ht m Γ σ hσ
    cases ht with
    | let₁ s ha hb =>
      obtain ⟨Γl, Γr, hs, ⟨hl⟩, ⟨hr⟩, _⟩ := hσ.split_nonempty s
      obtain ⟨ha'⟩ := ih ha hr
      obtain ⟨hb'⟩ := ik hb.normalizeBinder (hl.upNormalized _)
      exact ⟨.let₁ hs ha' hb'⟩
  | unit =>
    intro F Δ e A ht m Γ σ hσ
    cases ht with
    | unit hd => exact ⟨.unit (hσ.discardable hd)⟩
  | pair a b ih ik =>
    intro F Δ e A ht m Γ σ hσ
    cases ht with
    | pair s ha hb =>
      obtain ⟨Γl, Γr, hs, ⟨hl⟩, ⟨hr⟩, _⟩ := hσ.split_nonempty s
      obtain ⟨ha'⟩ := ih ha hl
      obtain ⟨hb'⟩ := ik hb hr
      exact ⟨.pair hs ha' hb'⟩
  | let₂ a b ih ik =>
    intro F Δ e A ht m Γ σ hσ
    cases ht with
    | let₂ s ha hb =>
      obtain ⟨Γl, Γr, hs, ⟨hl⟩, ⟨hr⟩, _⟩ := hσ.split_nonempty s
      obtain ⟨ha'⟩ := ih ha hr
      obtain ⟨hb'⟩ := ik hb.normalizeBinders₂ ((hl.upNormalized _).upNormalized _)
      exact ⟨.let₂ hs ha' hb'⟩
  | inl a ih =>
    intro F Δ e A ht m Γ σ hσ
    cases ht with
    | inl f ha =>
      obtain ⟨h⟩ := ih ha hσ
      exact ⟨.inl f h⟩
  | inr a ih =>
    intro F Δ e A ht m Γ σ hσ
    cases ht with
    | inr f ha =>
      obtain ⟨h⟩ := ih ha hσ
      exact ⟨.inr f h⟩
  | case a l r ih il ir =>
    intro F Δ e A ht m Γ σ hσ
    cases ht with
    | case f s ha hl hr =>
      obtain ⟨Γl, Γr, hs, ⟨hL⟩, ⟨hR⟩, _⟩ := hσ.split_nonempty s
      obtain ⟨ha'⟩ := ih ha hR
      obtain ⟨hl'⟩ := il hl.normalizeBinder (hL.upNormalized _)
      obtain ⟨hr'⟩ := ir hr.normalizeBinder (hL.upNormalized _)
      exact ⟨.case f hs ha' hl' hr'⟩
  | abort a ih =>
    intro F Δ e A ht m Γ σ hσ
    cases ht with
    | abort f ha =>
      obtain ⟨h⟩ := ih ha hσ
      exact ⟨.abort f h⟩
  | iter a b ih ik =>
    intro F Δ e A ht m Γ σ hσ
    cases ht with
    | iter f s hu he ha hb =>
      obtain ⟨Γl, Γr, hs, ⟨hl⟩, ⟨hr⟩, htop⟩ := hσ.split_nonempty s
      obtain ⟨ha'⟩ := ih ha hr
      obtain ⟨hb'⟩ := ik hb.normalizeBinder (hl.upNormalized _)
      exact ⟨.iter f hs (htop hu) he ha' hb'⟩

/-- The native typing action of a simultaneous quantitative substitution. -/
def bsubst {F : Fragment} {n m : Nat} {Δ : QCtx τ n} {Γ : QCtx τ m} {e : ε}
    {a : Term Φ n} {A : τ} {σ : Fin n → Term Φ m}
    (h : HasType F Δ e a A) (hσ : Substitution F Γ e σ Δ) :
    HasType F Γ e (Tm.bsubst σ a) A := Classical.choice (bsubst_nonempty a h hσ)

end HasType

end Silmaril.Isotope.Refinement
