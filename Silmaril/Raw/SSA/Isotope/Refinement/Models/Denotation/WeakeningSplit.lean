module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Slots

@[expose] public section

namespace Silmaril.Isotope.Refinement.Models

open CategoryTheory
open scoped MonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace SeqModel
/-- The tensor unit is terminal among pure computations with affine source. -/
theorem pure_to_unit_unique (M : SeqModel.{u,v,w,r} τ Φ ε) {A : τ}
    (f : M.toSeqData.Hom A Silmaril.unit) (hf : M.toSeqData.hasEffect ⊥ f)
    (ha : Quantity.affine ≤ quantity A) : f = M.toSeqData.discard A ha := by
  have h := M.toSeqData.pure_discard_natural f hf ha (by rw [TypeQuantity.unit_quantity]; exact le_top)
  rw [M.discard_unit, M.toSeqData.compose_identity] at h
  exact h
end SeqModel

namespace Denotation
variable (M : SeqModel.{u,v,w,r} τ Φ ε)

/-- Empty-target special casing in the interpreter agrees with the recursive
operation that drops one final slot. -/
theorem weakenPure_skip {n m : Nat} {Γ : QCtx τ n} {Δ : QCtx τ m}
    {ρ : Fin m → Fin n} (h : QCtx.Weakening Γ Δ ρ) {A : τ} {q : Usage}
    (hq : Usage.zero ≤ Usage.effective q (quantity A)) :
    weakenPure M.toSeqData (QCtx.Weakening.skip h hq) =
      weakenSlot M.toSeqData (weakenPure M.toSeqData h) (q' := .zero) hq := by
  cases m with
  | succ m => cases q <;> rfl
  | zero =>
    apply Subtype.ext
    change weaken M.toSeqData (QCtx.Weakening.skip h hq) = _
    rw [weaken_nil]
    exact (M.pure_to_unit_unique _ (weakenSlot M.toSeqData (weakenPure M.toSeqData h) (q' := .zero) hq).2 _).symm

/-- The retained-slot constructor computes by quantity restriction of that slot. -/
theorem weakenPure_cons {n m : Nat} {Γ : QCtx τ n} {Δ : QCtx τ m}
    {ρ : Fin m → Fin n} (h : QCtx.Weakening Γ Δ ρ) {A : τ} {q q' : Usage}
    (hq : Usage.effective q' (quantity A) ≤ Usage.effective q (quantity A)) :
    weakenPure M.toSeqData (QCtx.Weakening.cons h hq) =
      weakenSlot M.toSeqData (weakenPure M.toSeqData h) hq := by
  rfl

/-- Any two pure maps to a packed empty context agree. -/
theorem pure_empty_unique {n : Nat} {Γ : QCtx τ n} {Δ : QCtx τ 0}
    (h : Γ.Discardable) (f g : PureHom M.toSeqData (packed Γ) (packed Δ)) : f = g := by
  apply Subtype.ext
  exact (M.pure_to_unit_unique f.1 f.2 (discardable_quantity h)).trans
    (M.pure_to_unit_unique g.1 g.2 (discardable_quantity h)).symm


/-- Weakening commutes with any compatible splitting choices. In particular,
this applies to the witnesses returned by `QCtx.Weakening.split`. -/
theorem weakenPure_split {n m : Nat} {Γ Γl Γr : QCtx τ n} {Δ Δl Δr : QCtx τ m}
    {ρ : Fin m → Fin n} (h : QCtx.Weakening Γ Δ ρ)
    (s : QCtx.Split Γ Γl Γr) (t : QCtx.Split Δ Δl Δr)
    (hl : QCtx.Weakening Γl Δl ρ) (hr : QCtx.Weakening Γr Δr ρ) :
    pureCompose M.toSeqData (weakenPure M.toSeqData h) (splitPure M.toSeqData t) =
      pureCompose M.toSeqData (splitPure M.toSeqData s)
        (pureTensor M.toSeqData (weakenPure M.toSeqData hl) (weakenPure M.toSeqData hr)) := by
  induction h with
  | nil =>
    change 𝟙 (𝟙_ M.toSeqData.PureObject) ≫ (CategoryTheory.MonoidalCategory.leftUnitor (𝟙_ M.toSeqData.PureObject)).inv =
      (CategoryTheory.MonoidalCategory.leftUnitor (𝟙_ M.toSeqData.PureObject)).inv ≫
        (𝟙 (𝟙_ M.toSeqData.PureObject) ⊗ₘ 𝟙 (𝟙_ M.toSeqData.PureObject))
    simp
  | @cons n m Γ Δ ρ A q q' h hq ih =>
    let Γlt : QCtx τ n := fun i => Γl i.succ
    let Γrt : QCtx τ n := fun i => Γr i.succ
    let Δlt : QCtx τ m := fun i => Δl i.succ
    let Δrt : QCtx τ m := fun i => Δr i.succ
    have hΓl : Γlt.snoc A (Γl 0).2 = Γl := by rw [← (show (Γl 0).1 = A from (s 0).1)]; exact QCtx.snoc_tail Γl
    have hΓr : Γrt.snoc A (Γr 0).2 = Γr := by rw [← (show (Γr 0).1 = A from (s 0).2.1)]; exact QCtx.snoc_tail Γr
    have hΔl : Δlt.snoc A (Δl 0).2 = Δl := by rw [← (show (Δl 0).1 = A from (t 0).1)]; exact QCtx.snoc_tail Δl
    have hΔr : Δrt.snoc A (Δr 0).2 = Δr := by rw [← (show (Δr 0).1 = A from (t 0).2.1)]; exact QCtx.snoc_tail Δr
    let P (p : (QCtx τ (n+1) × QCtx τ (n+1)) × (QCtx τ (m+1) × QCtx τ (m+1))) :=
      ∀ (ss : QCtx.Split (Γ.snoc A q) p.1.1 p.1.2)
        (tt : QCtx.Split (Δ.snoc A q') p.2.1 p.2.2)
        (wl : QCtx.Weakening p.1.1 p.2.1 (Fin.cases 0 (fun i => (ρ i).succ)))
        (wr : QCtx.Weakening p.1.2 p.2.2 (Fin.cases 0 (fun i => (ρ i).succ))),
        pureCompose M.toSeqData (weakenPure M.toSeqData (QCtx.Weakening.cons h hq)) (splitPure M.toSeqData tt) =
          pureCompose M.toSeqData (splitPure M.toSeqData ss)
            (pureTensor M.toSeqData (weakenPure M.toSeqData wl) (weakenPure M.toSeqData wr))
    have hall : P ((Γlt.snoc A (Γl 0).2, Γrt.snoc A (Γr 0).2),
        (Δlt.snoc A (Δl 0).2, Δrt.snoc A (Δr 0).2)) := by
      intro ss tt wl wr
      have st : QCtx.Split Γ Γlt Γrt := fun i => ss i.succ
      have tt' : QCtx.Split Δ Δlt Δrt := fun i => tt i.succ
      have wlt : QCtx.Weakening Γlt Δlt ρ := weakening_cons_tail wl rfl
      have wrt : QCtx.Weakening Γrt Δrt ρ := weakening_cons_tail wr rfl
      have hql : Usage.effective (Δl 0).2 (quantity A) ≤ Usage.effective (Γl 0).2 (quantity A) := wl.effective_le 0
      have hqr : Usage.effective (Δr 0).2 (quantity A) ≤ Usage.effective (Γr 0).2 (quantity A) := wr.effective_le 0
      exact weakenSlot_splitSlot M.toSeqData (splitPure M.toSeqData st) (splitPure M.toSeqData tt')
        (weakenPure M.toSeqData h) (weakenPure M.toSeqData wlt) (weakenPure M.toSeqData wrt)
        (ih st tt' wlt wrt) hq (ss 0).2.2 (tt 0).2.2 hql hqr
    exact ((congrArg P (congrArg₂ Prod.mk (congrArg₂ Prod.mk hΓl hΓr)
      (congrArg₂ Prod.mk hΔl hΔr))).mp hall) s t hl hr
  | @skip n m Γ Δ ρ A q h hq ih =>
    let Γlt : QCtx τ n := fun i => Γl i.succ
    let Γrt : QCtx τ n := fun i => Γr i.succ
    have hΓl : Γlt.snoc A (Γl 0).2 = Γl := by rw [← (show (Γl 0).1 = A from (s 0).1)]; exact QCtx.snoc_tail Γl
    have hΓr : Γrt.snoc A (Γr 0).2 = Γr := by rw [← (show (Γr 0).1 = A from (s 0).2.1)]; exact QCtx.snoc_tail Γr
    let P (p : QCtx τ (n+1) × QCtx τ (n+1)) :=
      ∀ (ss : QCtx.Split (Γ.snoc A q) p.1 p.2)
        (wl : QCtx.Weakening p.1 Δl (fun i => (ρ i).succ))
        (wr : QCtx.Weakening p.2 Δr (fun i => (ρ i).succ)),
        pureCompose M.toSeqData (weakenPure M.toSeqData (QCtx.Weakening.skip h hq)) (splitPure M.toSeqData t) =
          pureCompose M.toSeqData (splitPure M.toSeqData ss)
            (pureTensor M.toSeqData (weakenPure M.toSeqData wl) (weakenPure M.toSeqData wr))
    have hall : P (Γlt.snoc A (Γl 0).2, Γrt.snoc A (Γr 0).2) := by
      intro ss wl wr
      have st : QCtx.Split Γ Γlt Γrt := fun i => ss i.succ
      have wlt : QCtx.Weakening Γlt Δl ρ := weakening_skip_tail wl (fun i => Fin.succ_ne_zero _)
      have wrt : QCtx.Weakening Γrt Δr ρ := weakening_skip_tail wr (fun i => Fin.succ_ne_zero _)
      have hql : Usage.zero ≤ Usage.effective (Γl 0).2 (quantity A) := wl.omitted 0 (fun i => Fin.succ_ne_zero _)
      have hqr : Usage.zero ≤ Usage.effective (Γr 0).2 (quantity A) := wr.omitted 0 (fun i => Fin.succ_ne_zero _)
      have el : weakenPure M.toSeqData wl = weakenSlot M.toSeqData (weakenPure M.toSeqData wlt) (q' := .zero) hql :=
        weakenPure_skip M wlt hql
      have er : weakenPure M.toSeqData wr = weakenSlot M.toSeqData (weakenPure M.toSeqData wrt) (q' := .zero) hqr :=
        weakenPure_skip M wrt hqr
      rw [weakenPure_skip, el, er]
      exact weakenSlot_splitSlot M.toSeqData (splitPure M.toSeqData st) (splitPure M.toSeqData t)
        (weakenPure M.toSeqData h) (weakenPure M.toSeqData wlt) (weakenPure M.toSeqData wrt)
        (ih st t wlt wrt) (q' := .zero) hq (ss 0).2.2 (.left .zero) hql hqr
    exact ((congrArg P (congrArg₂ Prod.mk hΓl hΓr)).mp hall) s hl hr

theorem weaken_split {n m : Nat} {Γ Γl Γr : QCtx τ n} {Δ Δl Δr : QCtx τ m}
    {ρ : Fin m → Fin n} (h : QCtx.Weakening Γ Δ ρ)
    (s : QCtx.Split Γ Γl Γr) (t : QCtx.Split Δ Δl Δr)
    (hl : QCtx.Weakening Γl Δl ρ) (hr : QCtx.Weakening Γr Δr ρ) :
    M.toSeqData.compose (weaken M.toSeqData h) (split M.toSeqData t) =
      M.toSeqData.compose (split M.toSeqData s)
        (M.toSeqData.tensor (weaken M.toSeqData hl) (weaken M.toSeqData hr)) :=
  congrArg Subtype.val (weakenPure_split M h s t hl hr)

end Denotation
end Silmaril.Isotope.Refinement.Models
