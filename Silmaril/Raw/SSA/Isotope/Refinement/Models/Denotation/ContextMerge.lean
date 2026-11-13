module

public import Silmaril.Raw.SSA.Isotope.Refinement.ContextMerge
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.TypeMerge
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.TypeMapWeakening

/-! # Pure maps into common contexts with matching retained positions -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {α : Type u} [DecidableEq α] [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : CaseData.{u,v,w,r} (Ty α) Φ ε)

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise pure type comparisons combine into maps of packed contexts.
The alignment premise prevents silently manufacturing or discarding a slot. -/
def mergeContext : {n : Nat} → (Γ Δ : QCtx (Ty α) n) → QCtx.Aligned Γ Δ →
    PureHom M.toSeqData (packed Γ) (packed (QCtx.merge Γ Δ)) ×
      PureHom M.toSeqData (packed Δ) (packed (QCtx.merge Γ Δ)) := by
  intro n
  induction n with
  | zero => intro Γ Δ _; exact ⟨pureIdentity M _, pureIdentity M _⟩
  | succ n ih =>
    intro Γ Δ h
    have ht := ih (fun i => Γ i.succ) (fun i => Δ i.succ) h.tail
    cases hΓ : (Γ 0).2 with
    | zero =>
      have hΔ := (h 0).mp hΓ
      simp only [packed, QCtx.merge, hΓ, hΔ, Usage.zero_mul]
      exact ht
    | used q =>
      cases hΔ : (Δ 0).2 with
      | zero => exact False.elim (Usage.noConfusion (hΓ.symm.trans ((h 0).mpr hΔ)))
      | used r =>
        simp only [packed, QCtx.merge, hΓ, hΔ, Usage.used_mul_used]
        exact (pureTensor M.toSeqData ht.1 (mergeArrows M (Γ 0).1 (Δ 0).1).1,
          pureTensor M.toSeqData ht.2 (mergeArrows M (Γ 0).1 (Δ 0).1).2)

set_option backward.isDefEq.respectTransparency false in
/-- The comparison pair is the generic pointwise context-map construction. -/
theorem mergeContext_eq_contextTypeMap {n : Nat} (Γ Δ : QCtx (Ty α) n) (h : QCtx.Aligned Γ Δ) :
    mergeContext M Γ Δ h =
      (contextTypeMap M.toSeqData (fun i => (Γ i).1) (fun i => mergeType (Γ i).1 (Δ i).1)
        (fun i => (Γ i).2) (fun i => (Γ i).2 * (Δ i).2)
        (fun i => (mergeArrows M (Γ i).1 (Δ i).1).1) (fun i => Usage.merge_zero_left _ _ (h i)),
       contextTypeMap M.toSeqData (fun i => (Δ i).1) (fun i => mergeType (Γ i).1 (Δ i).1)
        (fun i => (Δ i).2) (fun i => (Γ i).2 * (Δ i).2)
        (fun i => (mergeArrows M (Γ i).1 (Δ i).1).2) (fun i => Usage.merge_zero_right _ _ (h i))) := by
  induction Γ using QCtx.inductionOn with
  | nil => rfl
  | @snoc n Γ A q ih =>
    generalize hb : (Δ 0).1 = B
    obtain ⟨Δ, r, rfl⟩ := QCtx.exists_snoc_of_type Δ B hb
    have ht : QCtx.Aligned Γ Δ := h.tail
    cases q with
    | zero =>
      have hr : r = .zero := (h 0).mp rfl
      subst r
      change mergeContext M Γ Δ ht =
        (retainTypeMap M.toSeqData (q := .zero) (r := .zero) _ (mergeArrows M A B).1 _,
          retainTypeMap M.toSeqData (q := .zero) (r := .zero) _ (mergeArrows M A B).2 _)
      simp only [retainTypeMap_zero]
      exact ih Δ ht
    | used q =>
      cases r with
      | zero => exact False.elim (Usage.noConfusion ((h 0).mpr rfl))
      | used r =>
        change (pureTensor M.toSeqData (mergeContext M Γ Δ ht).1 (mergeArrows M A B).1,
            pureTensor M.toSeqData (mergeContext M Γ Δ ht).2 (mergeArrows M A B).2) =
          (retainTypeMap M.toSeqData (q := .used q) (r := .used (q ⊓ r)) _ (mergeArrows M A B).1 _,
            retainTypeMap M.toSeqData (q := .used r) (r := .used (q ⊓ r)) _ (mergeArrows M A B).2 _)
        simp only [retainTypeMap_used]
        rw [ih Δ ht]
        rfl

set_option backward.isDefEq.respectTransparency false in
/-- The left common-context comparison commutes with pointwise aligned splits. -/
theorem mergeContext_split_left {n : Nat} (A B : Fin n → Ty α)
    (q ql qr r rl rr : Fin n → Usage)
    (s : ∀ i, QCtx.SlotSplit (A i) (q i) (ql i) (qr i))
    (t : ∀ i, QCtx.SlotSplit (B i) (r i) (rl i) (rr i))
    (h : ∀ i, q i = .zero ↔ r i = .zero)
    (hl : ∀ i, ql i = .zero ↔ rl i = .zero) (hr : ∀ i, qr i = .zero ↔ rr i = .zero) :
    pureCompose M.toSeqData
      (mergeContext M (fun i => (A i, q i)) (fun i => (B i, r i)) h).1
      (splitPure M.toSeqData ((pointwiseSplit A q ql qr s).merge (pointwiseSplit B r rl rr t) hl hr)) =
    pureCompose M.toSeqData (splitPure M.toSeqData (pointwiseSplit A q ql qr s))
      (pureTensor M.toSeqData
        (mergeContext M (fun i => (A i, ql i)) (fun i => (B i, rl i)) hl).1
        (mergeContext M (fun i => (A i, qr i)) (fun i => (B i, rr i)) hr).1) := by
  simp only [mergeContext_eq_contextTypeMap]
  exact contextTypeMap_split M.toSeqData A (fun i => mergeType (A i) (B i))
    q ql qr (fun i => q i * r i) (fun i => ql i * rl i) (fun i => qr i * rr i)
    (fun i => (mergeArrows M (A i) (B i)).1) s
    (fun i => (s i).merge (t i) (hl i) (hr i))
    (fun i => Usage.merge_zero_left _ _ (h i))
    (fun i => Usage.merge_zero_left _ _ (hl i)) (fun i => Usage.merge_zero_left _ _ (hr i))

set_option backward.isDefEq.respectTransparency false in
/-- The right common-context comparison commutes with pointwise aligned splits. -/
theorem mergeContext_split_right {n : Nat} (A B : Fin n → Ty α)
    (q ql qr r rl rr : Fin n → Usage)
    (s : ∀ i, QCtx.SlotSplit (A i) (q i) (ql i) (qr i))
    (t : ∀ i, QCtx.SlotSplit (B i) (r i) (rl i) (rr i))
    (h : ∀ i, q i = .zero ↔ r i = .zero)
    (hl : ∀ i, ql i = .zero ↔ rl i = .zero) (hr : ∀ i, qr i = .zero ↔ rr i = .zero) :
    pureCompose M.toSeqData
      (mergeContext M (fun i => (A i, q i)) (fun i => (B i, r i)) h).2
      (splitPure M.toSeqData ((pointwiseSplit A q ql qr s).merge (pointwiseSplit B r rl rr t) hl hr)) =
    pureCompose M.toSeqData (splitPure M.toSeqData (pointwiseSplit B r rl rr t))
      (pureTensor M.toSeqData
        (mergeContext M (fun i => (A i, ql i)) (fun i => (B i, rl i)) hl).2
        (mergeContext M (fun i => (A i, qr i)) (fun i => (B i, rr i)) hr).2) := by
  simp only [mergeContext_eq_contextTypeMap]
  exact contextTypeMap_split M.toSeqData B (fun i => mergeType (A i) (B i))
    r rl rr (fun i => q i * r i) (fun i => ql i * rl i) (fun i => qr i * rr i)
    (fun i => (mergeArrows M (A i) (B i)).2) t
    (fun i => (s i).merge (t i) (hl i) (hr i))
    (fun i => Usage.merge_zero_right _ _ (h i))
    (fun i => Usage.merge_zero_right _ _ (hl i)) (fun i => Usage.merge_zero_right _ _ (hr i))

/-- Split naturality for arbitrary native contexts, on the left comparison map. -/
theorem mergeContext_split_fst {n : Nat} {Γ Γl Γr Δ Δl Δr : QCtx (Ty α) n}
    (s : QCtx.Split Γ Γl Γr) (t : QCtx.Split Δ Δl Δr)
    (h : QCtx.Aligned Γ Δ) (hl : QCtx.Aligned Γl Δl) (hr : QCtx.Aligned Γr Δr) :
    pureCompose M.toSeqData (mergeContext M Γ Δ h).1 (splitPure M.toSeqData (s.merge t hl hr)) =
      pureCompose M.toSeqData (splitPure M.toSeqData s)
        (pureTensor M.toSeqData (mergeContext M Γl Δl hl).1 (mergeContext M Γr Δr hr).1) := by
  obtain ⟨ql, qr, rfl, rfl⟩ := s.exists_quantities
  obtain ⟨rl, rr, rfl, rfl⟩ := t.exists_quantities
  exact mergeContext_split_left M (fun i => (Γ i).1) (fun i => (Δ i).1)
    (fun i => (Γ i).2) ql qr (fun i => (Δ i).2) rl rr
    (fun i => (s i).2.2) (fun i => (t i).2.2) h hl hr

/-- Split naturality for arbitrary native contexts, on the right comparison map. -/
theorem mergeContext_split_snd {n : Nat} {Γ Γl Γr Δ Δl Δr : QCtx (Ty α) n}
    (s : QCtx.Split Γ Γl Γr) (t : QCtx.Split Δ Δl Δr)
    (h : QCtx.Aligned Γ Δ) (hl : QCtx.Aligned Γl Δl) (hr : QCtx.Aligned Γr Δr) :
    pureCompose M.toSeqData (mergeContext M Γ Δ h).2 (splitPure M.toSeqData (s.merge t hl hr)) =
      pureCompose M.toSeqData (splitPure M.toSeqData t)
        (pureTensor M.toSeqData (mergeContext M Γl Δl hl).2 (mergeContext M Γr Δr hr).2) := by
  obtain ⟨ql, qr, rfl, rfl⟩ := s.exists_quantities
  obtain ⟨rl, rr, rfl, rfl⟩ := t.exists_quantities
  exact mergeContext_split_right M (fun i => (Γ i).1) (fun i => (Δ i).1)
    (fun i => (Γ i).2) ql qr (fun i => (Δ i).2) rl rr
    (fun i => (s i).2.2) (fun i => (t i).2.2) h hl hr

set_option backward.isDefEq.respectTransparency false in
/-- The left comparison commutes with identity-index resource weakenings. -/
theorem mergeContext_weaken_fst {n : Nat} {Γ Γ' Δ Δ' : QCtx (Ty α) n}
    (w : QCtx.Weakening Γ Γ' id) (v : QCtx.Weakening Δ Δ' id)
    (wm : QCtx.Weakening (QCtx.merge Γ Δ) (QCtx.merge Γ' Δ') id)
    (h : QCtx.Aligned Γ Δ) (h' : QCtx.Aligned Γ' Δ') :
    pureCompose M.toSeqData (mergeContext M Γ Δ h).1 (weakenPure M.toSeqData wm) =
      pureCompose M.toSeqData (weakenPure M.toSeqData w) (mergeContext M Γ' Δ' h').1 := by
  obtain ⟨q', rfl⟩ := w.exists_quantities
  obtain ⟨r', rfl⟩ := v.exists_quantities
  simp only [mergeContext_eq_contextTypeMap]
  exact contextTypeMap_weaken M.toSeqData (fun i => (Γ i).1)
    (fun i => mergeType (Γ i).1 (Δ i).1)
    (fun i => (Γ i).2) q' (fun i => (Γ i).2 * (Δ i).2) (fun i => q' i * r' i)
    (fun i => (mergeArrows M (Γ i).1 (Δ i).1).1)
    (fun i => Usage.merge_zero_left _ _ (h i))
    (fun i => Usage.merge_zero_left _ _ (h' i)) (fun i => w.effective_le i) (fun i => wm.effective_le i)

set_option backward.isDefEq.respectTransparency false in
/-- The right comparison commutes with identity-index resource weakenings. -/
theorem mergeContext_weaken_snd {n : Nat} {Γ Γ' Δ Δ' : QCtx (Ty α) n}
    (w : QCtx.Weakening Γ Γ' id) (v : QCtx.Weakening Δ Δ' id)
    (wm : QCtx.Weakening (QCtx.merge Γ Δ) (QCtx.merge Γ' Δ') id)
    (h : QCtx.Aligned Γ Δ) (h' : QCtx.Aligned Γ' Δ') :
    pureCompose M.toSeqData (mergeContext M Γ Δ h).2 (weakenPure M.toSeqData wm) =
      pureCompose M.toSeqData (weakenPure M.toSeqData v) (mergeContext M Γ' Δ' h').2 := by
  obtain ⟨q', rfl⟩ := w.exists_quantities
  obtain ⟨r', rfl⟩ := v.exists_quantities
  simp only [mergeContext_eq_contextTypeMap]
  exact contextTypeMap_weaken M.toSeqData (fun i => (Δ i).1)
    (fun i => mergeType (Γ i).1 (Δ i).1)
    (fun i => (Δ i).2) r' (fun i => (Γ i).2 * (Δ i).2) (fun i => q' i * r' i)
    (fun i => (mergeArrows M (Γ i).1 (Δ i).1).2)
    (fun i => Usage.merge_zero_right _ _ (h i))
    (fun i => Usage.merge_zero_right _ _ (h' i)) (fun i => v.effective_le i) (fun i => wm.effective_le i)

set_option backward.isDefEq.respectTransparency false in
/-- Comparing a context with itself gives the identity structural map. -/
theorem mergeContext_self {n : Nat} (Γ : QCtx (Ty α) n) :
    HEq (mergeContext M Γ Γ (QCtx.Aligned.refl Γ))
      (pureIdentity M (packed Γ), pureIdentity M (packed Γ)) := by
  induction Γ using QCtx.inductionOn with
  | nil => rfl
  | @snoc n Γ A q ih =>
    cases q with
    | zero => exact ih
    | used q =>
      have ht := purePair_components_heq M (congrArg packed (QCtx.merge_self Γ)) ih
      have hA := purePair_components_heq M (mergeType_self A) (mergeArrows_self M A)
      change HEq
        (pureTensor M.toSeqData (mergeContext M Γ Γ _).1 (mergeArrows M A A).1,
          pureTensor M.toSeqData (mergeContext M Γ Γ _).2 (mergeArrows M A A).2) _
      exact purePair_heq M (congrArg packed (QCtx.merge_self (Γ.snoc A (.used q))))
        ((pureTensor_target_heq M (congrArg packed (QCtx.merge_self Γ)) (mergeType_self A) ht.1 hA.1).trans
          (heq_of_eq (pureTensor_identity M (packed Γ) A)))
        ((pureTensor_target_heq M (congrArg packed (QCtx.merge_self Γ)) (mergeType_self A) ht.2 hA.2).trans
          (heq_of_eq (pureTensor_identity M (packed Γ) A)))

end Silmaril.Isotope.Refinement.Models.Denotation
