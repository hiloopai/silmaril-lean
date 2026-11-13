module

public import Silmaril.Raw.SSA.Isotope.Refinement.TypeMerge
public import Silmaril.Raw.SSA.Isotope.Refinement.SupportSplitting

/-! # Common quantitative contexts for hidden type comparisons -/

@[expose] public section
namespace Silmaril.Isotope.Refinement
universe u v w

namespace Usage
/-- Multiplication retains any effective nonzero bound available on both sides. -/
theorem merge_effective (q r : Usage) (A B p : Quantity)
    (hq : used p ≤ effective q A) (hr : used p ≤ effective r B) :
    used p ≤ effective (q * r) (A ⊓ B) := by decide +revert

/-- Discardability survives a common comparison of quantities and types. -/
theorem merge_discardable (q r : Usage) (A B : Quantity)
    (hq : zero ≤ effective q A) (hr : zero ≤ effective r B) :
    zero ≤ effective (q * r) (A ⊓ B) := by decide +revert

theorem merge_nonzero (q r : Usage) (hq : q ≠ zero) (hr : r ≠ zero) : q * r ≠ zero := by
  cases q <;> cases r <;> simp_all

/-- Aligned quantities and their product have the same retained status. -/
theorem merge_zero_left (q r : Usage) (h : q = zero ↔ r = zero) :
    q = zero ↔ q * r = zero := by cases q <;> cases r <;> simp_all

theorem merge_zero_right (q r : Usage) (h : q = zero ↔ r = zero) :
    r = zero ↔ q * r = zero := h.symm.trans (merge_zero_left q r h)

/-- Omitting a slot can only relax this common linearity bound. -/
theorem merge_linearity (q r : Usage) (A B : Quantity) :
    linearity q A ⊓ linearity r B ≤ linearity (q * r) (A ⊓ B) := by decide +revert

@[simp] theorem mul_self (q : Usage) : q * q = q := by cases q <;> simp
end Usage

namespace QCtx
variable {α : Type u} [DecidableEq α] {n : Nat}

/-- Combine retained quantities and covariantly compare their value types. -/
def merge (Γ Δ : QCtx (Ty α) n) : QCtx (Ty α) n := fun i =>
  (mergeType (Γ i).1 (Δ i).1, (Γ i).2 * (Δ i).2)

@[simp] theorem merge_self (Γ : QCtx (Ty α) n) : merge Γ Γ = Γ := by
  funext i
  simp [merge]

@[simp] theorem merge_snoc (Γ Δ : QCtx (Ty α) n) (A B : Ty α) (q r : Usage) :
    merge (Γ.snoc A q) (Δ.snoc B r) = (merge Γ Δ).snoc (mergeType A B) (q * r) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- Contexts have the same retained positions; their types and nonzero allowances may differ. -/
def Aligned (Γ Δ : QCtx (Ty α) n) : Prop := ∀ i, (Γ i).2 = .zero ↔ (Δ i).2 = .zero

omit [DecidableEq α] in
theorem Aligned.refl (Γ : QCtx (Ty α) n) : Aligned Γ Γ := fun _ => Iff.rfl

omit [DecidableEq α] in
theorem Aligned.symm {Γ Δ : QCtx (Ty α) n} (h : Aligned Γ Δ) : Aligned Δ Γ := fun i => (h i).symm

omit [DecidableEq α] in
theorem Aligned.tail {Γ Δ : QCtx (Ty α) (n+1)} (h : Aligned Γ Δ) :
    Aligned (fun i => Γ i.succ) (fun i => Δ i.succ) := fun i => h i.succ

omit [DecidableEq α] in
/-- Retaining a common binder quantity preserves alignment, even when types differ. -/
theorem Aligned.snoc {Γ Δ : QCtx (Ty α) n} (h : Aligned Γ Δ) (A B : Ty α) (q : Usage := .used ⊤) :
    Aligned (Γ.snoc A q) (Δ.snoc B q) := fun i => Fin.cases Iff.rfl h i

@[simp] theorem merge_restrict (Γ Δ : QCtx (Ty α) n) (p : Fin n → Bool) :
    merge (restrict Γ p) (restrict Δ p) = restrict (merge Γ Δ) p := by
  funext i
  cases hi : p i <;> simp [merge, restrict, hi]

variable [HasQuantity α]

/-- A common context can discard a position whenever both source contexts can. -/
theorem weakening_merge_restrict (Γ Δ : QCtx (Ty α) n) (p : Fin n → Bool)
    (hΓ : ∀ i, p i = false → Usage.zero ≤ effective Γ i)
    (hΔ : ∀ i, p i = false → Usage.zero ≤ effective Δ i) :
    Weakening (merge Γ Δ) (merge (restrict Γ p) (restrict Δ p)) id := by
  rw [merge_restrict]
  apply weakening_restrict
  intro i hi
  change Usage.zero ≤ Usage.effective ((Γ i).2 * (Δ i).2) (quantity (mergeType (Γ i).1 (Δ i).1))
  rw [quantity_mergeType]
  exact Usage.merge_discardable _ _ _ _ (hΓ i hi) (hΔ i hi)

/-- Two actual support weakenings induce the common-context support weakening. -/
theorem weakening_merge_of_restrict {Γ Δ : QCtx (Ty α) n} {p : Fin n → Bool}
    (w : Weakening Γ (restrict Γ p) id) (v : Weakening Δ (restrict Δ p) id) :
    Weakening (merge Γ Δ) (merge (restrict Γ p) (restrict Δ p)) id := by
  apply weakening_merge_restrict
  · intro i hi
    simpa [effective, restrict, hi] using w.effective_le i
  · intro i hi
    simpa [effective, restrict, hi] using v.effective_le i

omit [DecidableEq α] [HasQuantity α] in
/-- A mask with nonzero retained slots determines a shared support alignment. -/
theorem Aligned.restrict_of_nonzero (Γ Δ : QCtx (Ty α) n) (p : Fin n → Bool)
    (hΓ : ∀ i, p i = true → (Γ i).2 ≠ .zero)
    (hΔ : ∀ i, p i = true → (Δ i).2 ≠ .zero) :
    Aligned (restrict Γ p) (restrict Δ p) := by
  intro i
  cases hp : p i
  · simp [restrict, hp]
  · simp only [restrict, hp, ↓reduceIte]
    exact ⟨fun he => False.elim (hΓ i hp he), fun he => False.elim (hΔ i hp he)⟩

/-- Quantitative support conditions are stable under pointwise comparison. -/
theorem SlotAllows.merge {A B : Ty α} {q r : Usage} {used : Bool}
    (h : SlotAllows A q used) (k : SlotAllows B r used) :
    SlotAllows (mergeType A B) (q * r) used := by
  constructor
  · intro hu
    exact Usage.merge_nonzero q r (h.1 hu) (k.1 hu)
  · intro hu
    rw [quantity_mergeType]
    exact Usage.merge_discardable q r (quantity A) (quantity B) (h.2 hu) (k.2 hu)

theorem Discardable.merge {Γ Δ : QCtx (Ty α) n} (h : Γ.Discardable) (k : Δ.Discardable) :
    (QCtx.merge Γ Δ).Discardable := by
  intro i
  change Usage.zero ≤ Usage.effective ((Γ i).2 * (Δ i).2) (quantity (mergeType (Γ i).1 (Δ i).1))
  rw [quantity_mergeType]
  exact Usage.merge_discardable _ _ _ _ (h i) (k i)

theorem VarAllowed.merge {Γ Δ : QCtx (Ty α) n} {i : Fin n} (h : Γ.VarAllowed i) (k : Δ.VarAllowed i) :
    (QCtx.merge Γ Δ).VarAllowed i := by
  constructor
  · simp only [Usage.effective_linear]
    change Usage.used .linear ≤ Usage.effective ((Γ i).2 * (Δ i).2) (quantity (mergeType (Γ i).1 (Δ i).1))
    rw [quantity_mergeType]
    exact Usage.merge_effective _ _ _ _ _ (by simpa only [Usage.effective_linear, QCtx.effective] using h.1)
      (by simpa only [Usage.effective_linear, QCtx.effective] using k.1)
  · intro j hj
    change Usage.zero ≤ Usage.effective ((Γ j).2 * (Δ j).2) (quantity (mergeType (Γ j).1 (Δ j).1))
    rw [quantity_mergeType]
    exact Usage.merge_discardable _ _ _ _ (h.2 j hj) (k.2 j hj)

/-- A context comparison retains the quantity bounds that both sources permit. -/
theorem linearity_merge (Γ Δ : QCtx (Ty α) n) :
    Γ.linearity ⊓ Δ.linearity ≤ (merge Γ Δ).linearity := by
  apply le_linearity_iff.mpr
  intro i
  have hΓ := (le_linearity_iff.mp (le_refl Γ.linearity)) i
  have hΔ := (le_linearity_iff.mp (le_refl Δ.linearity)) i
  have hh := Usage.merge_linearity (Γ i).2 (Δ i).2 (quantity (Γ i).1) (quantity (Δ i).1)
  exact (inf_le_inf hΓ hΔ).trans (by simpa [merge] using hh)

theorem merge_unrestricted {Γ Δ : QCtx (Ty α) n} (h : Γ.linearity = ⊤) (k : Δ.linearity = ⊤) :
    (merge Γ Δ).linearity = ⊤ := top_le_iff.mp (by simpa [h, k] using linearity_merge Γ Δ)

omit [DecidableEq α] [HasQuantity α] in
theorem Aligned.restrict {Γ Δ : QCtx (Ty α) n} (h : Aligned Γ Δ) (p : Fin n → Bool) :
    Aligned (QCtx.restrict Γ p) (QCtx.restrict Δ p) := by
  intro i
  cases hi : p i <;> simp only [QCtx.restrict, hi, ↓reduceIte]
  · exact Iff.rfl
  · exact h i

/-- Splits with matching retained positions combine into a valid common split. -/
theorem SlotSplit.merge {A B : Ty α} {q ql qr r rl rr : Usage}
    (s : SlotSplit A q ql qr) (t : SlotSplit B r rl rr)
    (hl : ql = .zero ↔ rl = .zero) (hr : qr = .zero ↔ rr = .zero) :
    SlotSplit (mergeType A B) (q * r) (ql * rl) (qr * rr) := by
  cases s with
  | left =>
    cases t with
    | left => simpa using (SlotSplit.left (A := mergeType A B) (q * r))
    | right =>
      have hq : q = .zero := hl.mpr rfl
      have hr' : r = .zero := hr.mp rfl
      subst q
      subst r
      exact .left .zero
    | both hc =>
      have hr' : r = .zero := hr.mp rfl
      subst r
      simpa using (SlotSplit.left (A := mergeType A B) .zero)
  | right =>
    cases t with
    | left =>
      have hq : q = .zero := hr.mpr rfl
      have hr' : r = .zero := hl.mp rfl
      subst q
      subst r
      exact .left .zero
    | right => simpa using (SlotSplit.right (A := mergeType A B) (q * r))
    | both hc =>
      have hr' : r = .zero := hl.mp rfl
      subst r
      simpa using (SlotSplit.left (A := mergeType A B) .zero)
  | both hc =>
    cases t with
    | left =>
      have hq : q = .zero := hr.mpr rfl
      subst q
      simpa using (SlotSplit.left (A := mergeType A B) .zero)
    | right =>
      have hq : q = .zero := hl.mpr rfl
      subst q
      simpa using (SlotSplit.left (A := mergeType A B) .zero)
    | both hd =>
      apply SlotSplit.both
      rw [quantity_mergeType]
      exact Usage.merge_effective _ _ _ _ _ hc hd

omit [DecidableEq α] in
/-- Identity-index weakening changes usages and preserves every value type. -/
theorem Weakening.exists_quantities {Γ Δ : QCtx (Ty α) n} (w : Weakening Γ Δ id) :
    ∃ q : Fin n → Usage, Δ = (fun i => ((Γ i).1, q i)) := by
  refine ⟨fun i => (Δ i).2, ?_⟩
  funext i
  exact Prod.ext (w.types i).symm rfl

omit [DecidableEq α] in
/-- The output types of a split are exactly its input types; only usages vary. -/
theorem Split.exists_quantities {Γ Γl Γr : QCtx (Ty α) n} (s : Split Γ Γl Γr) :
    ∃ ql qr : Fin n → Usage,
      Γl = (fun i => ((Γ i).1, ql i)) ∧ Γr = (fun i => ((Γ i).1, qr i)) := by
  refine ⟨fun i => (Γl i).2, fun i => (Γr i).2, ?_, ?_⟩
  · funext i
    exact Prod.ext (s i).1 rfl
  · funext i
    exact Prod.ext (s i).2.1 rfl

/-- Merging allocation witnesses is sound when neither comparison removes a retained branch slot. -/
theorem Split.merge {Γ Γl Γr Δ Δl Δr : QCtx (Ty α) n}
    (s : Split Γ Γl Γr) (t : Split Δ Δl Δr)
    (hl : Aligned Γl Δl) (hr : Aligned Γr Δr) :
    Split (QCtx.merge Γ Δ) (QCtx.merge Γl Δl) (QCtx.merge Γr Δr) := by
  intro i
  refine ⟨congrArg₂ mergeType (s i).1 (t i).1,
    congrArg₂ mergeType (s i).2.1 (t i).2.1, ?_⟩
  exact (s i).2.2.merge (t i).2.2 (hl i) (hr i)

end QCtx
variable {α : Type u} [DecidableEq α] [HasQuantity α]
variable {Φ : Type v} {ε : Type w} [HasTy Φ (Ty α)] [EffectSystem ε] [HasEff Φ ε]

omit [DecidableEq α] in
/-- Two typings of the same raw term retain exactly the same positions after support restriction. -/
theorem HasType.support_aligned {F G : Fragment} {n : Nat} {Γ Δ : QCtx (Ty α) n}
    {e e' : ε} {t : Term Φ n} {A B : Ty α}
    (h : HasType F Γ e t A) (k : HasType G Δ e' t B) :
    QCtx.Aligned (QCtx.restrict Γ (Term.uses t)) (QCtx.restrict Δ (Term.uses t)) := by
  exact QCtx.Aligned.restrict_of_nonzero Γ Δ _ (fun _ => h.used_nonzero) (fun _ => k.used_nonzero)

end Silmaril.Isotope.Refinement
