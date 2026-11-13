module

public import Silmaril.Raw.SSA.Isotope.Refinement.TypingRestriction

@[expose] public section

namespace Silmaril.Isotope.Refinement.QCtx
universe u
variable {τ : Type u} [HasQuantity τ]

/-- Extend an identity-indexed weakening by retaining the newest bound slot. -/
theorem Weakening.keepNewest {n : Nat} {Γ Δ : QCtx τ n}
    (h : Weakening Γ Δ id) (A : τ) : Weakening (Γ.snoc A) (Δ.snoc A) id := by
  have he : Fin.cases 0 (fun i : Fin n => (id i).succ) = id := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  exact he ▸ Weakening.cons h le_rfl

namespace SlotSplit
variable {A : τ} {q ql qr : Usage}

theorem left_eq_of_ne_zero (s : SlotSplit A q ql qr) (h : ql ≠ .zero) : ql = q := by
  cases s with
  | left => rfl
  | right => exact False.elim (h rfl)
  | both => rfl

theorem right_eq_of_ne_zero (s : SlotSplit A q ql qr) (h : qr ≠ .zero) : qr = q :=
  s.symm.left_eq_of_ne_zero h

/-- Each output can independently discard the slots absent from its syntax. -/
theorem restrictOutputs (s : SlotSplit A q ql qr) (b c : Bool)
    (hb : b = true → ql ≠ .zero) (hc : c = true → qr ≠ .zero) :
    SlotSplit A (if b || c then q else .zero) (if b then ql else .zero) (if c then qr else .zero) := by
  cases b <;> cases c
  · exact .left .zero
  · simpa [s.right_eq_of_ne_zero (hc rfl)] using (SlotSplit.right (A := A) q)
  · simpa [s.left_eq_of_ne_zero (hb rfl)] using (SlotSplit.left (A := A) q)
  · exact s
end SlotSplit

namespace Split
variable {n : Nat} {Γ Γl Γr : QCtx τ n}

/-- A used slot inherited by an output has its original annotation. -/
theorem restrict_left_eq (s : Split Γ Γl Γr) (p : Fin n → Bool)
    (hp : ∀ i, p i = true → (Γl i).2 ≠ .zero) : QCtx.restrict Γl p = QCtx.restrict Γ p := by
  funext i
  apply Prod.ext
  · exact (s i).1
  change (if p i then (Γl i).2 else .zero) = (if p i then (Γ i).2 else .zero)
  cases hi : p i
  · rfl
  · exact (s i).2.2.left_eq_of_ne_zero (hp i hi)

theorem restrict_right_eq (s : Split Γ Γl Γr) (p : Fin n → Bool)
    (hp : ∀ i, p i = true → (Γr i).2 ≠ .zero) : QCtx.restrict Γr p = QCtx.restrict Γ p :=
  s.symm.restrict_left_eq p hp

/-- Restricting a split separately to the two raw supports. -/
theorem restrictOutputs (s : Split Γ Γl Γr) (p q : Fin n → Bool)
    (hp : ∀ i, p i = true → (Γl i).2 ≠ .zero)
    (hq : ∀ i, q i = true → (Γr i).2 ≠ .zero) :
    Split (QCtx.restrict Γ (fun i => p i || q i)) (QCtx.restrict Γl p) (QCtx.restrict Γr q) :=
  fun i => ⟨(s i).1, (s i).2.1, (s i).2.2.restrictOutputs (p i) (q i) (hp i) (hq i)⟩

/-- Once unused slots are removed, the split's three contexts are determined
by the original context and the two syntax supports alone. -/
theorem support (s : Split Γ Γl Γr) (p q : Fin n → Bool)
    (hp : ∀ i, p i = true → (Γl i).2 ≠ .zero)
    (hq : ∀ i, q i = true → (Γr i).2 ≠ .zero) :
    Split (QCtx.restrict Γ (fun i => p i || q i)) (QCtx.restrict Γ p) (QCtx.restrict Γ q) := by
  rw [← s.restrict_left_eq p hp, ← s.restrict_right_eq q hq]
  exact s.restrictOutputs p q hp hq

/-- The parent context can discard precisely what neither subterm uses. -/
theorem supportWeakening (s : Split Γ Γl Γr) (p q : Fin n → Bool)
    (hp : ∀ i, SlotAllows (Γl i).1 (Γl i).2 (p i))
    (hq : ∀ i, SlotAllows (Γr i).1 (Γr i).2 (q i)) :
    Weakening Γ (QCtx.restrict Γ (fun i => p i || q i)) id := by
  apply weakening_restrict
  intro i hi
  exact ((s i).2.2.allows (by simpa only [(s i).1] using hp i)
    (by simpa only [(s i).2.1] using hq i)).2 hi

/-- Left part of the canonical support square. -/
theorem supportWeakening_left (s : Split Γ Γl Γr) (p : Fin n → Bool)
    (hp : ∀ i, SlotAllows (Γl i).1 (Γl i).2 (p i)) :
    Weakening Γl (QCtx.restrict Γ p) id := by
  rw [← s.restrict_left_eq p (fun i => (hp i).1)]
  exact weakening_restrict Γl p (fun i => (hp i).2)

/-- Right part of the canonical support square. -/
theorem supportWeakening_right (s : Split Γ Γl Γr) (q : Fin n → Bool)
    (hq : ∀ i, SlotAllows (Γr i).1 (Γr i).2 (q i)) :
    Weakening Γr (QCtx.restrict Γ q) id := s.symm.supportWeakening_left q hq

end Split
end Silmaril.Isotope.Refinement.QCtx
