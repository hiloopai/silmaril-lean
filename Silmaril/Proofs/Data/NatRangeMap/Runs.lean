module

public import Silmaril.Data.NatRangeMap.Runs.Defs

/-!
# Run lists: lookup specifications, normalization and canonical forms
-/

@[expose] public section

namespace Silmaril.Proofs.Data.NatRangeMap

open Silmaril.Data.NatRangeMap
open Silmaril.Data.NatRangeMap.Raw

universe u

variable {α : Type u}

/-- Split every `if` in the goal and close the arithmetic leaves. -/
local macro "nrm_arith" : tactic =>
  `(tactic| (repeat' split) <;> first | rfl | omega | (congr 1; omega) | simp_all)

theorem find?_nil (k : Nat) : find? ([] : Raw α) k = none := rfl

theorem find?_cons (g l : Nat) (v : α) (rs : Raw α) (k : Nat) :
    find? (⟨g, l, v⟩ :: rs) k =
      if k < g then none else if k ≤ g + l then some v else find? rs (k - (g + l + 1)) := rfl

theorem find?_cons_lt {g l k : Nat} {v : α} {rs : Raw α} (h : k < g) :
    find? (⟨g, l, v⟩ :: rs) k = none := by
  simp [find?_cons, h]

theorem find?_cons_mem {g l k : Nat} {v : α} {rs : Raw α} (h₁ : g ≤ k) (h₂ : k ≤ g + l) :
    find? (⟨g, l, v⟩ :: rs) k = some v := by
  rw [find?_cons]; nrm_arith

theorem find?_cons_after (g l : Nat) (v : α) (rs : Raw α) (k : Nat) :
    find? (⟨g, l, v⟩ :: rs) (g + l + 1 + k) = find? rs k := by
  rw [find?_cons]; nrm_arith

theorem find?_cons_congr (x : Run α) {s t : Raw α} (h : ∀ k, find? s k = find? t k) (k : Nat) :
    find? (x :: s) k = find? (x :: t) k := by
  obtain ⟨g, l, v⟩ := x
  simp only [find?_cons, h]

theorem find?_of_extent_le {r : Raw α} {k : Nat} (h : extent r ≤ k) : find? r k = none := by
  induction r generalizing k with
  | nil => rfl
  | cons x rs ih =>
    obtain ⟨g, l, v⟩ := x
    simp only [extent] at h
    rw [find?_cons]
    have := ih (k := k - (g + l + 1)) (by omega)
    nrm_arith

theorem find?_addGap (d : Nat) (s : Raw α) (k : Nat) :
    find? (addGap d s) k = if k < d then none else find? s (k - d) := by
  cases s with
  | nil => simp [addGap, find?_nil]
  | cons x rs =>
    obtain ⟨g, l, v⟩ := x
    simp only [addGap, find?_cons]
    nrm_arith

theorem find?_mergeCons [DecidableEq α] (x : Run α) (s : Raw α) (k : Nat) :
    find? (mergeCons x s) k = find? (x :: s) k := by
  cases s with
  | nil => rfl
  | cons y rs =>
    obtain ⟨g, l, v⟩ := x
    obtain ⟨g', l', v'⟩ := y
    simp only [mergeCons]
    split
    · next h =>
      obtain ⟨rfl, rfl⟩ := h
      simp only [find?_cons]
      nrm_arith
    · rfl

theorem find?_catMerge [DecidableEq α] {r : Raw α} {n : Nat} (s : Raw α)
    (h : ∀ k, n ≤ k → find? r k = none) (k : Nat) :
    find? (catMerge r n s) k = if k < n then find? r k else find? s (k - n) := by
  induction r generalizing n k with
  | nil => simp [catMerge, find?_addGap, find?_nil]
  | cons x rs ih =>
    obtain ⟨g, l, v⟩ := x
    have hn : g + l < n := Nat.lt_of_not_le fun hle => by
      have := h (g + l) hle
      rw [find?_cons_mem (Nat.le_add_right g l) (Nat.le_refl _)] at this
      cases this
    have hrs : ∀ k, n - (g + l + 1) ≤ k → find? rs k = none := fun k hk => by
      rw [← find?_cons_after g l v rs k]
      exact h _ (by omega)
    simp only [catMerge, find?_mergeCons, find?_cons, ih hrs]
    nrm_arith

theorem find?_takeBelow (r : Raw α) (n k : Nat) :
    find? (takeBelow r n) k = if k < n then find? r k else none := by
  induction r generalizing n k with
  | nil => simp [takeBelow, find?_nil]
  | cons x rs ih =>
    obtain ⟨g, l, v⟩ := x
    simp only [takeBelow]
    split
    · rw [find?_cons]; simp only [find?_nil]; nrm_arith
    · split
      · simp only [find?_cons, find?_nil]; nrm_arith
      · simp only [find?_cons, ih]; nrm_arith

theorem find?_dropBelow (r : Raw α) (n k : Nat) :
    find? (dropBelow r n) k = find? r (n + k) := by
  induction r generalizing n k with
  | nil => rfl
  | cons x rs ih =>
    obtain ⟨g, l, v⟩ := x
    simp only [dropBelow]
    split
    · simp only [find?_cons]; nrm_arith
    · split
      · simp only [find?_cons]; nrm_arith
      · simp only [find?_cons, ih]; nrm_arith

theorem find?_assign [DecidableEq α] (r : Raw α) (lo len1 : Nat) (v : α) (k : Nat) :
    find? (assign r lo len1 v) k = if lo ≤ k ∧ k ≤ lo + len1 then some v else find? r k := by
  have h : ∀ k, lo ≤ k → find? (takeBelow r lo) k = none := fun k hk => by
    rw [find?_takeBelow]; nrm_arith
  simp only [assign, find?_catMerge _ h, find?_takeBelow, find?_mergeCons, find?_cons,
    find?_dropBelow]
  nrm_arith

theorem find?_erase [DecidableEq α] (r : Raw α) (lo len1 : Nat) (k : Nat) :
    find? (erase r lo len1) k = if lo ≤ k ∧ k ≤ lo + len1 then none else find? r k := by
  have h : ∀ k, lo + len1 + 1 ≤ k → find? (takeBelow r lo) k = none := fun k hk => by
    rw [find?_takeBelow]; nrm_arith
  simp only [erase, find?_catMerge _ h, find?_takeBelow, find?_dropBelow]
  nrm_arith

theorem find?_normalize [DecidableEq α] (r : Raw α) (k : Nat) :
    find? (normalize r) k = find? r k := by
  induction r generalizing k with
  | nil => rfl
  | cons x rs ih =>
    simp only [normalize, find?_mergeCons]
    exact find?_cons_congr x ih k

theorem canonical_tail {x : Run α} {rs : Raw α} (h : Canonical (x :: rs)) : Canonical rs := by
  cases rs with
  | nil => trivial
  | cons y rs => exact h.2

theorem canonical_mergeCons [DecidableEq α] (x : Run α) {s : Raw α} (hs : Canonical s) :
    Canonical (mergeCons x s) := by
  cases s with
  | nil => trivial
  | cons y rs =>
    simp only [mergeCons]
    split
    · next h =>
      cases rs with
      | nil => trivial
      | cons z rs =>
        refine ⟨fun hz he => hs.1 hz ?_, hs.2⟩
        rw [← he, h.2]
    · next h =>
      exact ⟨fun hg he => h ⟨hg, he⟩, hs⟩

theorem canonical_normalize [DecidableEq α] (r : Raw α) : Canonical (normalize r) := by
  induction r with
  | nil => trivial
  | cons x rs ih => exact canonical_mergeCons x ih

theorem find?_ofFn [DecidableEq α] (f : Nat → Option α) (n k : Nat) :
    find? (ofFn f n) k = if k < n then f k else none := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    simp only [ofFn]
    split
    · next h =>
      rw [ih]
      by_cases hk : k = n
      · subst hk; simp [h]
      · nrm_arith
    · next v h =>
      rw [find?_assign, ih]
      by_cases hk : k = n
      · subst hk; simp [h]
      · nrm_arith

theorem canonical_addGap (d : Nat) {s : Raw α} (hs : Canonical s) : Canonical (addGap d s) := by
  match s, hs with
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: _ :: _, hs => exact hs

theorem canonical_catMerge [DecidableEq α] (r : Raw α) (n : Nat) {s : Raw α}
    (hs : Canonical s) : Canonical (catMerge r n s) := by
  induction r generalizing n with
  | nil => exact canonical_addGap n hs
  | cons x rs ih => exact canonical_mergeCons _ (ih _)

theorem canonical_dropBelow {r : Raw α} (hr : Canonical r) (n : Nat) :
    Canonical (dropBelow r n) := by
  induction r generalizing n with
  | nil => trivial
  | cons x rs ih =>
    obtain ⟨g, l, v⟩ := x
    simp only [dropBelow]
    split
    · match rs, hr with
      | [], _ => trivial
      | _ :: _, hr => exact hr
    · split
      · match rs, hr with
        | [], _ => trivial
        | _ :: _, hr => exact hr
      · exact ih (canonical_tail hr) _

theorem canonical_assign [DecidableEq α] {r : Raw α} (hr : Canonical r) (lo len1 : Nat)
    (v : α) : Canonical (assign r lo len1 v) :=
  canonical_catMerge _ _ (canonical_mergeCons _ (canonical_dropBelow hr _))

theorem canonical_erase [DecidableEq α] {r : Raw α} (hr : Canonical r) (lo len1 : Nat) :
    Canonical (erase r lo len1) :=
  canonical_catMerge _ _ (canonical_dropBelow hr _)

theorem canonical_ofFn [DecidableEq α] (f : Nat → Option α) (n : Nat) :
    Canonical (ofFn f n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    simp only [ofFn]
    split
    · exact ih
    · exact canonical_assign ih _ _ _

theorem canonical_ofList [DecidableEq α] (l : List (Nat × Nat × α)) :
    Canonical (ofList l) := by
  induction l with
  | nil => trivial
  | cons e l ih => exact canonical_assign ih _ _ _

theorem find?_ofList_toListFrom [DecidableEq α] (r : Raw α) (b k : Nat) :
    find? (ofList (toListFrom b r)) k = if b ≤ k then find? r (k - b) else none := by
  induction r generalizing b with
  | nil => simp only [toListFrom, ofList, find?_nil]; nrm_arith
  | cons x rs ih =>
    obtain ⟨g, l, v⟩ := x
    simp only [toListFrom, ofList, find?_assign, ih, find?_cons]
    nrm_arith

theorem find?_ofList_toList [DecidableEq α] (r : Raw α) (k : Nat) :
    find? (ofList (toList r)) k = find? r k := by
  simp [toList, find?_ofList_toListFrom]

/-- A canonical list whose first run has length `len1 + 1` agrees with one whose
first run, at the same place and with the same value, is no longer. -/
theorem len1_le_of_find? {g l l' : Nat} {v : α} {rs ss : Raw α}
    (hc : Canonical (⟨g, l, v⟩ :: rs))
    (h : ∀ k, find? (⟨g, l, v⟩ :: rs) k = find? (⟨g, l', v⟩ :: ss) k) : l' ≤ l := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have hk := h (g + l + 1 + 0)
  rw [find?_cons_after, find?_cons_mem (by omega) (by omega)] at hk
  cases rs with
  | nil => cases hk
  | cons y rs =>
    obtain ⟨g₂, l₂, v₂⟩ := y
    rw [find?_cons] at hk
    split at hk
    · cases hk
    · split at hk
      · cases hk
        exact hc.1 (show g₂ = 0 by omega) rfl
      · omega

/-- **Canonical forms are unique**: canonical run lists with the same lookups are
equal. -/
theorem eq_of_find? {r₁ r₂ : Raw α} (h₁ : Canonical r₁) (h₂ : Canonical r₂)
    (h : ∀ k, find? r₁ k = find? r₂ k) : r₁ = r₂ := by
  induction r₁ generalizing r₂ with
  | nil =>
    cases r₂ with
    | nil => rfl
    | cons y ss =>
      obtain ⟨g, l, v⟩ := y
      have := h g
      rw [find?_cons_mem (Nat.le_refl g) (Nat.le_add_right g l)] at this
      cases this
  | cons x rs ih =>
    obtain ⟨g, l, v⟩ := x
    cases r₂ with
    | nil =>
      have := h g
      rw [find?_cons_mem (Nat.le_refl g) (Nat.le_add_right g l)] at this
      cases this
    | cons y ss =>
      obtain ⟨g', l', v'⟩ := y
      have hg₁ : g' ≤ g := Nat.le_of_not_lt fun hlt => by
        have := h g
        rw [find?_cons_mem (Nat.le_refl g) (Nat.le_add_right g l), find?_cons_lt hlt] at this
        cases this
      have hg₂ : g ≤ g' := Nat.le_of_not_lt fun hlt => by
        have := h g'
        rw [find?_cons_lt hlt, find?_cons_mem (Nat.le_refl g') (Nat.le_add_right g' l')] at this
        cases this
      have hg : g = g' := Nat.le_antisymm hg₂ hg₁
      subst hg
      have hv : v = v' := by
        have := h g
        rw [find?_cons_mem (Nat.le_refl g) (Nat.le_add_right g l),
          find?_cons_mem (Nat.le_refl g) (Nat.le_add_right g l')] at this
        exact Option.some.inj this
      subst hv
      have hl : l = l' := Nat.le_antisymm
        (len1_le_of_find? h₂ fun k => (h k).symm) (len1_le_of_find? h₁ h)
      subst hl
      have ht : rs = ss := ih (canonical_tail h₁) (canonical_tail h₂) fun k => by
        rw [← find?_cons_after g l v rs k, ← find?_cons_after g l v ss k]
        exact h _
      subst ht
      rfl

end Silmaril.Proofs.Data.NatRangeMap
