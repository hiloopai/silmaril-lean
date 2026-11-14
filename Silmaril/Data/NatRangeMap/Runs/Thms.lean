module

public import Silmaril.Data.NatRangeMap.Runs.Defs
import Silmaril.Proofs.Data.NatRangeMap.Runs

/-!
# Run lists: theorems

Proofs in `Silmaril.Proofs.Data.NatRangeMap` (`Silmaril/Proofs/Data/NatRangeMap/Runs.lean`).

* pointwise lookup specifications of `assign`, `erase`, `normalize`, `ofFn` and the
  primitives `takeBelow`, `dropBelow`, `mergeCons`, `catMerge`;
* `canonical_assign`, `canonical_erase`: canonical input gives canonical output;
  `canonical_ofFn`, `canonical_ofList`, `canonical_normalize`: these always produce canonical run lists;
* `eq_of_find?`: **canonical forms are unique** — canonical run lists with the same
  lookups are equal (raw run lists in general are not unique);
* `find?_ofList_toList`: `ofList` reads back `toList`;
* `find?_of_extent_le`: every run list denotes a finitely supported map.
-/

@[expose] public section

namespace Silmaril.Data.NatRangeMap.Raw

universe u

variable {α : Type u}

theorem find?_takeBelow (r : Raw α) (n k : Nat) :
    find? (takeBelow r n) k = if k < n then find? r k else none :=
  Proofs.Data.NatRangeMap.find?_takeBelow r n k

theorem find?_dropBelow (r : Raw α) (n k : Nat) :
    find? (dropBelow r n) k = find? r (n + k) :=
  Proofs.Data.NatRangeMap.find?_dropBelow r n k

theorem find?_mergeCons [DecidableEq α] (x : Run α) (s : Raw α) (k : Nat) :
    find? (mergeCons x s) k = find? (x :: s) k :=
  Proofs.Data.NatRangeMap.find?_mergeCons x s k

theorem find?_catMerge [DecidableEq α] {r : Raw α} {n : Nat} (s : Raw α)
    (h : ∀ k, n ≤ k → find? r k = none) (k : Nat) :
    find? (catMerge r n s) k = if k < n then find? r k else find? s (k - n) :=
  Proofs.Data.NatRangeMap.find?_catMerge s h k

theorem find?_assign [DecidableEq α] (r : Raw α) (lo len1 : Nat) (v : α) (k : Nat) :
    find? (assign r lo len1 v) k = if lo ≤ k ∧ k ≤ lo + len1 then some v else find? r k :=
  Proofs.Data.NatRangeMap.find?_assign r lo len1 v k

theorem find?_erase [DecidableEq α] (r : Raw α) (lo len1 : Nat) (k : Nat) :
    find? (erase r lo len1) k = if lo ≤ k ∧ k ≤ lo + len1 then none else find? r k :=
  Proofs.Data.NatRangeMap.find?_erase r lo len1 k

theorem find?_normalize [DecidableEq α] (r : Raw α) (k : Nat) :
    find? (normalize r) k = find? r k :=
  Proofs.Data.NatRangeMap.find?_normalize r k

theorem canonical_normalize [DecidableEq α] (r : Raw α) : Canonical (normalize r) :=
  Proofs.Data.NatRangeMap.canonical_normalize r

theorem find?_ofFn [DecidableEq α] (f : Nat → Option α) (n k : Nat) :
    find? (ofFn f n) k = if k < n then f k else none :=
  Proofs.Data.NatRangeMap.find?_ofFn f n k

theorem canonical_mergeCons [DecidableEq α] (x : Run α) {s : Raw α} (hs : Canonical s) :
    Canonical (mergeCons x s) :=
  Proofs.Data.NatRangeMap.canonical_mergeCons x hs

theorem canonical_catMerge [DecidableEq α] (r : Raw α) (n : Nat) {s : Raw α}
    (hs : Canonical s) : Canonical (catMerge r n s) :=
  Proofs.Data.NatRangeMap.canonical_catMerge r n hs

theorem canonical_dropBelow {r : Raw α} (hr : Canonical r) (n : Nat) :
    Canonical (dropBelow r n) :=
  Proofs.Data.NatRangeMap.canonical_dropBelow hr n

theorem canonical_assign [DecidableEq α] {r : Raw α} (hr : Canonical r) (lo len1 : Nat)
    (v : α) : Canonical (assign r lo len1 v) :=
  Proofs.Data.NatRangeMap.canonical_assign hr lo len1 v

theorem canonical_erase [DecidableEq α] {r : Raw α} (hr : Canonical r) (lo len1 : Nat) :
    Canonical (erase r lo len1) :=
  Proofs.Data.NatRangeMap.canonical_erase hr lo len1

theorem canonical_ofFn [DecidableEq α] (f : Nat → Option α) (n : Nat) :
    Canonical (ofFn f n) :=
  Proofs.Data.NatRangeMap.canonical_ofFn f n

theorem canonical_ofList [DecidableEq α] (l : List (Nat × Nat × α)) :
    Canonical (ofList l) :=
  Proofs.Data.NatRangeMap.canonical_ofList l

theorem find?_ofList_toList [DecidableEq α] (r : Raw α) (k : Nat) :
    find? (ofList (toList r)) k = find? r k :=
  Proofs.Data.NatRangeMap.find?_ofList_toList r k

theorem find?_of_extent_le {r : Raw α} {k : Nat} (h : extent r ≤ k) : find? r k = none :=
  Proofs.Data.NatRangeMap.find?_of_extent_le h

/-- **Canonical forms are unique**: canonical run lists with the same lookups are
equal. -/
theorem eq_of_find? {r₁ r₂ : Raw α} (h₁ : Canonical r₁) (h₂ : Canonical r₂)
    (h : ∀ k, find? r₁ k = find? r₂ k) : r₁ = r₂ :=
  Proofs.Data.NatRangeMap.eq_of_find? h₁ h₂ h

end Silmaril.Data.NatRangeMap.Raw
