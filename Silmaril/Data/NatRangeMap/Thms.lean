module

public import Silmaril.Data.NatRangeMap.Defs
import Silmaril.Proofs.Data.NatRangeMap.Map

/-!
# Finite range maps: theorems

Longer proofs in `Silmaril.Proofs.Data.NatRangeMap` (`Silmaril/Proofs/Data/NatRangeMap/`).

* pointwise specifications `find?_empty`, `find?_assign`, `find?_erase`, `find?_ofFn`;
* `ext_iff`: maps are equal iff their lookups agree (canonical forms are unique), so
  the structural `DecidableEq` instance decides extensional equality;
* `ofList_toList`: the run list `toList` determines the map;
* `finite` and `complete`: the represented functions are exactly the finitely
  supported functions `Nat → Option α`.
-/

@[expose] public section

namespace Silmaril.Data.NatRangeMap

universe u

variable {α : Type u}

@[simp] theorem find?_empty (k : Nat) : (empty : NatRangeMap α).find? k = none := rfl

@[simp] theorem find?_assign [DecidableEq α] (m : NatRangeMap α) (lo len1 : Nat) (v : α)
    (k : Nat) :
    (m.assign lo len1 v).find? k = if lo ≤ k ∧ k ≤ lo + len1 then some v else m.find? k := by
  simp only [assign, find?, Raw.find?_assign]

@[simp] theorem find?_erase [DecidableEq α] (m : NatRangeMap α) (lo len1 : Nat) (k : Nat) :
    (m.erase lo len1).find? k = if lo ≤ k ∧ k ≤ lo + len1 then none else m.find? k := by
  simp only [erase, find?, Raw.find?_erase]

@[simp] theorem ofList_nil [DecidableEq α] : ofList ([] : List (Nat × Nat × α)) = empty := rfl

theorem ofList_cons [DecidableEq α] (lo len1 : Nat) (v : α) (l : List (Nat × Nat × α)) :
    ofList ((lo, len1, v) :: l) = (ofList l).assign lo len1 v := rfl

/-- **Extensionality**: maps are equal iff their lookups agree. -/
theorem ext_iff {m₁ m₂ : NatRangeMap α} : m₁ = m₂ ↔ ∀ k, m₁.find? k = m₂.find? k :=
  Proofs.Data.NatRangeMap.Map.ext_iff

theorem ext {m₁ m₂ : NatRangeMap α} (h : ∀ k, m₁.find? k = m₂.find? k) : m₁ = m₂ :=
  ext_iff.2 h

theorem find?_ofFn [DecidableEq α] {f : Nat → Option α} {n : Nat}
    (hf : ∀ k, n ≤ k → f k = none) (k : Nat) : (ofFn f n).find? k = f k :=
  Proofs.Data.NatRangeMap.Map.find?_ofFn hf k

/-- **Completeness**: every finitely supported function is represented. -/
theorem complete [DecidableEq α] (f : Nat → Option α) (n : Nat)
    (hf : ∀ k, n ≤ k → f k = none) : ∃ m : NatRangeMap α, ∀ k, m.find? k = f k :=
  Proofs.Data.NatRangeMap.Map.complete f n hf

theorem find?_of_extent_le (m : NatRangeMap α) {k : Nat} (h : m.extent ≤ k) :
    m.find? k = none :=
  Proofs.Data.NatRangeMap.Map.find?_of_extent_le m h

/-- `ofList` reads back `toList`. -/
theorem ofList_toList [DecidableEq α] (m : NatRangeMap α) : ofList m.toList = m :=
  ext (Raw.find?_ofList_toList m.raw)

/-- **Finiteness**: every map is finitely supported. -/
theorem finite (m : NatRangeMap α) : ∃ n, ∀ k, n ≤ k → m.find? k = none :=
  Proofs.Data.NatRangeMap.Map.finite m

end Silmaril.Data.NatRangeMap
