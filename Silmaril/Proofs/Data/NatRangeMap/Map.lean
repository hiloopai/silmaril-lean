module

public import Silmaril.Data.NatRangeMap.Defs

/-!
# Finite range maps: extensionality and completeness
-/

@[expose] public section

namespace Silmaril.Proofs.Data.NatRangeMap.Map

open Silmaril.Data

universe u

variable {α : Type u}

theorem ext_iff {m₁ m₂ : NatRangeMap α} : m₁ = m₂ ↔ ∀ k, m₁.find? k = m₂.find? k := by
  refine ⟨fun h _ => h ▸ rfl, fun h => ?_⟩
  obtain ⟨r₁, h₁⟩ := m₁
  obtain ⟨r₂, h₂⟩ := m₂
  cases NatRangeMap.Raw.eq_of_find? h₁ h₂ h
  rfl

theorem find?_ofFn [DecidableEq α] {f : Nat → Option α} {n : Nat}
    (hf : ∀ k, n ≤ k → f k = none) (k : Nat) : (NatRangeMap.ofFn f n).find? k = f k := by
  simp only [NatRangeMap.ofFn, NatRangeMap.find?, NatRangeMap.Raw.find?_ofFn]
  by_cases hk : k < n
  · simp [hk]
  · simp [hk, hf k (Nat.le_of_not_lt hk)]

theorem complete [DecidableEq α] (f : Nat → Option α) (n : Nat)
    (hf : ∀ k, n ≤ k → f k = none) : ∃ m : NatRangeMap α, ∀ k, m.find? k = f k :=
  ⟨NatRangeMap.ofFn f n, find?_ofFn hf⟩

theorem find?_of_extent_le (m : NatRangeMap α) {k : Nat} (h : m.extent ≤ k) :
    m.find? k = none :=
  NatRangeMap.Raw.find?_of_extent_le h

theorem finite (m : NatRangeMap α) : ∃ n, ∀ k, n ≤ k → m.find? k = none :=
  ⟨m.extent, fun _ => find?_of_extent_le m⟩

end Silmaril.Proofs.Data.NatRangeMap.Map
