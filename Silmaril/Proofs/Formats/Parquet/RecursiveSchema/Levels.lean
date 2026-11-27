module

public import Silmaril.Formats.Parquet.RecursiveSchema.Defs

@[expose] public section

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema

open Silmaril.Formats.Parquet.RecursiveSchema

theorem classify_value {leaf : Leaf} {row level : Nat} :
    leaf.classify row level = .ok .value ↔ level = leaf.maxDefinition := by
  by_cases full : level = leaf.maxDefinition
  · simp [Leaf.classify, full]
  · cases selected : leaf.optional[level]? <;> simp [Leaf.classify, full, selected]

theorem classify_absent {leaf : Leaf} {row level : Nat} {location : Location} :
    leaf.classify row level = .ok (.absent location) ↔ leaf.optional[level]? = some location := by
  by_cases full : level = leaf.maxDefinition
  · simp [Leaf.classify, full, Leaf.maxDefinition]
  · cases selected : leaf.optional[level]? <;> simp [Leaf.classify, full, selected]

theorem classify_out_of_range {leaf : Leaf} {row level : Nat}
    (over : leaf.maxDefinition < level) :
    leaf.classify row level = .error (.level leaf.site.location row level leaf.maxDefinition) := by
  have different : level ≠ leaf.maxDefinition := by omega
  have outside : leaf.optional[level]? = none := by
    exact List.getElem?_eq_none (by simpa [Leaf.maxDefinition] using Nat.le_of_lt over)
  simp [Leaf.classify, different, outside]

theorem bitWidth_exact (leaf : Leaf) :
    leaf.maxDefinition < 2^leaf.bitWidth ∧
      (leaf.bitWidth = 0 ∨ 2^(leaf.bitWidth - 1) ≤ leaf.maxDefinition) := by
  by_cases zero : leaf.maxDefinition = 0
  · simp [Leaf.bitWidth, zero]
  · simp only [Leaf.bitWidth, zero, ite_false, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      false_or, Nat.add_sub_cancel]
    exact ⟨Nat.lt_log2_self, Nat.log2_self_le zero⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema
