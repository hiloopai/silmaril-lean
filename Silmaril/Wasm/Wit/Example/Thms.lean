module

public import Silmaril.Wasm.Wit.Example.Defs

/-!
# WIT: validity of the examples

The checker is evaluated by the kernel (`decide +kernel`), and `check_iff` turns its
answers into `Valid` and `¬ Valid`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Example

theorem wasiIo_valid : Valid [wasiIo] := check_sound (by decide +kernel)

theorem consumer_valid : Valid [consumer, wasiIo] := check_sound (by decide +kernel)

/-- Without its dependency, the consumer's foreign paths do not resolve. -/
theorem consumer_alone_invalid : ¬ Valid [consumer] := fun h =>
  absurd (check_complete h) (by decide +kernel)

theorem ownRecord_invalid : ¬ Valid [ownRecord] := fun h =>
  absurd (check_complete h) (by decide +kernel)

theorem typeCycle_invalid : ¬ Valid [typeCycle] := fun h =>
  absurd (check_complete h) (by decide +kernel)

theorem useCycle_invalid : ¬ Valid [useCycle] := fun h =>
  absurd (check_complete h) (by decide +kernel)

theorem undefinedName_invalid : ¬ Valid [undefinedName] := fun h =>
  absurd (check_complete h) (by decide +kernel)

theorem borrowResult_invalid : ¬ Valid [borrowResult] := fun h =>
  absurd (check_complete h) (by decide +kernel)

theorem badNames_invalid : ¬ Valid [badNames] := fun h =>
  absurd (check_complete h) (by decide +kernel)

/-- Package names must be unique in a universe. -/
theorem duplicate_invalid : ¬ Valid [wasiIo, wasiIo] := fun h =>
  absurd (check_complete h) (by decide +kernel)

/-- The type cycle is rejected by the acyclicity requirement itself. -/
theorem typeCycle_cyclic : ¬ ∃ s : TypeId → Nat, ∀ t t', TypeEdge [typeCycle] t t' → s t' < s t :=
  fun h =>
    have hi : Graph.kahn (ifaceDeps [typeCycle]) (Universe.ifaceIds [typeCycle]) = true := by
      decide +kernel
    absurd ((kahn_type_iff hi).mpr h) (by decide +kernel)

end Silmaril.Wasm.Wit.Example
