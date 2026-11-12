module

public import Silmaril.Cerberus.Target.Defs

@[expose] public section
namespace Silmaril.Cerberus.Target
open Silmaril.Cerberus

/-- Binding identity is independent of a symbol's diagnostic description. -/
theorem enum_lookup_of_key_eq (env : Environment) {first second : Sym}
    (same : first.key = second.key) :
    Map.lookup first env.enums = Map.lookup second env.enums := by
  change Finmap.lookup first.key env.enums = Finmap.lookup second.key env.enums
  rw [same]

theorem registerEnum_lookup {env next : Environment} {symbol : Sym} {values : List Int}
    (accepted : registerEnum env symbol values = .ok next) :
    Map.lookup symbol next.enums = some
      (if values.any (fun n => decide (n < 0)) then .signed .int else .unsigned .int) := by
  unfold registerEnum at accepted
  split at accepted
  · cases accepted
  · cases accepted
    exact Map.lookup_insert _ _ _

theorem registerEnum_rejects_existing (env : Environment) (symbol : Sym)
    (values : List Int) (type : IntegerType) (bound : Map.lookup symbol env.enums = some type) :
    registerEnum env symbol values = .error (.duplicateEnum symbol) := by
  simp [registerEnum, bound]

theorem normalize_enum (config : Config) (env : Environment) (symbol : Sym)
    (type : IntegerType) (bound : Map.lookup symbol env.enums = some type) :
    normalize config env (.enum symbol) = .ok type := by
  simp [normalize, lookupEnum, bound]

@[simp] theorem contains_eq_true (range : IntegerRange) (value : Int) :
    range.contains value = true ↔ range.lower ≤ value ∧ value ≤ range.upper := by
  simp [IntegerRange.contains]

/-- The range equation exposes both signedness and the chosen representation. -/
theorem integerRange_of_precision (config : Config) (env : Environment) (type : IntegerType)
    (bits : Nat) (signed : Bool) (hp : precision config env type = .ok bits)
    (hs : signedness config env type = .ok signed) :
    integerRange config env type = .ok (if signed then
      match config.binaryMode with
      | .twosComplement => ⟨-(2 ^ bits), 2 ^ bits - 1⟩
      | .onesComplement | .signMagnitude => ⟨-(2 ^ bits) + 1, 2 ^ bits - 1⟩
    else ⟨0, 2 ^ bits - 1⟩) := by
  simp only [integerRange, hp, hs]
  rfl

/-- Explicitly preserve the pinned frontend's floating-layout shortcuts. -/
theorem pinned_floating_layout (type : FloatingType) :
    floatingLayout pinnedApple type = .ok ⟨8, 8⟩ := rfl

theorem pinned_signed_int_range :
    integerRange pinnedApple emptyEnvironment (.signed .int) = .ok ⟨-2147483648, 2147483647⟩ := by
  rfl

theorem pinned_unsigned_long_range :
    integerRange pinnedApple emptyEnvironment (.unsigned .long) =
      .ok ⟨0, 18446744073709551615⟩ := by
  rfl

end Silmaril.Cerberus.Target
