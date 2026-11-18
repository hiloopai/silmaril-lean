module

public import Silmaril.Formats.JsonWithBytes.Utf8Map.Defs
import Silmaril.Proofs.Formats.JsonWithBytes.Utf8Map

public section
namespace Silmaril.Formats.JsonWithBytes.Utf8Map

theorem ofEntries_sound {Value : Type} {entries : List (String × Value)} {result : Map Value}
    (built : Map.ofEntries entries = .ok result) :
    (entries.map Prod.fst).Nodup ∧ ∀ key, result.find? key = entries.lookup key :=
  Proofs.Formats.JsonWithBytes.Utf8Map.ofEntries_sound built

theorem ofEntries_accepts {Value : Type} (entries : List (String × Value)) :
    (∃ map, Map.ofEntries entries = .ok map) ↔ (entries.map Prod.fst).Nodup :=
  Proofs.Formats.JsonWithBytes.Utf8Map.ofEntries_accepts entries

/-- Semantic isomorphism at the object layer, with shared AST children. Use
`Map.ofEntries` and `Map.find?`, not this noncomputable equivalence, for runtime data. -/
noncomputable def equiv {Number : Type} : Map (Unordered Number) ≃ Object Number :=
  Proofs.Formats.JsonWithBytes.Utf8Map.equiv

theorem agrees_equiv {Number : Type} (map : Map (Unordered Number)) : Agrees map (equiv map) :=
  Proofs.Formats.JsonWithBytes.Utf8Map.agrees_equiv map

/-- Every lookup of an accepted build agrees with the actual shared extensional object. -/
theorem equiv_ofEntries {Number : Type} {entries : List (String × Unordered Number)}
    {map : Map (Unordered Number)} (built : Map.ofEntries entries = .ok map) :
    (equiv map).val = Json.ofEntries entries (ofEntries_sound built).1 :=
  Proofs.Formats.JsonWithBytes.Utf8Map.equiv_ofEntries built

end Silmaril.Formats.JsonWithBytes.Utf8Map
