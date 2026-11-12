module

public import Mathlib.Data.Finmap
public import Silmaril.Cerberus.Implementation.Defs
public import Silmaril.Cerberus.Symbol.Defs

/-! # Lem finite maps

Lem's `map k v` is a finite map ordered by the key type's `MapKeyType`
comparison, and its equality is extensional. OCaml implements it as a balanced
tree that stores the key with each binding.

`Map k v` is Mathlib's `Finmap` indexed by `MapKey.Key k`, the part of a key that
Lem's comparison looks at, storing only the value. Keys that differ only in
diagnostic descriptions or locations share one binding. Every semantic key has
a representative, so `Map.ext_lookup` derives equality from the public lookups
using Mathlib's `Finmap.ext_lookup`. No consumer needs full key representatives.
`ofList` folds insertions from left to right, as Lem's `fromList` does: the last
binding wins. Mathlib supplies the lookup and insertion laws.

Mathlib's `AList` is not used, because its equality depends on insertion order.
The snoc contexts of `Silmaril.Isotope.Ctx` are not used either: they model
shadowing, which Lem maps do not have. Mathlib gives `Finmap` no safe `Repr`, so
neither `Map` nor the Core file record derives one.
-/

@[expose] public section

namespace Silmaril.Cerberus

/-- How Lem's `MapKeyType` instance compares keys: two keys are the same
exactly when their `key`s are equal. -/
class MapKey (k : Type) where
  Key : Type
  key : k → Key
  decEq : DecidableEq Key
  key_surjective : Function.Surjective key

instance {k : Type} [MapKey k] : DecidableEq (MapKey.Key k) := MapKey.decEq

instance : MapKey Nat := ⟨Nat, id, inferInstance, fun x => ⟨x, rfl⟩⟩
instance : MapKey Int := ⟨Int, id, inferInstance, fun x => ⟨x, rfl⟩⟩
instance : MapKey Identifier := ⟨String, Identifier.key, inferInstance, fun x => ⟨⟨.unknown, x⟩, rfl⟩⟩
instance : MapKey Sym := ⟨Digest × Nat, Sym.key, inferInstance, fun x => ⟨⟨x.1, x.2, .none⟩, rfl⟩⟩
instance : MapKey ImplementationConstant := ⟨ImplementationConstant, id, inferInstance, fun x => ⟨x, rfl⟩⟩

/-- Lem's `map k v`. -/
abbrev Map (k v : Type) [MapKey k] := Finmap fun _ : MapKey.Key k => v

namespace Map

variable {k v : Type} [MapKey k]

/-- The value bound to a key Lem compares equal to `x`. -/
def lookup (x : k) (m : Map k v) : Option v :=
  Finmap.lookup (MapKey.key x) m

/-- Bind `x` to `y`, replacing any binding of a key Lem compares equal to `x`. -/
def insert (x : k) (y : v) (m : Map k v) : Map k v :=
  Finmap.insert (MapKey.key x) y m

/-- Remove the binding whose key Lem compares equal to `x`. -/
def erase (x : k) (m : Map k v) : Map k v :=
  Finmap.erase (MapKey.key x) m

/-- The map of a list of bindings; the last binding of an equal key wins. -/
def ofList (bindings : List (k × v)) : Map k v :=
  bindings.foldl (fun m b => m.insert b.1 b.2) ∅

/-- Maps are equal when every public lookup agrees. -/
theorem ext_lookup {m n : Map k v} (h : ∀ x, m.lookup x = n.lookup x) : m = n := by
  apply Finmap.ext_lookup
  intro key
  obtain ⟨x, rfl⟩ := MapKey.key_surjective key
  exact h x

@[simp] theorem lookup_insert (x : k) (y : v) (m : Map k v) :
    (m.insert x y).lookup x = some y := by
  simp [lookup, insert]

theorem lookup_insert_of_key_ne {x x' : k} (y : v) (m : Map k v)
    (h : MapKey.key x' ≠ MapKey.key x) : (m.insert x y).lookup x' = m.lookup x' := by
  simp [lookup, insert, Finmap.lookup_insert_of_ne _ h]

end Map

end Silmaril.Cerberus
