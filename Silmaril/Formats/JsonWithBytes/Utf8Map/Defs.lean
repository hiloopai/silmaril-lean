module

public import Silmaril.Data.BytesTrie.Thms
public import Silmaril.Formats.JsonWithBytes.Defs

/-! A UTF-8 trie for the object layer of shared unordered JSON. Child values are
parameters: this module does not replace the shared recursive AST. -/

@[expose] public section
namespace Silmaril.Formats.JsonWithBytes.Utf8Map

open Silmaril.Data

def keyBytes (key : String) : List UInt8 := key.toUTF8.data.toList

def HasStringSupport {Value : Type} (map : BytesMap Value) : Prop :=
  ∃ keys : List String, ∀ bytes, bytes ∉ keys.map keyBytes → map.find? bytes = none

/-- A canonical trie with no bindings outside the image of UTF-8 string keys. -/
abbrev Map (Value : Type) := {map : BytesMap Value // HasStringSupport map}

def Map.find? {Value : Type} (map : Map Value) (key : String) : Option Value :=
  map.val.find? (keyBytes key)

def Map.empty {Value : Type} : Map Value :=
  ⟨BytesMap.empty, ⟨[], fun bytes _ => BytesMap.find?_empty bytes⟩⟩

def Map.insert {Value : Type} (acc : Map Value) (key : String) (value : Value) : Map Value :=
  ⟨acc.val.insert (keyBytes key) value, by
    obtain ⟨keys, supported⟩ := acc.property
    refine ⟨key :: keys, fun bytes absent => ?_⟩
    simp only [List.map_cons, List.mem_cons, not_or] at absent
    rw [BytesMap.find?_insert, ite_eq_right absent.1, supported _ absent.2]⟩

def Map.build {Value : Type} (acc : Map Value) : List (String × Value) → Except String (Map Value)
  | [] => .ok acc
  | (key, value) :: entries =>
    if (acc.find? key).isSome then .error key else build (acc.insert key value) entries

/-- Build in input order; reject the first repeated string key. The error is the duplicate key. -/
def Map.ofEntries {Value : Type} (entries : List (String × Value)) : Except String (Map Value) :=
  build empty entries

/-- Exactly the object fragment of the shared, extensional AST. -/
abbrev Object (Number : Type) := {value : Unordered Number //
  ∃ keys vals, value = Json.map keys vals}

/-- The indexed and shared semantics agree at every string key. -/
def Agrees {Number : Type} (map : Map (Unordered Number)) (object : Object Number) : Prop :=
  ∀ key, map.find? key = object.val.get? [.key key]

end Silmaril.Formats.JsonWithBytes.Utf8Map
