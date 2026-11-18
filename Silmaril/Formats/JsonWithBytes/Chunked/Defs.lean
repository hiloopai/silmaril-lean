module

public import Silmaril.Formats.JsonWithBytes.Chunked.Tree.Thms
public import Silmaril.Formats.Json.Fast.Defs
public import Silmaril.Formats.Json.Validate

/-! A canonical chunk-tree representation of the shared ordered JSON+bytes AST.
The `Canonical` invariant fixes shape, fullness and cached sizes recursively. -/

@[expose] public section
namespace Silmaril.Formats.JsonWithBytes.Chunked.Canonical

open Silmaril.ChunkSeq.Balanced
variable {Number : Type} [SizeOf Number]

def ofSimple (value : Ordered Number) : Canonical Number :=
  ⟨TreeValue.ofSimple value, congrArg TreeValue.ofSimple (TreeValue.toSimple_ofSimple value)⟩

def toSimple (value : Canonical Number) : Ordered Number := value.val.toSimple

def equiv : Canonical Number ≃ Ordered Number where
  toFun := toSimple
  invFun := ofSimple
  left_inv value := Subtype.ext value.property
  right_inv := TreeValue.toSimple_ofSimple

def scalar (value : Scalar Number) : Canonical Number := ofSimple (.scalar value)

def ofArray (items : List (Canonical Number)) : Canonical Number :=
  ⟨.list (Chunks.ofList 31 (items.map Subtype.val)), TreeValue.packed_array_canonical items⟩

def ofObject (entries : List (String × Canonical Number)) : Canonical Number :=
  ⟨.map (Chunks.ofList 31 (entries.map (fun entry => (entry.1, entry.2.val)))),
    TreeValue.packed_object_canonical entries⟩

/-- Explicit recursive duplicate rejection; the result uses the shared extensional map semantics. -/
def toUnordered (value : Canonical Number) : Except JsonError (Unordered Number) :=
  value.toSimple.validate

/-- Drop the production lookup cache, retaining ordered entries and exact scalars. The limit
counts container nesting only; this does not lex, reparse, or certify any source bytes. -/
def fromFast? : Nat → Json.Fast.Value → Option (Canonical JsonWire.Decimal)
  | _, .null => some (scalar .null)
  | _, .bool value => some (scalar (.bool value))
  | _, .string value => some (scalar (.string value))
  | _, .number value => some (scalar (.number value))
  | 0, .array _ | 0, .object _ _ => none
  | depth + 1, .array items => ofArray <$> items.toList.mapM (fromFast? depth)
  | depth + 1, .object entries _ => ofObject <$> entries.toList.mapM (fun (key, child) => do
      return (key, ← fromFast? depth child))

/-- The specification projection of a production data term, without chunk or cache metadata. -/
def orderedView? : Nat → Json.Fast.Value → Option Ordered
  | _, .null => some (.scalar .null)
  | _, .bool value => some (.scalar (.bool value))
  | _, .string value => some (.scalar (.string value))
  | _, .number value => some (.scalar (.number value))
  | 0, .array _ | 0, .object _ _ => none
  | depth + 1, .array items => (RawSyn.list ∘ RawSyn.ofList) <$> items.toList.mapM (orderedView? depth)
  | depth + 1, .object entries _ => (RawSyn.map ∘ RawSyn.ofEntries) <$> entries.toList.mapM (fun (key, child) => do
      return (key, ← orderedView? depth child))

end Silmaril.Formats.JsonWithBytes.Chunked.Canonical
