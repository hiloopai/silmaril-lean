module

public import Silmaril.Formats.JsonWithBytes.Defs
public import Silmaril.Prelude.ChunkSeq.Balanced.Defs
import Silmaril.Proofs.Formats.JsonWithBytes.Chunked.Size

@[expose] public section
namespace Silmaril.Formats.JsonWithBytes.Chunked

open Silmaril.ChunkSeq.Balanced


inductive TreeValue (Number : Type) where
  | scalar (value : Scalar Number)
  | list (items : Chunks (TreeValue Number))
  | map (entries : Chunks (String × TreeValue Number))

variable {Number : Type}
def TreeValue.toSimple [SizeOf Number] : TreeValue Number → Ordered Number
  | .scalar value => .scalar value
  | .list items => .list (RawSyn.ofList (items.toList.attach.map fun ⟨item, _member⟩ => item.toSimple))
  | .map entries => .map (RawSyn.ofEntries (entries.toList.attach.map
      fun ⟨(key, item), _member⟩ => (key, item.toSimple)))
termination_by value => sizeOf value
decreasing_by
  · have := Proofs.Formats.JsonWithBytes.Chunked.chunks_mem_lt _member
    simp only [TreeValue.list.sizeOf_spec]
    omega
  · have := Proofs.Formats.JsonWithBytes.Chunked.chunks_mem_lt _member
    simp only [TreeValue.map.sizeOf_spec, Prod.mk.sizeOf_spec] at *
    omega

abbrev TreeValue.Packed (Number : Type) : JsonIx → Type
  | .val => TreeValue Number
  | .arr => Chunks (TreeValue Number) → Chunks (TreeValue Number)
  | .obj => Chunks (String × TreeValue Number) → Chunks (String × TreeValue Number)

def TreeValue.pack : {index : JsonIx} → RawSyn String (Scalar Number) index → Packed Number index
  | _, .scalar value => .scalar value
  | _, .list items => .list (pack items .empty)
  | _, .map entries => .map (pack entries .empty)
  | _, .nil => id
  | _, .cons item rest => fun acc => pack rest (acc.push 31 (pack item))
  | _, .objNil => id
  | _, .objCons key item rest => fun acc => pack rest (acc.push 31 (key, pack item))

def TreeValue.ofSimple (value : Ordered Number) : TreeValue Number := pack value

namespace TreeValue

def index? (value : TreeValue Number) (index : Nat) : Option (TreeValue Number) :=
  match value with | .list items => items.get? 31 index | _ => none

def entry? (value : TreeValue Number) (index : Nat) : Option (String × TreeValue Number) :=
  match value with | .map entries => entries.get? 31 index | _ => none

end TreeValue

/-- The exact recursively packed image, including chunk boundaries and cached sizes. -/
abbrev Canonical (Number : Type) [SizeOf Number] :=
  {value : TreeValue Number // TreeValue.ofSimple value.toSimple = value}

end Silmaril.Formats.JsonWithBytes.Chunked
