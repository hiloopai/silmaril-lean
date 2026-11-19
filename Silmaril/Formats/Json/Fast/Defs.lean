module

public import Silmaril.Prelude.ChunkSeq.Defs
public import Silmaril.Formats.JsonWire.Defs
public import Init.Data.List.Sort.Impl

/-! Indexed scalar-Unicode JSON. `JsonWire` remains the source of truth for the unrestricted
wire vocabulary. This API retains order, duplicates and the exact same decimal representation.
The auxiliary object index holds source positions, never copies of the values. -/

@[expose] public section
namespace Silmaril.Formats.Json.Fast

open Silmaril

universe u

/-- The search key is a hash, not a proof of string equality. Collisions use exact equality
against the ordered entries. Positions within a bucket are in source order. -/
inductive KeyIndex where
  | empty
  | node (hash : Nat) (positions : Array Nat) (left right : KeyIndex)

def keyHash (key : String) : Nat :=
  key.toUTF8.data.foldl (fun acc byte => (acc * 257 + byte.toNat) % 4294967291) 0

namespace KeyIndex

def find? (hash : Nat) : KeyIndex → Option (Array Nat)
  | .empty => none
  | .node pivot positions left right =>
    if hash < pivot then left.find? hash
    else if pivot < hash then right.find? hash
    else some positions

def ofBuckets (buckets : Array (Nat × Array Nat)) : Nat → Nat → Nat → KeyIndex
  | 0, _, _ => .empty
  | fuel + 1, start, count =>
    if count == 0 then .empty
    else
      let mid := count / 2
      match buckets[start + mid]? with
      | none => .empty
      | some (hash, positions) =>
        .node hash positions (ofBuckets buckets fuel start mid)
          (ofBuckets buckets fuel (start + mid + 1) (count - mid - 1))

def ofEntries {α : Type u} (entries : Array (String × α)) : KeyIndex := Id.run do
  let mut hits := #[]
  for i in [:entries.size] do
    if let some (key, _) := entries[i]? then
      hits := hits.push (keyHash key, i)
  let sorted := hits.toList.mergeSort fun (hash, _) (other, _) => hash ≤ other
  let mut buckets := #[]
  let mut previous := 0
  let mut positions := #[]
  for (hash, pos) in sorted do
    if hash != previous && !positions.isEmpty then
      buckets := buckets.push (previous, positions)
      positions := #[]
    previous := hash
    positions := positions.push pos
  if !positions.isEmpty then buckets := buckets.push (previous, positions)
  return ofBuckets buckets buckets.size 0 buckets.size

end KeyIndex

inductive Value where
  | null
  | bool (value : Bool)
  | string (value : String)
  | number (value : JsonWire.Decimal)
  | array (items : ChunkSeq Value)
  /-- Use `Value.ofObject` to construct the consistent ordered entries and index. -/
  | object (entries : ChunkSeq (String × Value)) (index : Option KeyIndex)
  deriving Inhabited

namespace Value

def ofArray (items : Array Value) : Value := .array (ChunkSeq.ofArray items)

def ofObject (entries : Array (String × Value)) : Value :=
  .object (ChunkSeq.ofArray entries) (if entries.size ≤ 16 then none else some (KeyIndex.ofEntries entries))

def index? (value : Value) (i : Nat) : Option Value :=
  match value with
  | .array items => items.get? i
  | _ => none

def entries? : Value → Option (ChunkSeq (String × Value))
  | .object entries _ => some entries
  | _ => none

/-- Linear reference lookup: the first occurrence wins. -/
def memberLinear? (value : Value) (key : String) : Option Value := do
  (← value.entries?).findSome? fun (name, child) => if name == key then some child else none

/-- Select the first occurrence from an object built by `ofObject` (or by the parser). -/
def member? (value : Value) (key : String) : Option Value :=
  match value with
  | .object entries (some index) => do
    let positions ← index.find? (keyHash key)
    positions.findSome? fun pos => do
      let (name, child) ← entries.get? pos
      if name == key then some child else none
  | _ => value.memberLinear? key

def at? (value : Value) (path : JsonPath) : Option Value :=
  path.foldlM (fun value step => match step with
    | .key key => value.member? key
    | .index pos => value.index? pos) value

def string? : Value → Option String
  | .string text => some text
  | _ => none

def number? : Value → Option JsonWire.Decimal
  | .number decimal => some decimal
  | _ => none

def bool? : Value → Option Bool
  | .bool boolean => some boolean
  | _ => none

end Value
end Silmaril.Formats.Json.Fast
