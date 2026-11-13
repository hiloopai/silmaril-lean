module

public import Silmaril.Machine.SystemV.Abi.Ctypes.Defs
public import Silmaril.Cerberus.Ail.Syntax.Defs

/-! Native lowering and ABI classification use the same layout calculation.
This replaces the imported compiler's Cerberus-consumer layout shortcuts.
-/

@[expose] public section
namespace Silmaril.Compiler.Native.Layout

open Silmaril.Cerberus
open Silmaril.Cerberus.Mem.Concrete (Tags)
open Silmaril.Machine.SystemV.Abi

/-- Preserve native member types and reject tag-level attributes before they can
be erased by the imported compiler helper. Enum implementation registrations are
not present in Sigma; callers must supply them explicitly in the resulting Tags
before classifying enum objects. Missing registrations stay errors. -/
def tagsOf {α : Type} (sigma : Ail.Sigma α) : Except String Tags := do
  let mut definitions := []
  for (symbol, (location, attributes, definition)) in sigma.tagDefinitions do
    -- The imported frontend erases vectors to lane structs. Their source
    -- calling convention cannot be inferred from those member classes.
    if let .id name := symbol.description then
      if name.startsWith "__cfront_vector" then
        throw "native vector ABI needs retained frontend vector metadata"
    let .mk attributes := attributes
    unless attributes.isEmpty do
      throw "native tag attributes require resolved layout metadata"
    definitions := definitions ++ [(symbol, (location, definition))]
  return { definitions := Map.ofList definitions }

/-- Native sizeof/alignof of a complete object type. Void and function types
have no object layout; their old extension-sized placeholders are rejected. -/
def sizeAlign (tags : Tags) (type : Ctype) : Except String (Nat × Nat) := do
  let object ← objectOfCtype tags type
  return (object.size, object.align)

def maxObjectAlign : Nat := 65536

/-- Declared standalone-object alignment. The AMD64 rule raises local/global
arrays of at least sixteen bytes to alignment sixteen; member arrays keep their
ordinary element alignment. Explicit alignment never weakens natural alignment.
-/
def objectLayout (tags : Tags) (type : Ctype) (alignment : Option Alignment) :
    Except String (Nat × Nat) := do
  let (size, natural) ← sizeAlign tags type
  let natural := match type with
    | .mk _ (.array ..) => if size ≥ 16 then max 16 natural else natural
    | _ => natural
  let declared ← match alignment with
    | none => pure 0
    | some (.integer requested) =>
        if requested < 0 then throw "negative native object alignment"
        else if requested != 0 && !validAlignment requested.toNat then
          throw "declared native object alignment is not a power of two"
        else pure requested.toNat
    | some (.ctype alignmentType) => pure (← sizeAlign tags alignmentType).2
  let alignment := max natural declared
  unless validAlignment alignment do throw "native object alignment is not a nonzero power of two"
  if alignment > maxObjectAlign then throw "native object alignment exceeds compiler limit"
  return (size, alignment)

/-- Offsets come from the exact layout used by aggregate ABI classification.
Identity is the frontend's member spelling, matching its elaborated identifiers.
Atomic aggregate access requires separate native atomic metadata and is rejected.
-/
def memberOf (tags : Tags) (type : Ctype) (member : Identifier) :
    Except String (Nat × Ctype) := do
  let .mk _ node := type
  match node with
  | .struct _ | .union _ =>
      let layout ← layoutOfCtype tags type
      let some (_, fieldType, offset) := layout.members.find? fun (name, _, _) => name.name == member.name
        | throw s!"no native member {member.name}"
      return (offset, fieldType)
  | _ => throw "native member access requires a non-atomic aggregate"

end Silmaril.Compiler.Native.Layout
