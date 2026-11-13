module

public import Silmaril.Machine.SystemV.Abi.Defs
public import Silmaril.Cerberus.Mem.Layout.Defs

/-! Native layouts of the imported Cerberus type vocabulary. Floating fields use
AMD64 native sizes, never `Mem.Concrete.typeLayout`'s eight-byte float shortcut.
The source AST omits complex/vector/bit-field constructors; those require richer
native type metadata, rather than guessing from their desugared storage types.
-/

@[expose] public section
namespace Silmaril.Machine.SystemV.Abi

open Silmaril.Cerberus
open Silmaril.Cerberus.Mem.Concrete (Tags)

def integerBytes (base : IntegerBaseType) : Except String Nat :=
  match base with
  | .ichar => .ok 1 | .short => .ok 2 | .int => .ok 4
  | .long | .longLong | .intmax | .intptr => .ok 8
  | .intLeastN _ | .intFastN _ =>
      .error "least/fast integer typedef requires its resolved implementation type"
  | .intN bits =>
      if bits == 8 || bits == 16 || bits == 32 || bits == 64 || bits == 128 then
        .ok (bits / 8)
      else .error "integer typedef needs its resolved native implementation type"

def annotationsSupported (annotations : List Annot) : Bool :=
  annotations.all fun annotation => match annotation with
    | .attrs (.mk attributes) => attributes.isEmpty
    | _ => true

def integerObject (tags : Tags) (type : IntegerType) : Except String Object := do
  match type with
  | .char | .bool => return .integer 1 1
  | .signed base | .unsigned base =>
      let bytes ← integerBytes base
      return .integer bytes bytes
  | .size | .ptrdiff | .ptraddr => return .integer 8 8
  | .wchar | .wint => return .integer 4 4
  | .enum tag =>
      let some underlying := tags.enums.lookup tag
        | throw "native enum ABI needs an explicit underlying type registration"
      match underlying with
      | .enum _ => throw "recursive enum implementation type"
      | .char | .bool => return .integer 1 1
      | .signed base | .unsigned base =>
          let bytes ← integerBytes base
          return .integer bytes bytes
      | .size | .ptrdiff | .ptraddr => return .integer 8 8
      | .wchar | .wint => return .integer 4 4

/-- Scalar native classes of an imported C type, before recursive record layout.
Function types and void are not complete object types. Native pointers include
function pointers and always use native 64-bit addresses. -/
def scalarObject (tags : Tags) (type : Ctype) : Except String Object := do
  let .mk annotations node := type
  unless annotationsSupported annotations do
    throw "native type attributes require resolved layout metadata"
  match node with
  | .basic (.integer type) => integerObject tags type
  | .basic (.floating (.realFloating .float)) => .ok (.floating .binary32)
  | .basic (.floating (.realFloating .double)) => .ok (.floating .binary64)
  | .basic (.floating (.realFloating .longDouble)) => .ok (.floating .x87)
  | .pointer .. => .ok .pointer
  | .byte => .ok (.integer 1 1)
  | _ => .error "not a native scalar object type"

/-- One native layout result serves both ABI classification and compiler field
addressing. Flexible members occur in `members` but add no storage bytes. -/
structure CtypeLayout where
  object : Object
  members : List (Identifier × Ctype × Nat) := []

/-- Native complete-object layout with explicit fuel for recursive tag lookup.
Unsupported attributes must be preserved and handled by the native frontend;
this adapter accepts ordinary fields and explicit alignments only. -/
def layoutOfCtypeWithFuel : Nat → Tags → Ctype → Except String CtypeLayout
  | 0, _, _ => .error "native C layout exhausted recursive tag fuel"
  | fuel + 1, tags, type@(.mk annotations node) => do
      unless annotationsSupported annotations do
        throw "native type attributes require resolved layout metadata"
      match node with
      | .atomic _ => throw "native atomic layout requires target lock-free/storage metadata"
      | .void | .function .. | .functionNoParams _ => throw "type is not a complete native object"
      | .basic _ | .pointer .. | .byte => return ⟨← scalarObject tags type, []⟩
      | .array element (some length) =>
          if length < 0 then throw "negative native array bound"
          let element := (← layoutOfCtypeWithFuel fuel tags element).object
          let count := length.toNat
          let size := count * element.size
          if size > 64 then return ⟨.memory size element.align, []⟩
          return ⟨aggregate size element.align ((List.range count).map fun index =>
            ⟨8 * index * element.size, element, none⟩), []⟩
      | .array _ none => throw "incomplete array has no by-value native object size"
      | .struct tag =>
          let some (_, .struct members flexible) := tags.lookup tag
            | throw "missing native struct definition"
          let mut offset := 0
          let mut alignment := 1
          let mut fields := []
          let mut nativeMembers := []
          for (name, (attributes, declared, _, fieldType)) in members do
            let .mk attrs := attributes
            unless attrs.isEmpty do throw "native field attributes require resolved layout metadata"
            let field := (← layoutOfCtypeWithFuel fuel tags fieldType).object
            let declared ← match declared with
              | none => pure field.align
              | some (.integer requestedAlignment) =>
                  if requestedAlignment < 0 then throw "negative native field alignment"
                  else if requestedAlignment != 0 && !validAlignment requestedAlignment.toNat then
                    throw "declared native field alignment is not a power of two"
                  else pure (max field.align requestedAlignment.toNat)
              | some (.ctype alignmentType) =>
                  pure (max field.align (← layoutOfCtypeWithFuel fuel tags alignmentType).object.align)
            unless validAlignment declared do throw "invalid native field alignment"
            offset := alignUp offset declared
            fields := fields ++ [⟨8 * offset, field, none⟩]
            nativeMembers := nativeMembers ++ [(name, fieldType, offset)]
            offset := offset + field.size
            alignment := max alignment declared
          if let some (.mk attributes name _ element) := flexible then
            let .mk attrs := attributes
            unless attrs.isEmpty do throw "native flexible member attributes need layout metadata"
            let flexible := (← layoutOfCtypeWithFuel fuel tags element).object
            alignment := max alignment flexible.align
            nativeMembers := nativeMembers ++ [(name, element, alignUp offset flexible.align)]
          return ⟨aggregate (alignUp offset alignment) alignment fields, nativeMembers⟩
      | .union tag =>
          let some (_, .union members) := tags.lookup tag
            | throw "missing native union definition"
          let mut size := 0
          let mut alignment := 1
          let mut fields := []
          let mut nativeMembers := []
          for (name, (attributes, declared, _, fieldType)) in members do
            let .mk attrs := attributes
            unless attrs.isEmpty do throw "native union attributes require resolved layout metadata"
            let field := (← layoutOfCtypeWithFuel fuel tags fieldType).object
            let declared ← match declared with
              | none => pure field.align
              | some (.integer requestedAlignment) =>
                  if requestedAlignment < 0 then throw "negative native union alignment"
                  else if requestedAlignment != 0 && !validAlignment requestedAlignment.toNat then
                    throw "declared native union alignment is not a power of two"
                  else pure (max field.align requestedAlignment.toNat)
              | some (.ctype alignmentType) =>
                  pure (max field.align (← layoutOfCtypeWithFuel fuel tags alignmentType).object.align)
            unless validAlignment declared do throw "invalid native union alignment"
            fields := fields ++ [⟨0, field, none⟩]
            nativeMembers := nativeMembers ++ [(name, fieldType, 0)]
            size := max size field.size
            alignment := max alignment declared
          return ⟨aggregate (alignUp size alignment) alignment fields, nativeMembers⟩

def objectOfCtypeWithFuel (fuel : Nat) (tags : Tags) (type : Ctype) : Except String Object :=
  (layoutOfCtypeWithFuel fuel tags type).map (·.object)

def layoutOfCtype (tags : Tags) (type : Ctype) : Except String CtypeLayout :=
  layoutOfCtypeWithFuel 256 tags type

def objectOfCtype (tags : Tags) (type : Ctype) : Except String Object :=
  (layoutOfCtype tags type).map (·.object)

end Silmaril.Machine.SystemV.Abi
