module

public import Silmaril.Data.Layout.Defs
public import Silmaril.Cerberus.Mem.Layout.Defs

/-!
# Declarations as Cerberus C types

`toCtype` and `toTags` translate declarations into the Cerberus type vocabulary
(`Silmaril.Cerberus.Ctype`, tag definitions in `Mem.Concrete.Tags`), so a `Decl` can be
compared with Cerberus' concrete-memory layout `Mem.Concrete.typeLayout` (the LP64 layout of
Cerberus' `DefaultImpl`, `ocaml_implementation.ml`). Tags are numbered by their position in the
environment; typedef names are dropped (Cerberus resolves typedefs to annotations).

Outside the translated fragment (`none`): enums (Cerberus needs a registration in
`Tags.enums`), bit-fields, `__int128` and exact widths other than 1, 2, 4, 8 bytes.
Floating types translate, but Cerberus' concrete layout gives every real floating type
size and alignment 8 (`ocaml_implementation.ml:206-212`), unlike every psABI here
(`float` is 4/4, x86-64 `long double` 16/16); see `Cerberus.Thms.floatDisagreement`.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Cerb

open Silmaril.Cerberus
open Silmaril.Cerberus.Mem.Concrete (Tags TypeLayout typeLayout Failure)

def digest : Digest := ⟨[]⟩

def noQuals : Qualifiers := ⟨false, false, false⟩

def ident (s : String) : Identifier := ⟨.unknown, s⟩

/-- The position of a tag definition in the environment (or the length if absent). -/
def tagIndex (env : Env) (k : Kind) (tag : String) : Nat :=
  (env.findIdx? fun d => d.kind == k && d.tag == tag).getD env.length

def tagSym (env : Env) (k : Kind) (tag : String) : Sym :=
  ⟨digest, tagIndex env k tag, .id tag⟩

def intBase : IntKind → Option IntegerBaseType
  | .char => some .ichar | .short => some .short | .int => some .int | .long => some .long
  | .longLong => some .longLong | .intptr => some .intptr
  | .exact n => if n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 then some (.intN (8 * n)) else none
  | _ => none

def intType : IntKind → Sign → Option IntegerType
  | .char, .plain => some .char
  | .size, _ => some .size
  | .ptrdiff, _ => some .ptrdiff
  | .wchar, _ => some .wchar
  | k, .unsigned => (intBase k).map .unsigned
  | k, _ => (intBase k).map .signed

def floatType : FloatKind → Option RealFloatingType
  | .float => some .float | .double => some .double | .longDouble => some .longDouble
  | .float128 => none

/-- The Cerberus type of a declaration type. Pointer targets outside the fragment become
`void *` (a pointer's layout does not depend on its target). -/
def toCtype (env : Env) : CTy → Option Ctype
  | .void => some ⟨[], .void⟩
  | .bool => some ⟨[], .basic (.integer .bool)⟩
  | .int k s => (intType k s).map fun i => ⟨[], .basic (.integer i)⟩
  | .float k => (floatType k).map fun f => ⟨[], .basic (.floating (.realFloating f))⟩
  | .ptr t => some ⟨[], .pointer noQuals ((toCtype env t).getD ⟨[], .void⟩)⟩
  | .enum _ _ => none
  | .array e n => (toCtype env e).map fun c => ⟨[], .array c (some n)⟩
  | .struct tag => some ⟨[], .struct (tagSym env .struct tag)⟩
  | .union tag => some ⟨[], .union (tagSym env .union tag)⟩
  | .typedef _ t => toCtype env t

/-- A member: no attributes, `_Alignas` as an integer alignment. -/
def toMember (env : Env) (f : Field) :
    Option (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)) :=
  if f.bits.isSome then none else
  (toCtype env f.ty).map fun c =>
    (ident f.name, (.mk [], f.alignas.map fun a => .integer (Int.ofNat a), noQuals, c))

def toTagDef (env : Env) (d : Decl) : Option TagDefinition :=
  (d.fields.mapM (toMember env)).map fun ms => match d.kind with
    | .struct => .struct ms none
    | .union => .union ms

/-- The tag environment. -/
def toTags (env : Env) : Option Tags :=
  (env.mapM fun d => (toTagDef env d).map fun td => (tagSym env d.kind d.tag, (Loc.unknown, td))).map
    fun defs => { definitions := Map.ofList defs }

/-- Size, alignment and `(member, offset)` of a Cerberus layout. -/
def summary (r : Except Failure TypeLayout) : Option (Int × Int × List (String × Int)) :=
  match r with
  | .ok l => some (l.size, l.align, l.members.map fun (i, _, o) => (i.name, o))
  | .error _ => none

/-- Cerberus' layout of the struct or union `tag` of `env` (Cerberus' `alignment` and
`offsetsof` use fuel 64; one more here matches `declLayout`'s fuel for members). -/
def cerberusLayout (env : Env) (k : Kind) (tag : String) (fuel : Nat := defaultFuel + 1) :
    Option (Int × Int × List (String × Int)) :=
  (toTags env).bind fun tags =>
    summary (typeLayout fuel tags ⟨[], match k with
      | .struct => .struct (tagSym env .struct tag)
      | .union => .union (tagSym env .union tag)⟩)

/-- The same summary of our layout under a data model. -/
def ourLayout (dm : DataModel) (env : Env) (k : Kind) (tag : String) :
    Option (Int × Int × List (String × Int)) :=
  (tagLayout dm env k tag).toOption.map fun L =>
    (L.shape.size, L.shape.align,
      match k with
      | .struct => L.fields.map fun f => (f.name, (f.off : Int))
      | .union => [])

/-! ## The fragment where the layouts should agree -/

/-- Types whose System V layout Cerberus' concrete layout computes the same way: integers
and pointers, arrays, struct and union tags (no floating types, enums or `__int128`). -/
def inFragment : CTy → Bool
  | .bool | .ptr _ | .struct _ | .union _ => true
  | .int k s => (intType k s).isSome
  | .array e _ => inFragment e
  | .typedef _ t => inFragment t
  | .void | .float _ | .enum .. => false

/-- Tags are unique; every definition is nonempty (Cerberus rejects empty structs, GNU C gives
them size 0) with in-fragment members, no `_Alignas` and no bit-fields. -/
def Env.inFragment (env : Env) : Bool :=
  (env.map fun d => (d.kind, d.tag)).Nodup &&
    env.all fun d => !d.fields.isEmpty &&
      d.fields.all fun f => Cerb.inFragment f.ty && f.alignas.isNone && f.bits.isNone

end Silmaril.Data.Layout.Cerb
