module

public import Silmaril.Cerberus.Ail.Syntax.Defs
public import Silmaril.Cerberus.Frontend.Desugar.TypePrint.Defs
public import Silmaril.Cerberus.Mem.Layout.Defs

/-! # C types for code generation

The C compiler keeps every scalar in a 64-bit register in **canonical form**: an
integer of width `w < 8` bytes is sign-extended (signed types) or zero-extended
(unsigned types and `_Bool`) from `8 w` bits; a pointer is its 64-bit linear-memory
address; a `float` is its binary32 encoding zero-extended from 32 bits, a `double` its
binary64 encoding (`Silmaril.Compile.C.FloatConst`). An aggregate (struct, union,
array) is represented by its address.

`CType` is the code generator's view of a C type: what conversions, loads and
arithmetic need. Integer layouts are Cerberus's LP64 ones
(`Silmaril.Cerberus.Mem.Concrete.integerLayout`, plain `char` signed); enumerated
types are `int`. Struct and union layouts come from
`Silmaril.Cerberus.Mem.Concrete.typeLayout`.

The typed-Ail annotations leave integer types symbolic (`GenIntegerType`: promotions,
usual arithmetic conversions, the types of constants); `resolve` computes them
(STD §6.3.1.1, §6.3.1.8, §6.4.4.1).
-/

@[expose] public section

namespace Silmaril.Compile.C

open Silmaril.Cerberus
open Silmaril.Cerberus.Ail
open Silmaril.Cerberus.Mem.Concrete (Tags typeLayout integerLayout)

/-- The code generator's view of a type. -/
inductive CType where
  /-- An integer of `width` bytes. -/
  | int (width : Nat) (signed : Bool)
  /-- `_Bool`: one byte holding 0 or 1. -/
  | bool
  /-- A real floating type of `width` bytes: 4 (`float`, binary32) or 8 (`double`,
  binary64). -/
  | float (width : Nat)
  /-- A pointer to `pointee`. -/
  | ptr (pointee : Ctype)
  /-- A struct, union or array: represented by its address. -/
  | agg (ty : Ctype)
  | void
  /-- A function designator (only under `&` or a call). -/
  | func (ty : Ctype)
  /-- A type the compiler does not support yet (`long double`). -/
  | unsupported (why : String)

instance : Inhabited CType := ⟨.void⟩

/-- `int`. -/
def CType.sint : CType := .int 4 true

/-- The width and signedness of an integer type, enums as `int`. -/
def intLayout : IntegerType → Nat × Bool
  | .enum _ => (4, true)
  | ty => (integerLayout ty).getD (4, true)

def ofIntegerType : IntegerType → CType
  | .bool => .bool
  | ty => let (w, s) := intLayout ty; .int w s

/-- The code generator's view of a real floating type. -/
def ofFloatingType : FloatingType → CType
  | .realFloating .float => .float 4
  | .realFloating .double => .float 8
  | .realFloating .longDouble => .unsupported "long double"

/-- The code generator's view of a C type. -/
def ofCtype : Ctype → CType
  | ty@(.mk _ node) =>
    match node with
    | .void => .void
    | .basic (.integer it) => ofIntegerType it
    | .basic (.floating ft) => ofFloatingType ft
    | .pointer _ t => .ptr t
    | .array _ _ | .struct _ | .union _ => .agg ty
    | .function .. | .functionNoParams _ => .func ty
    | .atomic t => ofCtype t
    | .byte => .int 1 false

/-- Integer promotion on (width, signedness): everything narrower than `int` becomes
`int` (STD §6.3.1.1#2; LP64 `int` represents all their values). -/
def promote : Nat × Bool → Nat × Bool
  | (w, s) => if w < 4 then (4, true) else (w, s)

/-- The usual arithmetic conversions on promoted integer types (STD §6.3.1.8#1), by
width: the wider type wins; at equal width, unsigned wins. -/
def usual (a b : Nat × Bool) : Nat × Bool :=
  let (wa, sa) := promote a
  let (wb, sb) := promote b
  if sa == sb then (max wa wb, sa)
  else
    let (wu, ws) := if sa then (wb, wa) else (wa, wb)
    if wu ≥ ws then (wu, false) else (ws, true)

/-- The type of an integer constant (STD §6.4.4.1#5), as (width, signedness). -/
def constantType : IntegerConstant → Nat × Bool
  | .max ty | .min ty => intLayout ty
  | .iconstant n basis suffix =>
    let fitsS (w : Nat) : Bool := n < 2 ^ (8 * w - 1)
    let fitsU (w : Nat) : Bool := n < 2 ^ (8 * w)
    let decimal := basis == .decimal
    match suffix with
    | none =>
      if fitsS 4 then (4, true)
      else if !decimal && fitsU 4 then (4, false)
      else if fitsS 8 then (8, true) else (8, false)
    | some .u | some .ul | some .ull =>
      if suffix == some .u && fitsU 4 then (4, false) else (8, false)
    | some .l | some .ll =>
      if fitsS 8 then (8, true) else (8, false)

/-- Resolve a generic integer type to (width, signedness). -/
def resolve : GenIntegerType → Nat × Bool
  | .concrete ty => intLayout ty
  | .sizeT => (8, false)
  | .ptrdiffT => (8, true)
  | .ptraddrT => (8, false)
  | .unknown c => constantType c
  | .promote g => promote (resolve g)
  | .usual a b => usual (resolve a) (resolve b)

/-- `_Bool` is kept apart from the other integer types. -/
def resolveIsBool : GenIntegerType → Bool
  | .concrete .bool => true
  | _ => false

/-- The code generator's view of a generic (rvalue) type. -/
def ofGenType : GenType → CType
  | .void => .void
  | .basic (.integer g) => if resolveIsBool g then .bool else let (w, s) := resolve g; .int w s
  | .basic (.floating ft) => ofFloatingType ft
  | .array elem n => .agg (.mk [] (.array elem n))
  | .function ret ps v => .func (.mk [] (.function ret ps v))
  | .functionNoParams ret => .func (.mk [] (.functionNoParams ret))
  | .pointer _ t => .ptr t
  | .struct tag => .agg (.mk [] (.struct tag))
  | .union tag => .agg (.mk [] (.union tag))
  | .atomic t => ofGenType t
  | .byte => .int 1 false

/-- The type of a typed-Ail expression. -/
def typeOf (e : TypedExpression) : CType :=
  match e.annotation with
  | .lvalue _ ty _ => ofCtype ty
  | .rvalue g => ofGenType g

/-- Integer (width, signedness) of a scalar type; pointers are unsigned 64-bit, and a
floating type is its encoding (an unsigned integer of its width). -/
def CType.intShape : CType → Nat × Bool
  | .int w s => (w, s)
  | .bool => (1, false)
  | .float w => (w, false)
  | _ => (8, false)

def CType.isPtr : CType → Bool
  | .ptr _ => true
  | _ => false

def CType.isFloat : CType → Bool
  | .float _ => true
  | _ => false

def CType.isScalar : CType → Bool
  | .int .. | .bool | .ptr _ | .float _ => true
  | _ => false

/-- The common real type of the usual arithmetic conversions when an operand is
floating (STD §6.3.1.8#1): the wider floating type. -/
def floatCommon (a b : CType) : Option CType :=
  match a, b with
  | .float x, .float y => some (.float (max x y))
  | .float x, _ | _, .float x => some (.float x)
  | _, _ => none

/-! ## Layout -/

/-- Replace enumerated types by `int`, which `typeLayout` needs registered. -/
def eraseEnums : Ctype → Ctype
  | .mk a node => .mk a (match node with
    | .basic (.integer (.enum _)) => .basic (.integer (.signed .int))
    | .array t n => .array (eraseEnums t) n
    | .atomic t => .atomic (eraseEnums t)
    | n => n)

/-- The struct and union definitions of a program, for `typeLayout`, with enumerated
member types replaced by `int`. -/
def tagsOf (σ : Ail.Sigma GenTypeCategory) : Tags :=
  let fixMembers := List.map fun (m : Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)) =>
    (m.1, (m.2.1, m.2.2.1, m.2.2.2.1, eraseEnums m.2.2.2.2))
  let fix : TagDefinition → TagDefinition
    | .struct ms fam => .struct (fixMembers ms) fam
    | .union ms => .union (fixMembers ms)
  { definitions := Map.ofList (σ.tagDefinitions.map fun (s, (l, _, d)) => (s, (l, fix d))) }

/-- Size and alignment of a complete type, in bytes. -/
def sizeAlign (tags : Tags) (ty : Ctype) : Except String (Nat × Nat) :=
  match ty with
  | .mk _ .void => .ok (1, 1)
  | .mk _ (.function ..) | .mk _ (.functionNoParams _) => .ok (1, 1)
  | _ =>
    match typeLayout 64 tags (eraseEnums ty) with
    | .ok l => .ok (l.size.toNat, l.align.toNat)
    | .error _ => .error s!"no layout for type '{Frontend.Desugar.TypePrint.stringOfCtype ⟨false, false, false⟩ ty}'"

/-- The largest explicit object alignment lowered; a stricter one rejects. -/
def maxObjectAlign : Nat := 65536

/-- Size and alignment of an object of type `ty` declared with alignment `a`
(`_Alignas`, or the `aligned` attribute of a frontend that keeps it): the stricter of
the type's and the declared alignment. An alignment specifier never weakens the
type's (STD §6.7.5#5), and `_Alignas(0)` has no effect (STD §6.7.5#6). -/
def objectLayout (tags : Tags) (ty : Ctype) (a : Option Alignment) : Except String (Nat × Nat) := do
  let (size, align) ← sizeAlign tags ty
  let declared ← match a with
    | none => pure 0
    | some (.integer n) =>
      if n < 0 then throw s!"negative alignment {n}" else pure n.toNat
    | some (.ctype t) => pure (← sizeAlign tags t).2
  let align := max align declared
  if align &&& (align - 1) != 0 then throw s!"alignment {align} is not a power of two"
  if align > maxObjectAlign then throw s!"alignment {align} exceeds {maxObjectAlign}"
  return (size, align)

/-- The offset and type of a struct or union member. -/
partial def memberOf (tags : Tags) (ty : Ctype) (m : Identifier) : Except String (Nat × Ctype) :=
  match ty with
  | .mk _ (.struct tag) =>
    match Mem.Concrete.memberOffsets 64 tags tag with
    | .ok ms => match ms.find? (fun (n, _, _) => n.name == m.name) with
      | some (_, t, off) => .ok (off.toNat, t)
      | none => .error s!"no member {m.name}"
    | .error _ => .error "no struct layout"
  | .mk _ (.union tag) =>
    match tags.lookup tag with
    | some (_, .union ms) => match ms.find? (fun (n, _) => n.name == m.name) with
      | some (_, (_, _, _, t)) => .ok (0, t)
      | none => .error s!"no member {m.name}"
    | _ => .error "no union definition"
  | .mk _ (.atomic t) => memberOf tags t m
  | _ => .error "member of a non-aggregate"

end Silmaril.Compile.C
