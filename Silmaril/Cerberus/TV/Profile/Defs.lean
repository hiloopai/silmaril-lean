module

public import Silmaril.Data.Layout.Defs
public import Silmaril.Cerberus.Target.Defs
public import Silmaril.Cerberus.NativeTypes.Defs
public import Silmaril.Cerberus.Mem.Layout.Defs
public import Silmaril.Cerberus.Spec.Allowed.Defs

/-!
# Target profiles for C translation validation, and their coherence with the Core semantics

A validation result is about the Lean port of Cerberus's Core semantics. Whether it says anything
about a real target (a compiler, an ABI, a data model) depends on whether the choices that
semantics makes agree with the target's. This module makes both sides explicit and compares them
type by type, instead of assuming a fixed data model.

**The target side** (`Profile`) is a selection of independent parameters:

* `dataModel`: the shared C data model `Silmaril.Data.Layout.DataModel` (sizes, *in-struct*
  alignments, signedness of plain `char` and `wchar_t`, endianness), used read-only here;
* `floatFormat`: the **numeric format** of each real floating kind (binary32, binary64, x87
  extended, binary128, …: `NativeTypes.Floating`), separate from its storage shape: x87
  `long double` has 80 value bits in 16 bytes of storage on x86-64 and 12 on i386. `none` means
  the format is not known for this profile (which is not the same as unsupported);
* `elaborator`: the `Cerberus.Target.Config` the Ail-to-Core elaborator is run with (it fixes
  integer ranges and `sizeof` constants it folds);
* `impl`: the implementation-defined choices observations depend on (`Spec.Impl`: exit status,
  `abort` flushing);
* `language`: the source language and dialect — **unchecked metadata**: nothing compares it, and
  it implies no support for that language revision.

ABI argument passing (classification of parameters into registers) is **not** part of a profile:
it is the ABI conformance shapes' business, and a numeric format says nothing about passing class.

**The semantics side** is fixed by the port: the concrete memory of `Core.Dynamics`
(`Mem.Concrete`) takes integer widths from `Mem.Concrete.integerLayout`, gives every pointer
8 bytes, gives **every real floating type 8 bytes with 8-byte alignment** (upstream's
`DefaultImpl`, `ocaml_implementation.ml:206-212`), stores integers little-endian, and computes
with floating values in binary64 (`coreFloatFormat`).

`Profile.issues p s` lists every disagreement for the scalar type `s`: storage size and alignment
(core memory vs data model, elaborator vs data model), signedness, the value range the dynamics
checks conversions and overflow against (two's complement of the target size; `_Bool`, whose
conversion Core special-cases, is not compared), endianness and numeric format.
`Profile.CoherentAt p s` (no issue) is decidable, so each row of the coherence table is a kernel
fact for a concrete profile. A validation result transfers to the target only for programs whose
object types are coherent; for every other type the result is about the legacy LP64 model of the
port, not the target. Nothing here silently replaces the port's 8-byte floats.

Coherence is **necessary, not sufficient**. `Profile.issues` compares scalar storage, alignment,
signedness, value range, endianness and floating format, and nothing else. Fixed inside the port
and not compared: conversion of out-of-range values to signed types, right shifts of negative
values and the other implementation-defined integer operations of the runtime (`impl` maps of
Cerberus's `gcc_4.9.0_x86_64-apple-darwin10.8.0` implementation), aggregate layout and padding,
bit-fields, pointer representation, and the allocator's addresses. `language` and the
`float128` entry of `floatFormat` are labels: nothing compares them yet.
-/

@[expose] public section

namespace Silmaril.Cerberus.TV

open Silmaril.Data.Layout (DataModel FloatKind IntKind Shape Endian)

/-- A numeric floating format. -/
abbrev FloatFormat := NativeTypes.Floating

/-- The bits that carry a value (sign, exponent and significand, including x87's explicit
integer bit); the rest of the storage is padding. -/
def FloatFormat.valueBits (f : FloatFormat) : Nat := (NativeTypes.Floating.layout f).valueBits

/-- The C standard revision. -/
inductive Std where
  | c89 | c99 | c11 | c17 | c23
  deriving DecidableEq, Repr

/-- Source language: the standard revision and whether GNU extensions are accepted. -/
structure Language where
  std : Std
  gnu : Bool := false
  deriving DecidableEq, Repr

/-- **A target profile** (module docstring). -/
structure Profile where
  name : String
  /-- Unchecked metadata (module docstring): compared with nothing. -/
  language : Language
  dataModel : DataModel
  /-- Numeric formats. The `float128` entry is unchecked metadata: no `Scalar` covers it. -/
  floatFormat : FloatKind → Option FloatFormat
  elaborator : Target.Config
  impl : Spec.Impl := {}

/-! ## Scalar types -/

/-- The scalar types the coherence table covers. -/
inductive Scalar where
  | bool | char | schar | uchar | short | ushort | int | uint | long | ulong
  | longLong | ulongLong | size | ptrdiff | intptr | uintptr | wchar
  | pointer | float | double | longDouble
  deriving DecidableEq, Repr

def Scalar.all : List Scalar :=
  [.bool, .char, .schar, .uchar, .short, .ushort, .int, .uint, .long, .ulong, .longLong,
    .ulongLong, .size, .ptrdiff, .intptr, .uintptr, .wchar, .pointer, .float, .double,
    .longDouble]

/-- The Cerberus integer type of an integer scalar. -/
def Scalar.integerType : Scalar → Option IntegerType
  | .bool => some .bool
  | .char => some .char
  | .schar => some (.signed .ichar)
  | .uchar => some (.unsigned .ichar)
  | .short => some (.signed .short)
  | .ushort => some (.unsigned .short)
  | .int => some (.signed .int)
  | .uint => some (.unsigned .int)
  | .long => some (.signed .long)
  | .ulong => some (.unsigned .long)
  | .longLong => some (.signed .longLong)
  | .ulongLong => some (.unsigned .longLong)
  | .size => some .size
  | .ptrdiff => some .ptrdiff
  | .intptr => some (.signed .intptr)
  | .uintptr => some (.unsigned .intptr)
  | .wchar => some .wchar
  | _ => none

/-- The data-model kind and written sign of an integer scalar. -/
def Scalar.intKind : Scalar → Option (IntKind × Data.Layout.Sign)
  | .char => some (.char, .plain)
  | .schar => some (.char, .signed)
  | .uchar => some (.char, .unsigned)
  | .short => some (.short, .signed)
  | .ushort => some (.short, .unsigned)
  | .int => some (.int, .signed)
  | .uint => some (.int, .unsigned)
  | .long => some (.long, .signed)
  | .ulong => some (.long, .unsigned)
  | .longLong => some (.longLong, .signed)
  | .ulongLong => some (.longLong, .unsigned)
  | .size => some (.size, .unsigned)
  | .ptrdiff => some (.ptrdiff, .signed)
  | .intptr => some (.intptr, .signed)
  | .uintptr => some (.intptr, .unsigned)
  | .wchar => some (.wchar, .plain)
  | _ => none

/-- The floating kind of a floating scalar. -/
def Scalar.floatKind : Scalar → Option (FloatKind × RealFloatingType)
  | .float => some (.float, .float)
  | .double => some (.double, .double)
  | .longDouble => some (.longDouble, .longDouble)
  | _ => none

/-- The Cerberus C type of a scalar (`void *` for `pointer`). -/
def Scalar.ctype (s : Scalar) : Ctype :=
  match s.integerType, s.floatKind with
  | some ity, _ => .mk [] (.basic (.integer ity))
  | none, some (_, r) => .mk [] (.basic (.floating (.realFloating r)))
  | none, none => .mk [] (.pointer ⟨false, false, false⟩ (.mk [] .void))

/-- The data model's shape and signedness of a scalar. -/
def Scalar.target (dm : DataModel) (s : Scalar) : Option (Shape × Option Bool) :=
  match s with
  | .bool => some (dm.bool, some false)
  | .pointer => some (dm.ptr, none)
  | _ => match s.intKind, s.floatKind with
    | some (k, sign), _ => (dm.intShape k).map fun sh => (sh, some (dm.isSigned k sign))
    | none, some (k, _) => (dm.floatShape k).map fun sh => (sh, none)
    | none, none => none

/-! ## The semantics side -/

/-- Size and alignment the Core semantics' concrete memory gives a scalar
(`Mem.Concrete.typeLayout`, the function the dynamics uses). -/
def coreShape (s : Scalar) : Option Shape :=
  match Mem.Concrete.typeLayout 2 ∅ s.ctype with
  | .ok l => some ⟨l.size.toNat, l.align.toNat⟩
  | .error _ => none

/-- Signedness the concrete memory gives an integer scalar (`Mem.Concrete.integerLayout`). -/
def coreSigned (s : Scalar) : Option Bool :=
  s.integerType.bind fun ity => (Mem.Concrete.integerLayout ity).map (·.2)

/-- The value range the concrete memory gives an integer scalar (`Mem.Concrete.integerBounds`,
used by the dynamics' conversions and overflow checks). -/
def coreRange (s : Scalar) : Option (Int × Int) :=
  s.integerType.bind Mem.Concrete.integerBounds

/-- The two's-complement range of `size` bytes. -/
def twosRange (size : Nat) (signed : Bool) : Int × Int :=
  if signed then (-(2 : Int) ^ (8 * size - 1), (2 : Int) ^ (8 * size - 1) - 1)
  else (0, (2 : Int) ^ (8 * size) - 1)

/-- The numeric format the Core semantics computes in: binary64 for every real floating type. -/
def coreFloatFormat (_ : FloatKind) : FloatFormat := .binary64

/-- The concrete memory stores integers little-endian. -/
def coreEndian : Endian := .little

/-- Size and alignment the elaborator's target configuration gives a scalar. -/
def elaboratorShape (config : Target.Config) (s : Scalar) : Option Shape :=
  let toShape (l : Target.Layout) : Shape := ⟨l.size, l.alignment⟩
  match s.integerType, s.floatKind with
  | some ity, _ => match Target.integerLayout config Target.emptyEnvironment ity with
    | .ok l => some (toShape l)
    | .error _ => none
  | none, some (_, r) => match Target.floatingLayout config (.realFloating r) with
    | .ok l => some (toShape l)
    | .error _ => none
  | none, none => config.pointerLayout.map toShape

/-! ## Coherence -/

/-- A disagreement between the semantics (or the elaborator) and the target, or a choice the
profile leaves unknown. -/
inductive Issue where
  | differs (what : String)
  | unknown (what : String)
  deriving DecidableEq, Repr

def showShape : Option Shape → String
  | some sh => s!"{sh.size}/{sh.align}"
  | none => "none"

/-- **Every disagreement for the scalar `s`** (module docstring). -/
def Profile.issues (p : Profile) (s : Scalar) : List Issue :=
  let tgt := s.target p.dataModel
  let tshape := tgt.map (·.1)
  let layout := if coreShape s = tshape then [] else
    [.differs s!"core memory {showShape (coreShape s)} vs data model {showShape tshape}"]
  let elabIssue := if elaboratorShape p.elaborator s = tshape then [] else
    [.differs s!"elaborator {showShape (elaboratorShape p.elaborator s)} vs data model {showShape tshape}"]
  let sign := match tgt.bind (·.2) with
    | some b => if coreSigned s = some b then [] else [.differs "signedness"]
    | none => []
  let range := match s, tgt with
    | .bool, _ => []
    | _, some (sh, some b) =>
        if coreRange s = some (twosRange sh.size b) then [] else
          [.differs s!"core value range {repr (coreRange s)} vs {repr (twosRange sh.size b)}"]
    | _, _ => []
  let endian := match tshape with
    | some sh => if sh.size > 1 && p.dataModel.endian != coreEndian then
        [.differs "the core memory is little-endian"] else []
    | none => []
  let format := match s.floatKind with
    | some (k, _) => match p.floatFormat k with
      | some f =>
          (if f = coreFloatFormat k then [] else
            [.differs s!"core computes in {repr (coreFloatFormat k)}, target format {repr f}"]) ++
          (match tshape with
            | some sh => if f.valueBits ≤ 8 * sh.size then [] else
                [.differs "format value bits exceed the storage size"]
            | none => [])
      | none => [.unknown "the profile gives no floating format"]
    | none => []
  layout ++ elabIssue ++ sign ++ range ++ endian ++ format

/-- **Coherence at a scalar type**: no issue. -/
def Profile.CoherentAt (p : Profile) (s : Scalar) : Prop := p.issues s = []

instance (p : Profile) (s : Scalar) : Decidable (p.CoherentAt s) :=
  inferInstanceAs (Decidable (p.issues s = []))

/-- The scalar types at which a profile is coherent. -/
def Profile.coherentScalars (p : Profile) : List Scalar :=
  Scalar.all.filter fun s => (p.issues s).isEmpty

/-- The scalar types at which it is not, with the issues. -/
def Profile.incoherent (p : Profile) : List (Scalar × List Issue) :=
  Scalar.all.filterMap fun s => match p.issues s with
    | [] => none
    | is => some (s, is)

end Silmaril.Cerberus.TV
