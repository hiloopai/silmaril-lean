module

/-!
# Fixed-size bytes as C structs: declarations, data models, layouts

A small, executable model of C object layout, meant to be shared by every memory model that
stores C objects as bytes (x86 ELF process memories, Wasm linear memories, and later wire
formats).

* **Declarations** (`CTy`, `Field`, `Decl`, `Env`): C types with structs and unions by tag, as in
  C and in Cerberus (`Ctype` with `Tags`), fixed-size arrays, pointers,
  typedef names (kept for rendering, transparent for layout), enums, `_Alignas` and bit-field
  widths on members.
* **Data models** (`DataModel`): the size and alignment of every scalar and the per-ABI quirks:
  LP64 (`long` is 8 bytes) versus ILP32, `long double` (x87 16/16 on x86-64, binary128 16/16 on
  AArch64 and RISC-V, 12/4 on i386), the signedness of plain `char` and `wchar_t`, the enum
  representation, and the in-struct alignment of 8-byte scalars on i386 (4). Models:
  `sysvX86_64`, `aapcs64`, `rv64Lp64`, `i386Ilp32`, `wasm32`.
* **Layouts** (`layoutTy`, `declLayout`, `resolve`): the psABI padding discipline shared by the
  System V x86-64, AAPCS64 and RISC-V psABIs for ordinary members: each member is placed at
  the next multiple of its alignment, a struct is as aligned as its most aligned member and its
  size is rounded up to that alignment; union members all start at offset zero. Bit-fields are
  rejected (see `Task.bitfieldLayout` in `Thms`).

Well-formedness (members disjoint, in bounds, aligned) is proved in `Silmaril.Data.Layout.Thms`;
the byte view (read/write a field of a struct stored at an address, with frame lemmas) is in
`Silmaril.Data.Layout.Bytes`, bit-level specifications of integer fields in
`Silmaril.Data.Layout.Bits`.

## Design hooks for wire formats

A fixed layout is a *codec at fixed offsets*: every member is a byte range of a fixed-size
record (`PlacedField`), and the byte view reads and writes such ranges. Wire formats such as
protobuf replace fixed offsets by a *parsed* placement (tag, varint length, field order) and
fixed sizes by length-delimited ones. The intended extension keeps the same three layers:
declarations (a message schema), a placement function from a value to byte ranges (here
`declLayout`; there a serializer), and a lens per member with frame lemmas. The relational
codec laws of `Silmaril.Encoding` (`EncRel`) are the intended specification interface for
that variable-length placement; nothing here depends on it yet.
-/

@[expose] public section

namespace Silmaril.Data.Layout

/-! ## Declarations -/

/-- Integer kinds whose width the data model chooses. `exact n` is an exact-width
`intN_t`/`uintN_t` of `n` bytes; `int128` is `__int128`. -/
inductive IntKind where
  | char | short | int | long | longLong | int128
  | size | ptrdiff | intptr | wchar
  | exact (bytes : Nat)
  deriving DecidableEq, Repr

/-- Signedness as written: plain `char` (and an unadorned `wchar_t`) has the data model's
signedness. -/
inductive Sign where
  | signed | unsigned | plain
  deriving DecidableEq, Repr

/-- Real floating kinds. -/
inductive FloatKind where
  | float | double | longDouble | float128
  deriving DecidableEq, Repr

/-- C types. Structs, unions and enums are referred to by tag, resolved in an `Env`.
A `typedef` keeps its name for rendering and is transparent for layout. -/
inductive CTy where
  | void
  | bool
  | int (k : IntKind) (sign : Sign)
  | float (k : FloatKind)
  | ptr (to : CTy)
  | enum (tag : String) (underlying : Option (IntKind × Sign))
  | array (elem : CTy) (count : Nat)
  | struct (tag : String)
  | union (tag : String)
  | typedef (name : String) (ty : CTy)
  deriving DecidableEq, Repr

/-- A struct or union member: `_Alignas(alignas)` and a bit-field width are optional. -/
structure Field where
  name : String
  ty : CTy
  alignas : Option Nat := none
  bits : Option Nat := none
  deriving DecidableEq, Repr

/-- Struct or union. -/
inductive Kind where
  | struct | union
  deriving DecidableEq, Repr

/-- A tag definition. -/
structure Decl where
  kind : Kind
  tag : String
  fields : List Field
  deriving DecidableEq, Repr

/-- Tag definitions in scope. -/
abbrev Env := List Decl

def Env.find? (env : Env) (kind : Kind) (tag : String) : Option Decl :=
  List.find? (fun d => d.kind == kind && d.tag == tag) env

/-! ## Data models -/

/-- Size and alignment, in bytes. -/
structure Shape where
  size : Nat
  align : Nat
  deriving DecidableEq, Repr

inductive Endian where
  | little | big
  deriving DecidableEq, Repr

/-- A C data model and the psABI quirks a layout needs. `intShape`/`floatShape` return `none`
for a kind the ABI does not provide. Alignments are the *in-struct* (ABI) alignments, which on
i386 differ from GCC's `__alignof__` for `long long` and `double` (8 there, 4 in structs). -/
structure DataModel where
  name : String
  intShape : IntKind → Option Shape
  floatShape : FloatKind → Option Shape
  ptr : Shape
  bool : Shape
  /-- The implementation type of an enum without a fixed underlying type. The psABIs here
  use `int` when all values fit (GCC's default, no `-fshort-enums`). -/
  enumRepr : IntKind × Sign := (.int, .signed)
  charSigned : Bool
  wcharSigned : Bool
  endian : Endian := .little

/-- Natural shape of an exact-width integer: size = alignment. -/
def exactShape (bytes : Nat) : Option Shape :=
  if bytes = 1 ∨ bytes = 2 ∨ bytes = 4 ∨ bytes = 8 then some ⟨bytes, bytes⟩ else none

/-- System V AMD64 psABI §3.1.2 (Figure 3.1). `long double` is the x87 80-bit format in
16 bytes; plain `char` is signed. -/
def sysvX86_64 : DataModel where
  name := "x86_64 System V (LP64)"
  intShape
    | .char => some ⟨1, 1⟩ | .short => some ⟨2, 2⟩ | .int => some ⟨4, 4⟩
    | .long | .longLong | .size | .ptrdiff | .intptr => some ⟨8, 8⟩
    | .int128 => some ⟨16, 16⟩ | .wchar => some ⟨4, 4⟩
    | .exact n => exactShape n
  floatShape
    | .float => some ⟨4, 4⟩ | .double => some ⟨8, 8⟩
    | .longDouble => some ⟨16, 16⟩ | .float128 => some ⟨16, 16⟩
  ptr := ⟨8, 8⟩
  bool := ⟨1, 1⟩
  charSigned := true
  wcharSigned := true

/-- AAPCS64 (LP64, Linux): sizes as x86-64; `long double` is IEEE binary128 (16/16);
plain `char` and `wchar_t` are unsigned. -/
def aapcs64 : DataModel :=
  { sysvX86_64 with name := "AArch64 AAPCS64 (LP64)", charSigned := false, wcharSigned := false }

/-- RISC-V psABI, LP64 / LP64D: sizes as x86-64; `long double` is binary128 (16/16);
plain `char` is unsigned, `wchar_t` is signed `int`. -/
def rv64Lp64 : DataModel :=
  { sysvX86_64 with name := "RISC-V LP64", charSigned := false }

/-- i386 System V psABI as used by GCC on Linux (ILP32): `long` and pointers are 4 bytes;
`long long` and `double` are 8 bytes aligned to 4 *in structs*; `long double` is 12/4;
`__int128` does not exist. -/
def i386Ilp32 : DataModel where
  name := "i386 System V (ILP32)"
  intShape
    | .char => some ⟨1, 1⟩ | .short => some ⟨2, 2⟩ | .int => some ⟨4, 4⟩
    | .long | .size | .ptrdiff | .intptr => some ⟨4, 4⟩
    | .longLong => some ⟨8, 4⟩
    | .int128 => none | .wchar => some ⟨4, 4⟩
    | .exact n => if n = 8 then some ⟨8, 4⟩ else exactShape n
  floatShape
    | .float => some ⟨4, 4⟩ | .double => some ⟨8, 4⟩
    | .longDouble => some ⟨12, 4⟩ | .float128 => some ⟨16, 16⟩
  ptr := ⟨4, 4⟩
  bool := ⟨1, 1⟩
  charSigned := true
  wcharSigned := true

/-- WebAssembly C ABI (clang `wasm32`, ILP32): `long long` and `double` 8/8,
`long double` binary128 16/16, plain `char` signed. -/
def wasm32 : DataModel where
  name := "wasm32 (ILP32)"
  intShape
    | .char => some ⟨1, 1⟩ | .short => some ⟨2, 2⟩ | .int => some ⟨4, 4⟩
    | .long | .size | .ptrdiff | .intptr => some ⟨4, 4⟩
    | .longLong => some ⟨8, 8⟩
    | .int128 => some ⟨16, 16⟩ | .wchar => some ⟨4, 4⟩
    | .exact n => exactShape n
  floatShape
    | .float => some ⟨4, 4⟩ | .double => some ⟨8, 8⟩
    | .longDouble => some ⟨16, 16⟩ | .float128 => some ⟨16, 16⟩
  ptr := ⟨4, 4⟩
  bool := ⟨1, 1⟩
  charSigned := true
  wcharSigned := true

/-- Whether an integer of this kind and written sign is signed under the data model. -/
def DataModel.isSigned (dm : DataModel) (k : IntKind) : Sign → Bool
  | .signed => true
  | .unsigned => false
  | .plain => match k with
    | .char => dm.charSigned
    | .wchar => dm.wcharSigned
    | .size => false
    | _ => true

/-! ## Placement -/

/-- The next multiple of `a` (identity for `a = 0`). -/
def alignUp (n a : Nat) : Nat :=
  if a = 0 then n else ((n + a - 1) / a) * a

/-- A member's place: byte offset and shape. -/
structure Slot where
  off : Nat
  size : Nat
  align : Nat
  deriving DecidableEq, Repr

def Slot.endOff (s : Slot) : Nat := s.off + s.size

/-- Sequential placement from offset `off`: each member at the next multiple of its alignment. -/
def place (off : Nat) : List Shape → List Slot
  | [] => []
  | s :: ss =>
    let o := alignUp off s.align
    ⟨o, s.size, s.align⟩ :: place (o + s.size) ss

/-- The unpadded end of a sequential placement. -/
def placeEnd (off : Nat) : List Shape → Nat
  | [] => off
  | s :: ss => placeEnd (alignUp off s.align + s.size) ss

/-- The largest member alignment, at least 1. -/
def maxAlign : List Shape → Nat
  | [] => 1
  | s :: ss => max s.align (maxAlign ss)

/-- The largest member size. -/
def maxSize : List Shape → Nat
  | [] => 0
  | s :: ss => max s.size (maxSize ss)

/-- Struct placement: the record's shape and the members' slots. -/
def structPlace (ms : List Shape) : Shape × List Slot :=
  (⟨alignUp (placeEnd 0 ms) (maxAlign ms), maxAlign ms⟩, place 0 ms)

/-- Union placement: every member at offset zero. -/
def unionPlace (ms : List Shape) : Shape × List Slot :=
  (⟨alignUp (maxSize ms) (maxAlign ms), maxAlign ms⟩, ms.map fun s => ⟨0, s.size, s.align⟩)

def kindPlace : Kind → List Shape → Shape × List Slot
  | .struct => structPlace
  | .union => unionPlace

/-- Members in increasing order without overlap, all at or after `lo`. -/
def Chain : Nat → List Slot → Prop
  | _, [] => True
  | lo, s :: ss => lo ≤ s.off ∧ Chain (s.off + s.size) ss

/-- `n` is a power of two. -/
def Pow2 (n : Nat) : Prop := ∃ k, n = 2 ^ k

/-- Two data models lay out alike: same scalar shapes and enum representation (they may
differ in name, signedness of `char`/`wchar_t` and floating formats). -/
structure DataModel.SameLayout (dm dm' : DataModel) : Prop where
  int : dm.intShape = dm'.intShape
  float : dm.floatShape = dm'.floatShape
  ptr : dm.ptr = dm'.ptr
  bool : dm.bool = dm'.bool
  enumRepr : dm.enumRepr = dm'.enumRepr

/-- A complete object's shape: power-of-two alignment dividing the size. -/
structure Shape.WF (s : Shape) : Prop where
  pow2 : Pow2 s.align
  dvd : s.align ∣ s.size

/-- Every scalar the data model provides has a well-formed shape. -/
structure DataModel.WF (dm : DataModel) : Prop where
  int : ∀ k s, dm.intShape k = some s → s.WF
  float : ∀ k s, dm.floatShape k = some s → s.WF
  ptr : dm.ptr.WF
  bool : dm.bool.WF

/-! ## Layout computation -/

/-- Power-of-two test (alignments up to `2 ^ 63`). -/
def isPow2 (n : Nat) : Bool := (List.range 64).any fun k => 2 ^ k == n

/-- `Except.ok` on every element, in order (a proof-friendly `mapM`). -/
def traverse {α β : Type} (f : α → Except String β) : List α → Except String (List β)
  | [] => .ok []
  | a :: as => match f a with
    | .error e => .error e
    | .ok b => match traverse f as with
      | .error e => .error e
      | .ok bs => .ok (b :: bs)

/-- Shape of an integer kind with its data model. -/
def DataModel.intOf (dm : DataModel) (k : IntKind) : Except String Shape :=
  match dm.intShape k with
  | some s => .ok s
  | none => .error s!"the data model has no integer of kind {repr k}"

def DataModel.floatOf (dm : DataModel) (k : FloatKind) : Except String Shape :=
  match dm.floatShape k with
  | some s => .ok s
  | none => .error s!"the data model has no floating type {repr k}"

/-- The effective alignment of a member: `_Alignas` never weakens the natural alignment. -/
def memberAlign (natural : Nat) : Option Nat → Except String Nat
  | none => .ok natural
  | some a => if isPow2 a then .ok (max natural a) else .error "_Alignas is not a power of two"

/-- Member shapes with their effective alignment, given the shape of each member type. -/
def fieldShapes (g : CTy → Except String Shape) : List Field → Except String (List Shape)
  | [] => .ok []
  | f :: fs =>
    if f.bits.isSome then .error s!"bit-field {f.name}: see Task.bitfieldLayout" else
    match g f.ty with
    | .error err => .error err
    | .ok s => match memberAlign s.align f.alignas with
      | .error err => .error err
      | .ok a => match fieldShapes g fs with
        | .error err => .error err
        | .ok ss => .ok (⟨s.size, a⟩ :: ss)

section
variable (dm : DataModel) (env : Env)

/-- Shape of a complete object type. Fuel bounds tag lookups (as in Cerberus' `typeLayout`).
Void, flexible members and bit-fields are rejected. -/
def layoutTy : Nat → CTy → Except String Shape
  | 0, _ => .error "layout fuel exhausted"
  | _ + 1, .void => .error "void is not an object type"
  | _ + 1, .bool => .ok dm.bool
  | _ + 1, .int k _ => dm.intOf k
  | _ + 1, .float k => dm.floatOf k
  | _ + 1, .ptr _ => .ok dm.ptr
  | _ + 1, .enum _ none => dm.intOf dm.enumRepr.1
  | _ + 1, .enum _ (some (k, _)) => dm.intOf k
  | fuel + 1, .array e n => match layoutTy fuel e with
    | .ok s => .ok ⟨n * s.size, s.align⟩
    | .error err => .error err
  | fuel + 1, .typedef _ t => layoutTy fuel t
  | fuel + 1, .struct tag => match env.find? .struct tag with
    | none => .error s!"incomplete struct {tag}"
    | some d => match fieldShapes (layoutTy fuel) d.fields with
      | .ok ms => .ok (structPlace ms).1
      | .error err => .error err
  | fuel + 1, .union tag => match env.find? .union tag with
    | none => .error s!"incomplete union {tag}"
    | some d => match fieldShapes (layoutTy fuel) d.fields with
      | .ok ms => .ok (unionPlace ms).1
      | .error err => .error err

/-- Default fuel: nesting depth of tag lookups. -/
def defaultFuel : Nat := 64

/-- A member with its place. -/
structure PlacedField where
  name : String
  ty : CTy
  off : Nat
  size : Nat
  align : Nat
  deriving DecidableEq, Repr

def PlacedField.slot (f : PlacedField) : Slot := ⟨f.off, f.size, f.align⟩

/-- A tag definition with its layout. -/
structure DeclLayout where
  kind : Kind
  tag : String
  shape : Shape
  fields : List PlacedField
  deriving DecidableEq, Repr

/-- Layout of a declaration (with `defaultFuel` for its members). -/
def declLayout (d : Decl) : Except String DeclLayout :=
  match fieldShapes (layoutTy dm env defaultFuel) d.fields with
  | .error err => .error err
  | .ok ms =>
    let (shape, slots) := kindPlace d.kind ms
    .ok ⟨d.kind, d.tag, shape,
      (d.fields.zip slots).map fun (f, s) => ⟨f.name, f.ty, s.off, s.size, s.align⟩⟩

/-- Layout of the struct or union `tag` in `env`. -/
def tagLayout (kind : Kind) (tag : String) : Except String DeclLayout :=
  match env.find? kind tag with
  | none => .error s!"no definition of {tag}"
  | some d => declLayout dm env d

end

/-- Well-formedness of a computed layout: members in bounds and aligned (each member's
alignment divides its offset and the record's alignment), struct members pairwise disjoint in
declaration order, union members at offset zero, and a well-formed record shape. -/
structure DeclLayout.WF (L : DeclLayout) : Prop where
  shape : L.shape.WF
  inBounds : ∀ f ∈ L.fields, f.off + f.size ≤ L.shape.size
  aligned : ∀ f ∈ L.fields, f.align ∣ f.off
  alignDvd : ∀ f ∈ L.fields, f.align ∣ L.shape.align
  pow2 : ∀ f ∈ L.fields, Pow2 f.align
  disjoint : L.kind = .struct → L.fields.Pairwise fun f g => f.off + f.size ≤ g.off
  unionZero : L.kind = .union → ∀ f ∈ L.fields, f.off = 0

namespace DeclLayout

/-- The member called `name`. -/
def field? (L : DeclLayout) (name : String) : Option PlacedField :=
  L.fields.find? (·.name == name)

/-- Offset of member `name` (`offsetof`). -/
def offsetOf? (L : DeclLayout) (name : String) : Option Nat :=
  (L.field? name).map (·.off)

/-- Byte `k` of the record is padding: inside the record, outside every member. -/
def isPad (L : DeclLayout) (k : Nat) : Bool :=
  k < L.shape.size && L.fields.all fun f => !(f.off ≤ k && k < f.off + f.size)

/-- The padding bytes, in order. -/
def padding (L : DeclLayout) : List Nat :=
  (List.range L.shape.size).filter L.isPad

/-- `(name, offset, size)` of each member: the table DWARF and `pahole` print. -/
def table (L : DeclLayout) : List (String × Nat × Nat) :=
  L.fields.map fun f => (f.name, f.off, f.size)

end DeclLayout

/-! ## Member paths -/

/-- One step of a member designator: `.name` or `[i]`. -/
inductive Step where
  | field (name : String)
  | index (i : Nat)
  deriving DecidableEq, Repr

section
variable (dm : DataModel) (env : Env)

/-- Peel typedefs. -/
def CTy.strip : CTy → CTy
  | .typedef _ t => t.strip
  | t => t

/-- `offsetof(T, path)` and the designated subobject's type and shape. -/
def resolve : CTy → List Step → Except String (Nat × CTy × Shape)
  | t, [] => match layoutTy dm env defaultFuel t with
    | .ok s => .ok (0, t, s)
    | .error e => .error e
  | t, .index i :: p => match t.strip with
    | .array e n =>
      if i < n then match layoutTy dm env defaultFuel e, resolve e p with
        | .ok s, .ok (o, t', s') => .ok (i * s.size + o, t', s')
        | .error err, _ | _, .error err => .error err
      else .error s!"index {i} out of bounds {n}"
    | _ => .error "indexing a non-array"
  | t, .field name :: p =>
    let tag? : Option (Kind × String) := match t.strip with
      | .struct tag => some (.struct, tag)
      | .union tag => some (.union, tag)
      | _ => none
    match tag? with
    | none => .error s!"member {name} of a non-aggregate"
    | some (k, tag) => match tagLayout dm env k tag with
      | .error err => .error err
      | .ok L => match L.field? name with
        | none => .error s!"no member {name} in {tag}"
        | some f => match resolve f.ty p with
          | .ok (o, t', s') => .ok (f.off + o, t', s')
          | .error err => .error err

end

end Silmaril.Data.Layout
