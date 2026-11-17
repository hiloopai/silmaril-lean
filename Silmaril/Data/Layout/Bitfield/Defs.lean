module

public import Silmaril.Data.Layout.Defs

/-!
# Bit-fields: bit-level placement under two ABIs

`Silmaril.Data.Layout` places ordinary members and rejects bit-fields (`Task.bitfieldLayout`).
This module places a struct or union **with** bit-fields, at bit granularity, under a
**bit-field policy**:

* `BitPolicy.sysv`: the System V AMD64 psABI §3.1.2 "Bit-Fields"
  (x86-psABIs/x86-64-ABI@e1ce098331da5dbd66e1ffc74162380bcc213236), with GCC 13.3's choices
  where the psABI leaves the rule to the implementation (only x86-64 is compared with a compiler
  here; i386, AArch64 and RISC-V are described as using the same rule, unmeasured): a bit-field of declared type `T` (size `s`, alignment `a`) of
  width `w > 0` starts at the current bit unless it would not fit in the `s`-byte storage unit
  aligned to `a` that contains the current bit, in which case it starts at the next `a`-aligned
  bit; a zero-width bit-field moves the current bit to the next `a`-aligned bit; **only named
  bit-fields** contribute `a` to the record's alignment; bit-fields of different types share
  storage units.
* `BitPolicy.ms`: Microsoft's allocation **as clang 18.1 emulates it** for
  `--target=x86_64-pc-windows-msvc` (clang's MSVC-compatible record layout; no layout here comes
  from `cl.exe`): bit-fields are packed into
  **storage units of their declared type**; a bit-field starts a new unit (aligned to its type)
  when the open unit's type size differs or the field does not fit; a zero-width bit-field closes
  the open unit (and is ignored when none is open); an ordinary member closes the open unit; every
  bit-field's type contributes its alignment, named or not, in a struct; in a union a bit-field
covers its whole storage unit and contributes no alignment.

Ordinary members are placed as `Silmaril.Data.Layout.place` places them, at the next byte aligned
for them; a union places every member at bit 0. The record's size is the end (in whole bytes)
rounded up to its alignment.

**Scope, refused rather than approximated** (an `Except.error` with the reason): a bit-field
wider than its type; a named zero-width bit-field; a bit-field of a type other than an integer,
`_Bool` or enum; `_Alignas` on a bit-field; members whose types are aggregates containing
bit-fields (`layoutTy` refuses them; only the declaration being laid out may have bit-fields);
`#pragma pack`, `__attribute__((packed))` and GCC's `ms_struct` are not represented.

Queries: `bitShapeOf` (`sizeof`, `_Alignof`); `offsetOf`, **C's `offsetof`**, which refuses
every bit-field (C17 7.19p3), wherever it lies; `bitOffsetOf`, the physical bit offset and width of
any named member (a layout query, not a C expression); `paddingBits` and `paddingBytes`, the bits
and the whole bytes no named member covers (unnamed bit-fields are padding, C17 6.7.2.1p12).

`msX64` (`Data.Layout.Defs`) is a data model, not a calling convention: Microsoft x64 argument passing is
`Silmaril.Machine.Abi.Win64`.

The result is a list of `BitSlot`s (name, bit offset, bit width; an ordinary member's width is
eight times its size) and the record's `Shape`. Well-formedness (slots in increasing order, pairwise
disjoint, inside the record) is `Thms.bitLayout_wf`; `Thms.bitfieldLayout` discharges
`Silmaril.Data.Layout.Task.bitfieldLayout`.
-/

@[expose] public section

namespace Silmaril.Data.Layout

/-- How an ABI allocates bit-fields (module doc). -/
inductive BitPolicy where
  | sysv
  | ms
  deriving DecidableEq, Repr

/-- A member to place: its name (`""` for an unnamed bit-field), its shape (with `_Alignas`
applied) and its bit-field width, if it is one. -/
structure BMember where
  name : String
  shape : Shape
  bits : Option Nat
  deriving DecidableEq, Repr

/-- A placed member, in bits. -/
structure BitSlot where
  name : String
  off : Nat
  width : Nat
  deriving DecidableEq, Repr

/-- The placement state: the current bit, the record's alignment so far, and (Microsoft) the
open storage unit (its first bit and its size in bytes). -/
structure BCur where
  pos : Nat
  align : Nat
  unit : Option (Nat × Nat)
  deriving DecidableEq, Repr

/-- The next multiple of `a` at or below `n` (identity for `a = 0`). -/
def alignDown (n a : Nat) : Nat := if a = 0 then n else n / a * a

/-- The first bit after the open unit (the current bit when none is open). -/
def BCur.base (c : BCur) : Nat :=
  match c.unit with
  | some (st, sz) => max c.pos (st + 8 * sz)
  | none => c.pos

/-- The width a member occupies, in bits. -/
def BMember.width (m : BMember) : Nat :=
  match m.bits with
  | some w => w
  | none => 8 * m.shape.size

/-- **One member of a struct** (module doc): its first bit and the next state. -/
def bitStep (pol : BitPolicy) (c : BCur) (m : BMember) : Except String (Nat × BCur) :=
  let s := m.shape
  match m.bits with
  | none =>
    let p := alignUp c.base (8 * s.align)
    .ok (p, ⟨p + 8 * s.size, max c.align s.align, none⟩)
  | some w =>
    if 8 * s.size < w then .error s!"bit-field {m.name}: width {w} exceeds its type ({s.size} bytes)"
    else if w = 0 ∧ m.name ≠ "" then .error s!"bit-field {m.name}: a named bit-field of width 0"
    else match pol with
    | .sysv =>
      if w = 0 then
        let p := alignUp c.pos (8 * s.align)
        .ok (p, ⟨p, c.align, none⟩)
      else
        let u := alignDown c.pos (8 * s.align)
        let p := if c.pos + w ≤ u + 8 * s.size then c.pos else alignUp c.pos (8 * s.align)
        .ok (p, ⟨p + w, if m.name = "" then c.align else max c.align s.align, none⟩)
    | .ms =>
      if w = 0 then .ok (c.base, ⟨c.base, c.align, none⟩)
      else match c.unit with
        | some (st, sz) =>
          if sz = s.size ∧ c.pos + w ≤ st + 8 * sz then
            .ok (c.pos, ⟨c.pos + w, max c.align s.align, some (st, sz)⟩)
          else
            let st' := alignUp c.base (8 * s.align)
            .ok (st', ⟨st' + w, max c.align s.align, some (st', s.size)⟩)
        | none =>
          let st' := alignUp c.pos (8 * s.align)
          .ok (st', ⟨st' + w, max c.align s.align, some (st', s.size)⟩)

/-- Members of a struct from a state, in order. -/
def bitPlace (pol : BitPolicy) : BCur → List BMember → Except String (List BitSlot × BCur)
  | c, [] => .ok ([], c)
  | c, m :: ms => match bitStep pol c m with
    | .error e => .error e
    | .ok (p, c') => match bitPlace pol c' ms with
      | .error e => .error e
      | .ok (ss, c'') => .ok (⟨m.name, p, m.width⟩ :: ss, c'')

/-- Whole bytes covering `n` bits. -/
def bytesOf (n : Nat) : Nat := (n + 7) / 8

/-- **A struct with bit-fields**: the slots and the record's shape. -/
def bitStruct (pol : BitPolicy) (ms : List BMember) : Except String (List BitSlot × Shape) :=
  match bitPlace pol ⟨0, 1, none⟩ ms with
  | .error e => .error e
  | .ok (ss, c) => .ok (ss, ⟨alignUp (bytesOf c.base) c.align, c.align⟩)

/-- A union member's contribution to the alignment: System V, every member but an unnamed
bit-field; Microsoft, ordinary members only (a bit-field adds none). -/
def unionAlign (pol : BitPolicy) (m : BMember) : Nat :=
  match pol, m.bits with
  | .sysv, some _ => if m.name = "" then 1 else m.shape.align
  | .ms, some _ => 1
  | _, _ => m.shape.align

/-- The bits a union member makes the union cover: its width, and under Microsoft a bit-field's
whole storage unit (its declared type). -/
def unionExtent (pol : BitPolicy) (m : BMember) : Nat :=
  match pol, m.bits with
  | .ms, some _ => max m.width (8 * m.shape.size)
  | _, _ => m.width

/-- **A union with bit-fields**: every member at bit 0. -/
def bitUnion (pol : BitPolicy) (ms : List BMember) : Except String (List BitSlot × Shape) :=
  if ms.any fun m => match m.bits with
      | some w => 8 * m.shape.size < w || (w == 0 && m.name != "")
      | none => false then
    .error "a bit-field wider than its type, or a named bit-field of width 0"
  else
    let a := ms.foldl (fun a m => max a (unionAlign pol m)) 1
    let e := ms.foldl (fun e m => max e (unionExtent pol m)) 0
    .ok (ms.map (fun m => ⟨m.name, 0, m.width⟩), ⟨alignUp (bytesOf e) a, a⟩)

def bitKind (pol : BitPolicy) : Kind → List BMember → Except String (List BitSlot × Shape)
  | .struct => bitStruct pol
  | .union => bitUnion pol

/-- Whether a type may hold a bit-field: integers, `_Bool` and enums (through typedefs). -/
def bitfieldType : CTy → Bool
  | .bool | .int .. | .enum .. => true
  | .typedef _ t => bitfieldType t
  | _ => false

/-- The members of a declaration with their shapes (`layoutTy`; nested aggregates must be
bit-field-free). -/
def bitMembers (dm : DataModel) (env : Env) : List Field → Except String (List BMember)
  | [] => .ok []
  | f :: fs => match layoutTy dm env defaultFuel f.ty with
    | .error e => .error e
    | .ok s =>
      let m : Except String BMember := match f.bits with
        | some w =>
          if !bitfieldType f.ty then .error s!"bit-field {f.name}: not an integer, _Bool or enum type"
          else if f.alignas.isSome then .error s!"bit-field {f.name}: _Alignas on a bit-field"
          else .ok ⟨f.name, s, some w⟩
        | none => match memberAlign s.align f.alignas with
          | .error e => .error e
          | .ok a => .ok ⟨f.name, ⟨s.size, a⟩, none⟩
      match m with
      | .error e => .error e
      | .ok m => match bitMembers dm env fs with
        | .error e => .error e
        | .ok ms => .ok (m :: ms)

/-- **The bit-level layout of a declaration** under a data model and a bit-field policy. -/
def bitLayout (pol : BitPolicy) (dm : DataModel) (env : Env) (d : Decl) :
    Except String (List BitSlot × Shape) :=
  match bitMembers dm env d.fields with
  | .error e => .error e
  | .ok ms => bitKind pol d.kind ms

/-! ## Queries: `sizeof`, `_Alignof`, `offsetof`, padding -/

/-- `sizeof` and `_Alignof` of a tag. -/
def bitShapeOf (pol : BitPolicy) (dm : DataModel) (env : Env) (k : Kind) (tag : String) :
    Except String Shape :=
  match env.find? k tag with
  | none => .error s!"no definition of {tag}"
  | some d => (bitLayout pol dm env d).map (·.2)

/-- **C's `offsetof`**: the byte offset of an ordinary member. A bit-field is refused, whatever
its position (also `unsigned x : 8` at offset 0): `offsetof` of a bit-field is undefined
(C17 7.19p3). The physical placement of any member, bit-fields included, is `bitOffsetOf`, a
layout query that is not a C expression. -/
def offsetOf (pol : BitPolicy) (dm : DataModel) (env : Env) (k : Kind) (tag member : String) :
    Except String Nat :=
  match env.find? k tag with
  | none => .error s!"no definition of {tag}"
  | some d => match d.fields.find? (·.name == member) with
    | none => .error s!"{tag} has no member {member}"
    | some f =>
      if f.bits.isSome then
        .error s!"{member} is a bit-field: offsetof is undefined for bit-fields (C17 7.19p3); use bitOffsetOf for its placement"
      else match bitLayout pol dm env d with
        | .error e => .error e
        | .ok (ss, _) => match ss.find? (·.name == member) with
          | none => .error s!"{tag} has no placed member {member}"
          | some s => .ok (s.off / 8)

/-- **Physical placement** of a named member under the policy: its bit offset from the start of
the object and its width in bits (eight times the size for an ordinary member). A layout
introspection query, defined for bit-fields too; it is not C's `offsetof`. -/
def bitOffsetOf (pol : BitPolicy) (dm : DataModel) (env : Env) (k : Kind) (tag member : String) :
    Except String (Nat × Nat) :=
  match env.find? k tag with
  | none => .error s!"no definition of {tag}"
  | some d => match bitLayout pol dm env d with
    | .error e => .error e
    | .ok (ss, _) => match ss.find? (fun s => s.name == member && member != "") with
      | none => .error s!"{tag} has no member {member}"
      | some s => .ok (s.off, s.width)

/-- **Padding bits** of a layout: the bits of the object representation (`8 * size` bits) that
**no named member** covers. They include alignment gaps, tail padding, the unused bits of
bit-field storage units, the bits of **unnamed** bit-fields (which are not members, C17
6.7.2.1p12), and, in a union, the bits beyond every member. -/
def paddingBits (ss : List BitSlot) (sh : Shape) : Nat :=
  ((List.range (8 * sh.size)).filter fun b =>
    !(ss.any fun s => s.name != "" && s.off ≤ b && b < s.off + s.width)).length

/-- **Padding bytes** of a layout: the bytes all eight of whose bits are padding bits. A byte
holding a few bits of a bit-field and some padding bits is not a padding byte; it contributes
its padding bits to `paddingBits` only. -/
def paddingBytes (ss : List BitSlot) (sh : Shape) : Nat :=
  ((List.range sh.size).filter fun i => (List.range 8).all fun j =>
    !(ss.any fun s => s.name != "" && s.off ≤ 8 * i + j && 8 * i + j < s.off + s.width)).length

end Silmaril.Data.Layout

namespace Silmaril.Data.Layout

/-- The placement `Task.bitfieldLayout` asks for: a struct's fields under the System V policy, as
(bit offset, bit width) pairs and the record's shape. -/
def bitfieldPlace (dm : DataModel) (env : Env) (fs : List Field) : Option (List (Nat × Nat) × Shape) :=
  match bitMembers dm env fs with
  | .error _ => none
  | .ok ms => match bitStruct .sysv ms with
    | .error _ => none
    | .ok (ss, sh) => some (ss.map fun s => (s.off, s.width), sh)

end Silmaril.Data.Layout
