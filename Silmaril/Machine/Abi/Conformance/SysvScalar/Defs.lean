module

public import Silmaril.Machine.Abi.Conformance.Defs
public import Silmaril.Machine.Abi.SystemV.Scalar.Thms
public import Silmaril.Data.Layout.Bitfield.Defs

/-!
# The System V scalar fragment, with small aggregates by value, as an ABI definition

**`sysvScalar`** extends `sysvInt` with the scalar floating types and with structs and unions
passed and returned **by value**:
* `float` and `double` are SSE class (psABI §3.2.3) and travel in XMM0–XMM7, mixed with
  INTEGER-class arguments in RDI…R9, each class counted separately;
* a struct or union is classified from its **member layout** in the header (`leavesOf`): the
  System V layout of the data model (`Data.Layout.bitLayout .sysv`, bit-fields included) gives
  each member's offset; nested structs, unions and arrays are **flattened** to their scalar
  leaves at bit offsets from the start of the outermost aggregate, and each leaf's class is
  merged into the eightbytes it overlaps by the ABI model's classifier
  (`SystemV.Abi.aggregate`: the §3.2.3 merge rules and post-merger cleanup, MEMORY over 16
  bytes or with an unaligned member). Flattening is what GCC's recursion with absolute bit
  offsets computes; a nested aggregate at an offset that is not a multiple of its alignment is
  refused. An aggregate of at most 16 bytes travels in one
  or two registers of its eightbytes' classes, or, if they do not all find a register, whole on
  the stack; a MEMORY aggregate is passed on the stack and returned through a hidden pointer
  (RDI in, RAX out);
* arguments that find no register take 8-byte stack slots in argument order; a result is in
  RAX/RDX (INTEGER) and XMM0/XMM1 (SSE), or at the hidden pointer.

The convention is `Machine.Abi.SystemV.Scalar.sysv`: the psABI planner (`plan`, whose closed
form on this fragment is `scalarPlan`) with the full `Ffi.Entry`/`Ffi.Return`/`Ffi.ResultAt`
discipline. The lowering reads tag definitions in the environment it is given; `Declares`
gives it the definitions of the same header that declares the prototype (`HeaderSrc.env`).

The floating types' sizes come from the data model (`DataModel.floatShape`): a 4-byte type is
IEEE binary32, an 8-byte type binary64. `lowerScalar` refuses, with a reason:
* `long double` (X87 and X87UP classes: passed in memory, returned in `%st0`), as a parameter,
  result or member;
* `__float128` (SSE and SSEUP classes) and `__int128`, likewise;
* as parameters and results: `_Bool`, `char`, `short`, enums, arrays (members of these types
  are classified);
* a struct or union with no definition in the environment (incomplete), with a zero-length or
  flexible array member, with an unnamed bit-field of nonzero width (padding the compilers
  classify differently), with a bit-field in a nested aggregate (`layoutTy` refuses them), with
  an eightbyte that holds no member (NO_CLASS), aligned to more than 8 bytes, or larger than
  `maxAggBytes`;
* varargs (the `%al` vector-register count and `va_list`).

**What a row does not cover.** The standard machines (`Open`, `Open9`) model no SSE
instruction, so code that reads an XMM argument or writes XMM0 is stuck on them and has no
`sysvScalar` row there. A row on such a machine is for code that receives floating arguments
and does not touch them (on an integer machine, `Mach.ofInt`, they are carried by
`callModelOf`, unchanged); a row about floating
computation needs a machine with SSE steps.

**Result storage.** The hidden pointer of a MEMORY result points at memory the callee owns
(`owned`: `[rdi, rdi + size)` at entry). `Ffi.SretAt` only places and aligns the pointer; the
conformance statement's `Stack` requires, of every admitted call, that each byte of it be
readable and writable and apart from the stack window, the code, its data, the image and the
call's caller-visible objects (`S.objects`): the psABI has the caller provide that space. That
such calls exist is `SysvScalar.Sret.admitted`, a concrete admitted call with a 24-byte
MEMORY result.

**Padding.** An aggregate's value is its object representation, padding bytes included; their
content is unspecified (`Machine.Abi.SystemV.Scalar`), so specs should not constrain them.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance

open Silmaril.Data.Layout (CTy DataModel Env)
open Silmaril.Data.Layout.Header (CProto)
open Silmaril.Machine.SystemV.Abi (Object Field aggregate)
open Silmaril.Machine.Abi.SystemV.Scalar (Kind Arg Agg Eights)

/-- The scalar of a C type under a data model, or why the scalar fragment has none. -/
def kindOf (dm : DataModel) : CTy → Except String Kind
  | .typedef _ t => kindOf dm t
  | .ptr _ => .ok .pointer
  | .int k s => match dm.intShape k with
    | some ⟨4, _⟩ => .ok (if dm.isSigned k s then .int32 else .uint32)
    | some ⟨8, _⟩ => .ok (if dm.isSigned k s then .int64 else .uint64)
    | some ⟨n, _⟩ => .error s!"{n}-byte integer: outside the scalar fragment (4- and 8-byte \
        integers, pointers, float and double)"
    | none => .error "integer kind without a size in the data model"
  | .float .longDouble => .error "long double: X87/X87UP class (passed in memory, returned in \
      %st0); outside the scalar fragment"
  | .float .float128 => .error "__float128: SSE/SSEUP class; outside the scalar fragment"
  | .float k => match dm.floatShape k with
    | some ⟨4, 4⟩ => .ok .float
    | some ⟨8, 8⟩ => .ok .double
    | some ⟨n, _⟩ => .error s!"{n}-byte floating type: outside the scalar fragment (binary32 \
        and binary64)"
    | none => .error "floating kind without a size in the data model"
  | .bool => .error "_Bool: outside the scalar fragment (4- and 8-byte integers, pointers, \
      float and double)"
  | .struct t => .error s!"struct {t} by value: aggregates are outside the scalar fragment"
  | .union t => .error s!"union {t} by value: aggregates are outside the scalar fragment"
  | .enum t _ => .error s!"enum {t}: enumerations are outside the scalar fragment"
  | .array .. => .error "array object type"
  | .void => .error "void object type"

/-- The ABI model's object of an INTEGER-class scalar of the given shape. -/
def intObject (s : Silmaril.Data.Layout.Shape) : Object := Object.integer s.size s.align

/-- The fields `fs` moved `k` bits further into the enclosing object. -/
def shiftFields (k : Nat) (fs : List Field) : List Field :=
  fs.map fun x => { x with offsetBits := x.offsetBits + k }

/-- A struct, union or array type (through typedefs). -/
def aggTy : CTy → Bool
  | .typedef _ t => aggTy t
  | .struct _ | .union _ | .array .. => true
  | _ => false

/-- The leaf fields of the members of a struct or union, each at its offset in the aggregate
(`slots`, from `bitLayout .sysv`): a named bit-field is one INTEGER leaf over its bits, any
other member contributes its own leaves (`leaf`, relative to its start) moved to its offset. A
member that is itself an aggregate (`aggTy`) must sit at a multiple of
its alignment, else the member list is refused (GCC classifies such a member MEMORY; the
fragment does not follow it). `bitLayout` represents no packing, so it never places one there:
the refusal is a guard. -/
def memberLeaves (leaf : CTy → Except String (Object × List Field)) :
    List (Silmaril.Data.Layout.Field × Silmaril.Data.Layout.BitSlot) → Except String (List Field)
  | [] => .ok []
  | (m, slot) :: rest =>
    let here : Except String (List Field) := match m.bits with
      | some 0 => .ok [⟨slot.off, intObject ⟨1, 1⟩, some 0⟩]
      | some w => if m.name = "" then
          .error "unnamed bit-field of nonzero width: outside the scalar fragment"
        else .ok [⟨slot.off, intObject ⟨1, 1⟩, some w⟩]
      | none => match leaf m.ty with
        | .error err => .error err
        | .ok (o, fs) =>
          if aggTy m.ty ∧ (o.align = 0 ∨ slot.off % (8 * o.align) ≠ 0) then
            .error s!"nested aggregate member {m.name} at bit offset {slot.off}, not a \
              multiple of its alignment: outside the scalar fragment"
          else .ok (shiftFields slot.off fs)
    match here, memberLeaves leaf rest with
    | .error err, _ => .error err
    | .ok _, .error err => .error err
    | .ok xs, .ok ys => .ok (xs ++ ys)

/-- **The classified object of a member type, with its leaves** (psABI §3.2.3) under the data
model, with the tag definitions of `env`. The leaves are the scalar fields of the object at
their **bit offsets from its start**: a scalar is one leaf (INTEGER for integers, `_Bool`,
enums and pointers; SSE for `float` and `double`); an array's leaves are its elements' leaves
at the elements' offsets; a struct's or union's are its members' leaves at the members'
offsets in the System V layout (`bitLayout .sysv`; a named bit-field is one INTEGER leaf over
the bits it occupies). An aggregate's object is the ABI model's classifier
(`SystemV.Abi.aggregate`) on its **leaves**, so a nested aggregate's members are merged into
the eightbytes of the outer object they actually overlap, as GCC's recursion with absolute
bit offsets does (`struct { float x; struct { int a; float b, c; } in; }` is INTEGER, SSE;
classifying `in` as a whole object relative to its own start would give INTEGER, INTEGER).
`fuel` bounds the nesting. -/
def leavesOf (dm : DataModel) (env : Env) : Nat → CTy → Except String (Object × List Field)
  | 0, _ => .error "aggregate nesting too deep"
  | f + 1, .typedef _ t => leavesOf dm env f t
  | _ + 1, .void => .error "void member"
  | _ + 1, .bool => scalar (intObject dm.bool)
  | _ + 1, .ptr _ => scalar (intObject dm.ptr)
  | _ + 1, .int .int128 _ => .error "__int128 member: a 16-byte-aligned INTEGER pair; outside \
      the scalar fragment"
  | _ + 1, .int k _ => match dm.intShape k with
    | some s => scalar (intObject s)
    | none => .error "integer kind without a size in the data model"
  | _ + 1, .enum _ u => match dm.intShape (match u with | some (k, _) => k | none => dm.enumRepr.1) with
    | some s => scalar (intObject s)
    | none => .error "enum representation without a size in the data model"
  | _ + 1, .float .longDouble => .error "long double member: X87/X87UP class; outside the \
      scalar fragment"
  | _ + 1, .float .float128 => .error "__float128 member: SSE/SSEUP class; outside the scalar \
      fragment"
  | _ + 1, .float k => match dm.floatShape k with
    | some ⟨4, 4⟩ => scalar (Object.floating .binary32)
    | some ⟨8, 8⟩ => scalar (Object.floating .binary64)
    | _ => .error "floating member outside binary32 and binary64"
  | f + 1, .array e n =>
    if n = 0 then .error "zero-length or flexible array member" else
    match leavesOf dm env f e with
    | .error err => .error err
    | .ok (o, fs) =>
      let leaves := (List.range n).flatMap fun i => shiftFields (8 * (i * o.size)) fs
      .ok (aggregate (n * o.size) o.align leaves, leaves)
  | f + 1, .struct tag => match env.find? .struct tag with
    | none => .error s!"struct {tag}: no definition (incomplete type)"
    | some d => match Silmaril.Data.Layout.bitLayout .sysv dm env d with
      | .error err => .error err
      | .ok (slots, shape) => match memberLeaves (leavesOf dm env f) (d.fields.zip slots) with
        | .error err => .error err
        | .ok fs => .ok (aggregate shape.size shape.align fs, fs)
  | f + 1, .union tag => match env.find? .union tag with
    | none => .error s!"union {tag}: no definition (incomplete type)"
    | some d => match Silmaril.Data.Layout.bitLayout .sysv dm env d with
      | .error err => .error err
      | .ok (slots, shape) => match memberLeaves (leavesOf dm env f) (d.fields.zip slots) with
        | .error err => .error err
        | .ok fs => .ok (aggregate shape.size shape.align fs, fs)
where
  /-- A scalar: its object, one leaf at offset 0. -/
  scalar (o : Object) : Except String (Object × List Field) := .ok (o, [⟨0, o, none⟩])

/-- The classified object of a member type (`leavesOf` without the leaves). -/
def objectOf (dm : DataModel) (env : Env) (fuel : Nat) (t : CTy) : Except String Object :=
  Prod.fst <$> leavesOf dm env fuel t

/-- A by-value struct or union (`name` its C spelling) as an argument of the fragment: its
classified object (`objectOf`), if its eightbytes are MEMORY or one or two INTEGER/SSE
eightbytes, its alignment at most 8 and its size at most `maxAggBytes`. -/
def aggArg (dm : DataModel) (env : Env) (name : String) (t : CTy) : Except String Arg :=
  match objectOf dm env Silmaril.Data.Layout.defaultFuel t with
  | .error e => .error s!"{name} by value: {e}"
  | .ok o => match Eights.ofClasses o.classes with
    | none => .error s!"{name} by value: an eightbyte of class NO_CLASS, X87 or SSEUP; outside \
        the scalar fragment"
    | some e =>
      let g : Agg := ⟨name, o.size, o.align, e⟩
      if h : g.ok = true then .ok (.agg g h)
      else .error s!"{name} by value: aligned to more than 8 bytes or larger than 2^32 bytes; \
        outside the scalar fragment"

/-- The argument of a C type: a scalar (`kindOf`) or a by-value struct or union (`aggArg`). -/
def argOf (dm : DataModel) (env : Env) : CTy → Except String Arg
  | .typedef _ t => argOf dm env t
  | .struct t => aggArg dm env s!"struct {t}" (.struct t)
  | .union t => aggArg dm env s!"union {t}" (.union t)
  | t => .scalar <$> kindOf dm t

/-- The scalar-fragment prototype of a C prototype, its structs and unions defined in `env`. -/
def lowerScalar (dm : DataModel) (env : Env) (cp : CProto) :
    Except String Silmaril.Machine.Abi.SystemV.Scalar.Proto :=
  if cp.variadic then
    .error "variadic: the %al vector-register count and va_list are outside the scalar fragment"
  else
    match Silmaril.Data.Layout.traverse (argOf dm env) cp.params,
        (match cp.ret with
          | .void => (Except.ok none : Except String (Option Arg))
          | t => some <$> argOf dm env t) with
    | .error e, _ => .error e
    | _, .error e => .error s!"result: {e}"
    | .ok ps, .ok r =>
      if h : ps.length ≤ Silmaril.Machine.Abi.SystemV.maxArity then .ok ⟨ps, r, h⟩
      else .error "more than 127 parameters"

/-- The bytes of a MEMORY result at the hidden pointer (none for other results). -/
def sretBytes (p : Silmaril.Machine.Abi.SystemV.Scalar.Proto) : Nat :=
  if p.indirect then (p.result.map Arg.size).getD 0 else 0

/-- **System V AMD64, scalar fragment with small aggregates**: fixed-arity prototypes of 4- and
8-byte integers, pointers, `float`, `double`, and structs and unions by value classified from
their layout, planned by the psABI planner (`scalarPlan`), with the full `Ffi.Entry`/`Ffi.Return`
discipline. Arguments without registers for all their eightbytes are 8-byte stack slots above
the return address; the callee owns that area, and the storage of a MEMORY result (at RDI on
entry). -/
def sysvScalar : AbiDef where
  id := "x86_64-sysv-psabi@e1ce0983/lp64/scalar-aggregates"
  source := "System V Application Binary Interface, AMD64 Architecture Processor Supplement, \
    x86-psABIs/x86-64-ABI@e1ce098331da5dbd66e1ffc74162380bcc213236, §3.2 (Function Calling \
    Sequence): register save and red zone (§3.2.1–3.2.2), parameter passing: classification \
    of INTEGER and SSE scalars and of aggregates and unions into eightbytes (INTEGER, SSE, \
    MEMORY), passing whole on the stack when registers run out, returning of values and the \
    hidden pointer of MEMORY results (§3.2.3)"
  dm := Silmaril.Data.Layout.sysvX86_64
  V := Silmaril.Machine.Abi.SystemV.Scalar.vocab
  D := Silmaril.Machine.Abi.SystemV.CallSite
  conv := Silmaril.Machine.Abi.SystemV.Scalar.sysv {}
  lower env := lowerScalar Silmaril.Data.Layout.sysvX86_64 env
  argArea p := p.stackBytes
  owned p s x := (s.machine.core.read .rdi).toNat ≤ x ∧
    x < (s.machine.core.read .rdi).toNat + sretBytes p

/-! ## Examples: one struct tag, two headers -/

/-- The prototype `A` lowers `f` to, with the header's tag definitions, if it does. -/
def HeaderSrc.lowered (hdr : HeaderSrc) (A : AbiDef) (f : String) : Option A.V.Proto :=
  (hdr.proto? f).bind fun cp => (A.lower hdr.env cp).toOption

/-- `long f(struct s)` with `s` two `long`s. -/
def tagHdrA : HeaderSrc := ⟨[("s.h", "struct s { long a; long b; }; long f(struct s v);")], "s.h"⟩

/-- `long f(struct s)` with `s` two `double`s. -/
def tagHdrB : HeaderSrc :=
  ⟨[("s.h", "struct s { double a; double b; }; long f(struct s v);")], "s.h"⟩

/-- The prototype `f` lowers to under `tagHdrB`: `struct s` is SSE, SSE. -/
def sseProto : Silmaril.Machine.Abi.SystemV.Scalar.Proto :=
  ⟨[.agg ⟨"struct s", 16, 8, .two true true⟩ (by decide)], some (.scalar .int64), by decide⟩

end Silmaril.Machine.Abi.Conformance

end
