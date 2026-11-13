module

public import Silmaril.Compiler.C.Sem.C2.Defs
public import Silmaril.Compiler.C.Float.Defs
@[expose] public section

/-!
# C3: real floating types, on typed Ail

The fourth rung of the C semantics ladder. C3 extends C2 (`C2.lean`) with the
real floating types `float` (IEEE 754 binary32) and `double` (binary64) of x86-64 (System V,
SSE arithmetic: `FLT_EVAL_METHOD` 0, every operation rounds to its own type, to nearest-even).
A scalar of a floating type is its interchange encoding, a natural number, in the same slots as
C2's integers; the static type of every expression says which scalars are encodings. The
operations are those of `Silmaril.Compile.C.FloatConst` (the correctly rounded model of
`Silmaril.Numeric.Ieee754` that ccomp's constant folder uses). The **C3 fragment**
(`C3.InFragment`, decided by `C3.check`) adds to C2's:

* objects of type `float` and `double`: automatic, of static storage duration, members of
  arrays, structs and unions, parameters and results, with their initializers and constants
  (decimal and hexadecimal, suffix `f` or none);
* the usual arithmetic conversions to a floating type (STD §6.3.1.8), conversions between the
  floating types and to and from the integer types and `_Bool` (§6.3.1.4, §6.3.1.5);
* `+ - * /` and unary `-` and `+`, `++`/`--` and compound assignment, the relational and
  equality operators (a NaN is unordered, `-0.0 == 0.0`), and floating conditions (`if`,
  loops, `!`, `&&`, `||`, `?:`: a value is true when it is not a zero);
* the functions of `<math.h>` whose result IEEE 754 specifies exactly (`F.libm`): `fabs`,
  `floor`, `ceil`, `trunc`, `sqrt` and their `float` versions, declared with their prototypes;
* objects of type `long double` (16 bytes, aligned to 16), without their values: they can be
  laid out (a union member that aligns a buffer), copied as bytes and pointed to;
* `offsetof`.

Still outside: values of type `long double` and its constants (suffix `l`), complex types,
floating arguments of external functions other than those of `F.libm` (so `printf` of a
floating value), the other functions of `<math.h>`, floating arguments of calls without a
prototype, function pointers, `malloc` and variadic definitions.

## Choices

As in C2, plus the x86-64 choices of gcc: the layout of `float` is 4 bytes aligned to 4 and of
`double` 8 aligned to 8 (Cerberus's `typeLayout` gives every real floating type 8 bytes, so C3
lays out its types itself, `typeLayout`); a NaN operand of an arithmetic operation is returned
quieted (the first one when both are), an invalid operation returns the default NaN of SSE
(negative, quiet), a conversion between the formats keeps a NaN's sign and the top of its
payload; a floating value whose truncation is not representable in the integer type it is
converted to is undefined (STD §6.3.1.4#1), as are infinities and NaNs.

## Statement: C3 extends C2 on C2's fragment

The intended theorem of the rung is

  `C2.sem ⊑[C2.fragment] C3.sem`, i.e. `∀ p, C2.InFragment p → C2.beh p ⊆ C3.beh p`

(`Syntax.RefinesOn`): on a program of C2 no expression has a floating type, every conversion
`C3.conv` makes is C2's `convTo`, and the layout of every struct and union is Cerberus's (the
two layouts differ only on floating members), so C3's interpreter computes C2's results step by
step. `C3.check` accepts every program that `C2.check` accepts. `csem run` dispatches to C3 only
when C1 and C2 decline the program, so the `csem` campaign tests C3 on the programs it adds; the
refinement is not yet proved.
-/

namespace Silmaril.Compile.C.Sem.C3

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Compile.C
open Silmaril.Compile.Category
open Silmaril.Numeric.Ieee754 (F32 F64 RoundingMode)
open C0 (Stop ub Kont Result)
open C1 (Memory Env Place FunDef wrap convTo shape store base external externals plainString)
open C2 (Layout Agg Val Next aggOf lvType readAgg writeAgg depth)

/-! ## Floating values -/

namespace F

/-- The sign bit of format `w` (4: binary32, 8: binary64). -/
def signBit (w : Nat) : Nat := FloatConst.signBit w

/-- The exponent field of format `w`, all ones. -/
def expMask (w : Nat) : Nat := if w == 4 then 0x7f800000 else 0x7ff0000000000000

/-- The fraction field of format `w`. -/
def fracMask (w : Nat) : Nat := if w == 4 then 0x7fffff else 0xfffffffffffff

/-- The quiet bit of a NaN of format `w`. -/
def quietBit (w : Nat) : Nat := if w == 4 then 0x400000 else 0x8000000000000

/-- SSE's default NaN of format `w` (the "QNaN floating-point indefinite"): negative, quiet. -/
def defaultNaN (w : Nat) : Nat := if w == 4 then 0xffc00000 else 0xfff8000000000000

/-- Is the encoding `x` a NaN? -/
def isNaN (w x : Nat) : Bool := x &&& expMask w == expMask w && x &&& fracMask w != 0

/-- Is the encoding `x` true as a condition: not a zero of either sign (a NaN is true)? -/
def truth (w x : Nat) : Bool := x % signBit w != 0

/-- `-x`: the sign bit flipped. -/
def neg (w x : Nat) : Nat := x ^^^ signBit w

/-- `fabs`: the sign bit cleared. -/
def abs (w x : Nat) : Nat := x % signBit w

/-- The order of two encodings: `none` when one is a NaN; the two zeros are equal. -/
def cmp (w x y : Nat) : Option Ordering :=
  if isNaN w x || isNaN w y then none
  else
    let key (v : Nat) : Int :=
      if v ≥ signBit w then -((v - signBit w : Nat) : Int) else (v : Int)
    some (compare (key x) (key y))

/-- A relational or equality operator on two encodings. -/
def compareOp (op : BinaryOperator) (w x y : Nat) : Option Bool :=
  let o := cmp w x y
  match op with
  | .lt => some (o == some .lt)
  | .gt => some (o == some .gt)
  | .le => some (o == some .lt || o == some .eq)
  | .ge => some (o == some .gt || o == some .eq)
  | .eq => some (o == some .eq)
  | .ne => some (o != some .eq)
  | _ => none

/-- `x aop y` in format `w`, as SSE computes it: a NaN operand is returned quieted (the
first when both are), an invalid operation gives the default NaN. -/
def arith (w : Nat) (aop : ArithmeticOperator) (x y : Nat) : Except Stop Nat :=
  if isNaN w x then .ok (x ||| quietBit w)
  else if isNaN w y then .ok (y ||| quietBit w)
  else match FloatConst.binary w aop x y with
    | some r => .ok (if isNaN w r then defaultNaN w else r)
    | none => .error (.unsupported "a floating operator outside C3")

/-- Convert an encoding from format `src` to format `dst` (`cvtss2sd`, `cvtsd2ss`): a NaN keeps
its sign and the top of its payload, quieted. -/
def convert (src dst x : Nat) : Nat :=
  if (src == 4) == (dst == 4) then x
  else if isNaN src x then
    let sign := if x ≥ signBit src then signBit dst else 0
    let frac := x &&& fracMask src
    let frac := if src == 4 then frac <<< 29 else frac >>> 29
    sign ||| expMask dst ||| frac ||| quietBit dst
  else FloatConst.convert src dst x

/-- `x` rounded to an integral value in direction `mode` (`floor`, `ceil`, `trunc`): a NaN is
returned quieted, the sign of a zero is kept. -/
def integral (w : Nat) (mode : RoundingMode) (x : Nat) : Nat :=
  if isNaN w x then x ||| quietBit w
  else if w == 4 then (F32.roundIntegral mode ⟨x.toUInt32⟩).bits.toNat
  else (F64.roundIntegral mode ⟨x.toUInt64⟩).bits.toNat

/-- The correctly rounded square root (`sqrtss`, `sqrtsd`): a NaN is returned quieted, the
root of a negative number is the default NaN. -/
def sqrt (w x : Nat) : Nat :=
  if isNaN w x then x ||| quietBit w
  else
    let r := if w == 4 then (F32.sqrtWith .nearestTiesToEven ⟨x.toUInt32⟩).bits.toNat
      else (F64.sqrtWith .nearestTiesToEven ⟨x.toUInt64⟩).bits.toNat
    if isNaN w r then defaultNaN w else r

/-- The functions of `<math.h>` that C3 computes (exact, or correctly rounded): their format
and their value on an encoding. -/
def libm : String → Option (Nat × (Nat → Nat))
  | "fabs" => some (8, F.abs 8)
  | "fabsf" => some (4, F.abs 4)
  | "floor" => some (8, integral 8 .towardNegative)
  | "floorf" => some (4, integral 4 .towardNegative)
  | "ceil" => some (8, integral 8 .towardPositive)
  | "ceilf" => some (4, integral 4 .towardPositive)
  | "trunc" => some (8, integral 8 .towardZero)
  | "truncf" => some (4, integral 4 .towardZero)
  | "sqrt" => some (8, sqrt 8)
  | "sqrtf" => some (4, sqrt 4)
  | _ => none

end F

/-- The width of a real floating type of C3 (`float` 4, `double` 8); `long double` is
outside. -/
def floatWidth : RealFloatingType → Option Nat
  | .float => some 4
  | .double => some 8
  | .longDouble => none

/-- Convert a scalar of type `src` to type `dst` (`void`: discard). A value of an integer type
is its integer; a value of a floating type is its encoding. -/
def conv (src dst : CType) (v : Int) : Except Stop Int :=
  match src, dst with
  | .float s, .float d => .ok (F.convert s d v.toNat)
  | .float s, .bool => .ok (if F.truth s v.toNat then 1 else 0)
  | .float s, .int w sg =>
    match FloatConst.toInt? s v.toNat with
    | some n =>
      if C1.inRange w sg n then .ok n
      else ub "a floating value out of the range of the integer type it is converted to"
    | none => ub "an infinity or a NaN converted to an integer type"
  | .float _, .void => .ok 0
  | .float _, _ => .error (.unsupported "a floating value converted to a type outside C3")
  | .int .., .float d | .bool, .float d => .ok (FloatConst.ofInt d v)
  | _, .float _ => .error (.unsupported "a conversion to a floating type outside C3")
  | _, _ => convTo dst v

/-- Convert an integer (a constant's value) to the scalar type `dst`. -/
def ofInt (dst : CType) (v : Int) : Except Stop Int := conv (.int 8 true) dst v

/-- Is a value of type `t` true as a condition? -/
def truthOf (t : CType) (v : Int) : Bool :=
  match t with
  | .float w => F.truth w v.toNat
  | _ => v != 0

/-- The encoding of a floating constant (`f`: `float`, none: `double`) and its format. -/
def floatConst : FloatingConstant → Except Stop (Nat × Nat)
  | (text, sfx) =>
    let w := if sfx == some .f then 4 else 8
    if sfx == some .l then .error (.unsupported "a long double constant")
    else match FloatConst.parse w text with
      | some x => .ok (w, x)
      | none => .error (.unsupported s!"a floating constant {text} outside C3")

/-! ## Memory -/

/-- The width in bytes of a scalar type of C3 (C1's, and the floating types). -/
def width : CType → Option Nat
  | .float w => some w
  | t => C1.width t

/-- Load a scalar of type `t` at `a`. -/
def load (m : Memory) (t : CType) (a : Nat) : Except Stop Int :=
  match t with
  | .float w => do return Memory.ofLE (← m.readBytes a w)
  | _ => C1.load m t a

/-- Store a scalar of type `t` (already converted) at `a`. -/
def storeV (m : Memory) (t : CType) (a : Nat) (v : Int) : Except Stop Memory :=
  match t with
  | .float w => m.writeBytes a (Memory.le w v)
  | _ => store m t a v

/-- Read a place. -/
def readPlace (fd : FunDef) (env : Env) (t : CType) : Place → Except Stop Int
  | .reg x =>
    match env.regs[x]? with
    | some v => .ok v
    | none => if fd.locals.contains x then ub "read of an uninitialised local"
              else .error (.unsupported "an object outside the fragment")
  | .mem a => load env.mem t a

/-- Write a place (the value already converted to `t`). -/
def writePlace (env : Env) (t : CType) (v : Int) : Place → Except Stop Env
  | .reg x => .ok (env.setReg x v)
  | .mem a => env.withMem (storeV · t a v)

/-! ## Layout -/

/-- Size, alignment and (for a struct) member offsets of a type, LP64 as gcc lays it out on
x86-64: Cerberus's `typeLayout` with `float` of 4 bytes aligned to 4. -/
def typeLayout (tags : Mem.Concrete.Tags) :
    Nat → Ctype → Except String (Nat × Nat × List (Identifier × Ctype × Nat))
  | 0, _ => .error "a type nested too deeply"
  | n + 1, .mk _ node =>
    match node with
    | .basic (.integer it) => let (w, _) := intLayout it; .ok (w, w, [])
    | .basic (.floating (.realFloating ft)) =>
      let w := (floatWidth ft).getD 16
      .ok (w, w, [])
    | .pointer .. => .ok (8, 8, [])
    | .byte => .ok (1, 1, [])
    | .atomic t => typeLayout tags n t
    | .array t (some k) => do
      if k < 0 then throw "a negative array length"
      let (size, align, _) ← typeLayout tags n t
      return (k.toNat * size, align, [])
    | .struct tag =>
      match tags.lookup tag with
      | some (_, .struct ms none) => do
        let mut off := 0
        let mut align := 0
        let mut out : Array (Identifier × Ctype × Nat) := #[]
        for (m, (_, al, _, t)) in ms do
          if al.isSome then throw "a member with an alignment specifier"
          let (size, a, _) ← typeLayout tags n t
          off := C1.alignUp off a
          out := out.push (m, t, off)
          off := off + size
          align := max align a
        if align == 0 then throw "an empty struct"
        return (C1.alignUp off align, align, out.toList)
      | _ => .error "a struct without a definition of C3"
    | .union tag =>
      match tags.lookup tag with
      | some (_, .union ms) => do
        let mut size := 0
        let mut align := 0
        for (_, (_, al, _, t)) in ms do
          if al.isSome then throw "a member with an alignment specifier"
          let (s, a, _) ← typeLayout tags n t
          size := max size s
          align := max align a
        if align == 0 then throw "an empty union"
        return (C1.alignUp size align, align, [])
      | _ => .error "a union without a definition"
    | _ => .error "a type without a layout"

/-- The layout of the struct and union definitions of a program (`C2.layoutOf`, with C3's
`typeLayout`). -/
def layoutOf (σ : Ail.Sigma GenTypeCategory) : Layout := Id.run do
  let tags := tagsOf σ
  let mut L : Layout := {}
  for (s, (_, attrs, d)) in σ.tagDefinitions do
    if attrs != .mk [] then continue
    let ty : Ctype := .mk [] (match d with | .struct .. => .struct s | .union _ => .union s)
    let .ok (size, align, offs) := typeLayout tags depth ty | continue
    match d with
    | .struct ms none =>
      if ms.any (fun (_, (a, al, _, _)) => a != .mk [] || al.isSome) then continue
      L := { L with sizes := L.sizes.insert s.number (size, align),
                    fields := L.fields.insert s.number (ms.map fun (_, (_, _, _, t)) => t) }
      for (m, t, off) in offs do
        L := { L with members := L.members.insert (s.number, m.name) (off, t) }
    | .struct _ (some _) => pure ()
    | .union ms =>
      if ms.any (fun (_, (a, al, _, _)) => a != .mk [] || al.isSome) then continue
      L := { L with sizes := L.sizes.insert s.number (size, align),
                    fields := L.fields.insert s.number (ms.map fun (_, (_, _, _, t)) => t) }
      for (m, (_, _, _, t)) in ms do
        L := { L with members := L.members.insert (s.number, m.name) (0, t) }
  return L

/-- Size and alignment of a type, structs and unions from the layout. -/
def sizeAlignOf (L : Layout) : Nat → Ctype → Except String (Nat × Nat)
  | 0, _ => .error "a type nested too deeply"
  | n + 1, .mk _ node =>
    match node with
    | .basic (.integer it) => let (w, _) := intLayout it; .ok (w, w)
    | .basic (.floating (.realFloating ft)) =>
      let w := (floatWidth ft).getD 16
      .ok (w, w)
    | .pointer .. => .ok (8, 8)
    | .byte | .void | .function .. | .functionNoParams _ => .ok (1, 1)
    | .atomic t => sizeAlignOf L n t
    | .array t (some k) => do
      if k < 0 then throw "a negative array length"
      let (size, align) ← sizeAlignOf L n t
      return (k.toNat * size, align)
    | .struct tag | .union tag =>
      match L.sizes[tag.number]? with
      | some sa => .ok sa
      | none => .error "a struct or union outside C3"
    | _ => .error "a type without a layout"

mutual
/-- Is `t` the type of an object of C3: an integer, a real floating type (a `long double`
object has no value in C3, but it can be laid out, copied and pointed to), a pointer to an object
type of C3, to a struct or union or to `void`, an array of known size of objects of C3, or a
struct or union of C3 whose members are objects of C3? -/
def objType (L : Layout) : Nat → Ctype → Bool
  | 0, _ => false
  | n + 1, .mk _ node =>
    match node with
    | .basic (.integer _) => true
    | .basic (.floating (.realFloating _)) => true
    | .pointer _ t => pointee L n t
    | .array t (some _) => objType L n t
    | .struct tag | .union tag =>
      match L.fields[tag.number]? with
      | some ts => ts.all (objType L n ·)
      | none => false
    | _ => false
/-- Can `t` be pointed to? -/
def pointee (L : Layout) : Nat → Ctype → Bool
  | 0, _ => false
  | n + 1, t@(.mk _ node) =>
    match node with
    | .void | .struct _ | .union _ => true
    | _ => objType L n t
end

/-! ## Programs -/

/-- A prepared program: C2's, with C3's layout. -/
structure Prog extends toC2 : C2.Prog

/-- Size and alignment of a type. -/
def Prog.sizeAlign (P : Prog) (ty : Ctype) : Except Stop (Nat × Nat) :=
  (sizeAlignOf P.layout depth ty).mapError Stop.unsupported

/-- The size of the pointee of a pointer type, for pointer arithmetic (`void`: 1). -/
def Prog.pointee (P : Prog) : CType → Except Stop Nat
  | .ptr ty => do return max 1 (← P.sizeAlign ty).1
  | _ => throw (.unsupported "pointer arithmetic on a non-pointer")

/-- Is `t` the type of an object of C3? -/
def Prog.obj (P : Prog) (t : Ctype) : Bool := objType P.layout depth t

/-- Prepare a typed-Ail program and lay out its static memory (`C2.prepare`, with C3's layout
and floating locals in registers). -/
def prepare (p : TypedProgram) : Prog := Id.run do
  let σ := p.2
  let tags := tagsOf σ
  let layout := layoutOf σ
  let sizeOf (ty : Ctype) : Except String (Nat × Nat) := sizeAlignOf layout depth ty
  let mut protos : Std.HashMap Nat (List CType) := {}
  let mut pctys : Std.HashMap Nat (List Ctype) := {}
  let mut rets : Std.HashMap Nat CType := {}
  let mut names : Std.HashMap Nat String := {}
  let mut statics : Array (Nat × Ctype × Option TypedExpression) := #[]
  let inits : Std.HashMap Nat TypedExpression :=
    σ.objectDefinitions.foldl (fun m (x, e) => m.insert x.number e) {}
  for (x, (_, _, d)) in σ.declarations do
    names := names.insert x.number (Silmaril.Compile.Forks.Csem.C.symName x)
    match d with
    | .function _ (_, ret) ps _ _ _ =>
      protos := protos.insert x.number (ps.map fun (_, t, _) => ofCtype t)
      pctys := pctys.insert x.number (ps.map fun (_, t, _) => t)
      rets := rets.insert x.number (ofCtype ret)
    | .object (dur, _) _ _ ty =>
      if dur != .automatic then statics := statics.push (x.number, ty, inits[x.number]?)
  let mut lits : List (List UInt8) := []
  for (_, e) in σ.objectDefinitions do
    lits := lits ++ (C2.scanE e).1
  let mut funcs : Std.HashMap Nat FunDef := {}
  for (x, fd) in σ.functionDefinitions do
    let pts := (protos[x.number]?).getD []
    let pcs := (pctys[x.number]?).getD []
    let params := fd.params.zipIdx.map fun (y, i) => (y.number, (pts[i]?).getD (.int 4 true))
    let blockLocals := C1.localsS fd.body
    let locals := blockLocals.foldl (fun m (n, t) => m.insert n (ofCtype t))
      (params.foldl (fun m (n, t) => m.insert n t) {})
    let (ls, taken) := C2.scanS fd.body
    lits := lits ++ ls
    let all := fd.params.zipIdx.map (fun (y, i) => (y.number, (pcs[i]?).getD (.mk [] .void)))
      ++ blockLocals
    let memLocals := all.filter fun (n, t) =>
      taken.contains n || (width (ofCtype t)).isNone
    funcs := funcs.insert x.number
      { params, ret := (rets[x.number]?).getD (.int 4 true), body := fd.body, locals,
        memLocals, inMem := memLocals.foldl (fun s (n, _) => s.insert n) {} }
  -- layout: string literals, objects of static storage duration, argv
  let mut a := base
  let mut strs : Std.HashMap (List UInt8) Nat := {}
  for l in lits do
    if !strs.contains l then
      strs := strs.insert l a
      a := a + l.length + 1
  let roTop := a
  let mut gaddr : Std.HashMap Nat Nat := {}
  for (x, ty, _) in statics do
    if gaddr.contains x then continue
    match sizeOf ty with
    | .ok (size, align) =>
      a := C1.alignUp a (max align 1)
      gaddr := gaddr.insert x a
      a := a + max size 1
    | .error _ => pure ()
  let argv := C1.alignUp a 16
  return { funcs, protos, names, statics := statics.toList, tags, main := p.1.map (·.number),
           strs, gaddr, argv, roTop, top := C1.alignUp (argv + 17) 16, layout }

/-! ## Initializers -/

mutual
/-- Write the constant `c` of type `ty` at `a` (the object is already zeroed). -/
def writeConst (P : Prog) (m : Memory) (a : Nat) (ty : Ctype) : Constant → Except Stop Memory
  | .array et cs => do
    let (esize, _) ← P.sizeAlign et
    writeConsts P m a esize et cs
  | .struct _ ms => writeMembers P m a ty ms
  | .union _ x c => do
    let (off, mty) ← P.member ty x
    writeConst P m (a + off) mty c
  | .indeterminate _ | .null => .ok m
  | .integer ic => do
    let t := ofCtype ty
    storeV m t a (← ofInt t (Silmaril.Compile.Forks.Csem.C.intConstValue ic))
  | .character cc => do
    let t := ofCtype ty
    storeV m t a (← ofInt t (Silmaril.Compile.Forks.Csem.C.charValue cc))
  | .predefined pc => do
    let t := ofCtype ty
    storeV m t a (← ofInt t (if pc matches .true_ then 1 else 0))
  | .floating fc => do
    let t := ofCtype ty
    let (w, x) ← floatConst fc
    storeV m t a (← conv (.float w) t x)
def writeConsts (P : Prog) (m : Memory) (a esize : Nat) (et : Ctype) :
    List Constant → Except Stop Memory
  | [] => .ok m
  | c :: cs => do
    let m ← writeConst P m a et c
    writeConsts P m (a + esize) esize et cs
def writeMembers (P : Prog) (m : Memory) (a : Nat) (ty : Ctype) :
    List (Identifier × Constant) → Except Stop Memory
  | [] => .ok m
  | (x, c) :: cs => do
    let (off, mty) ← P.member ty x
    let m ← writeConst P m (a + off) mty c
    writeMembers P m a ty cs
end

/-! ## Evaluation -/

/-- The usual arithmetic conversions of two operand types (STD §6.3.1.8): the wider floating
type if one is floating, else C1's. -/
def usualOf (ta tb : CType) : Except Stop CType :=
  match floatCommon ta tb with
  | some u => .ok u
  | none => C1.usualOf ta tb

mutual
/-- The place an lvalue designates. -/
def evalL (P : Prog) : Nat → FunDef → TypedExpression → Env → Except Stop (Place × Env)
  | 0, _, _, _ => .error .outOfFuel
  | n + 1, fd, e, env =>
    match e.node with
    | .ident x =>
      if fd.locals.contains x.number && !fd.inMem.contains x.number then
        .ok (.reg x.number, env)
      else match env.frame[x.number]? with
        | some a => .ok (.mem a, env)
        | none => match P.gaddr[x.number]? with
          | some a => .ok (.mem a, env)
          | none => .error (.unsupported s!"object {Silmaril.Compile.Forks.Csem.C.symName x} outside the fragment")
    | .unary .indirection p => do
      let (v, env) ← evalE P n fd p env
      return (.mem v.toNat, env)
    | .memberof a m => do
      let (pl, env) ← evalL P n fd a env
      let b ← pl.addr
      let (off, _) ← P.member (lvType a) m
      return (.mem (b + off), env)
    | .memberofptr p m => do
      let (v, env) ← evalE P n fd p env
      let .ptr sty := typeOf p | .error (.unsupported "a member through a non-pointer")
      let (off, _) ← P.member sty m
      return (.mem (v.toNat + off), env)
    | .str s =>
      match P.strs[(Silmaril.Compile.Forks.Csem.C.stringBytes s).toList]? with
      | some a => .ok (.mem a, env)
      | none => .error (.unsupported "an unknown string literal")
    | .annot _ a => evalL P n fd a env
    | _ => .error (.unsupported "an lvalue outside the fragment")

/-- Evaluate an expression of a struct or union type to its bytes. -/
def evalA (P : Prog) : Nat → FunDef → TypedExpression → Env → Except Stop (Agg × Env)
  | 0, _, _, _ => .error .outOfFuel
  | n + 1, fd, e, env =>
    match e.node with
    | .rvalue a => do
      let (pl, env) ← evalL P n fd a env
      let b ← pl.addr
      let (size, _) ← P.sizeAlign (lvType a)
      return (← readAgg env.mem b size, env)
    | .assign l r => do
      let (v, env) ← evalA P n fd r env
      let (pl, env) ← evalL P n fd l env
      let b ← pl.addr
      return (v, ← env.withMem (writeAgg · b v))
    | .call f args => do
      let .functionDecay ⟨_, _, _, .ident g⟩ := f.node
        | .error (.unsupported "an indirect call")
      let pts := (P.protos[g.number]?).getD []
      let (vs, env) ← evalArgs P n fd pts args env
      let (v, env) ← callFn P n g vs env
      match v with
      | .agg v => return (v, env)
      | .scalar _ => .error (.unsupported "a scalar result of an aggregate call")
    | .cond c a b => do
      let (vc, env) ← evalE P n fd c env
      if truthOf (typeOf c) vc then
        match a with
        | some a => evalA P n fd a env
        | none => .error (.unsupported "an aggregate ?: without a middle operand")
      else evalA P n fd b env
    | .binary a .comma b => do
      let env ← evalD P n fd a env
      evalA P n fd b env
    | .annot _ a => evalA P n fd a env
    | _ => .error (.unsupported "an aggregate expression outside C3")

/-- Evaluate an expression for its effects only. -/
def evalD (P : Prog) : Nat → FunDef → TypedExpression → Env → Except Stop Env
  | 0, _, _, _ => .error .outOfFuel
  | n + 1, fd, e, env =>
    match aggOf (typeOf e) with
    | some _ => do let (_, env) ← evalA P n fd e env; return env
    | none => do let (_, env) ← evalE P n fd e env; return env

/-- Evaluate an expression to a value of its scalar type (`typeOf e`). -/
def evalE (P : Prog) : Nat → FunDef → TypedExpression → Env → Except Stop (Int × Env)
  | 0, _, _, _ => .error .outOfFuel
  | n + 1, fd, e, env =>
    let t := typeOf e
    match e.node with
    | .rvalue a => do
      let (pl, env) ← evalL P n fd a env
      return (← readPlace fd env (typeOf a) pl, env)
    | .arrayDecay a => do
      let (pl, env) ← evalL P n fd a env
      return (← pl.addr, env)
    | .const .null => .ok (0, env)
    | .const (.integer ic) => do return (← ofInt t (Silmaril.Compile.Forks.Csem.C.intConstValue ic), env)
    | .const (.floating fc) => do
      let (w, x) ← floatConst fc
      return (← conv (.float w) t x, env)
    | .const c => do return (← C0.constVal c t, env)
    | .annot _ a | .cast _ _ a => do
      let (v, env) ← evalE P n fd a env
      let ta := typeOf a
      if ta.isFloat || t.isFloat then return (← conv ta t v, env)
      return (← convTo t (← convTo ta v), env)
    | .unary op a => do
      match op with
      | .plus => let (v, env) ← evalE P n fd a env; return (← conv (typeOf a) t v, env)
      | .minus =>
        let (v, env) ← evalE P n fd a env
        match t with
        | .float w => return (F.neg w (← conv (typeOf a) t v).toNat, env)
        | _ =>
          let (w, s) ← shape t
          return (← C1.arith .sub w s 0 (← convTo t v), env)
      | .bnot =>
        let (v, env) ← evalE P n fd a env
        let (w, s) ← shape t
        return (wrap w s (-(← convTo t v) - 1), env)
      | .address =>
        let (pl, env) ← evalL P n fd a env
        return (← pl.addr, env)
      | .postfixIncr | .postfixDecr =>
        let (pl, env) ← evalL P n fd a env
        let ta := typeOf a
        let old ← readPlace fd env ta pl
        let r ← match ta with
          | .ptr _ => do
            let k ← P.pointee ta
            pure (wrap 8 false (if op == .postfixIncr then old + k else old - k))
          | .float w =>
            F.arith w (if op == .postfixIncr then .add else .sub) old.toNat
              (FloatConst.ofInt w 1)
          | _ => do
            let (w, s) := usual (← shape ta) (4, true)
            convTo ta (← C1.arith (if op == .postfixIncr then .add else .sub) w s (wrap w s old) 1)
        return (old, ← writePlace env ta r pl)
      | .indirection => .error (.unsupported "an indirection outside an lvalue")
    | .binary a op b => do
      match op with
      | .arithmetic aop =>
        let (va, env) ← evalE P n fd a env
        let (vb, env) ← evalE P n fd b env
        let ta := typeOf a
        let tb := typeOf b
        match t, ta, tb with
        | .ptr _, .ptr _, _ =>
          let k ← P.pointee ta
          return (wrap 8 false (if aop == .sub then va - vb * k else va + vb * k), env)
        | .ptr _, _, .ptr _ =>
          let k ← P.pointee tb
          return (wrap 8 false (va * k + vb), env)
        | _, .ptr _, .ptr _ =>
          let k ← P.pointee ta
          return (← convTo t ((va - vb).tdiv k), env)
        | .float w, _, _ =>
          let ca ← conv ta t va
          let cb ← conv tb t vb
          return (← F.arith w aop ca.toNat cb.toNat, env)
        | _, _, _ =>
          let (w, s) ← shape t
          let ca ← convTo t va
          let cb ← if aop == .shl || aop == .shr then pure vb else convTo t vb
          return (← C1.arith aop w s ca cb, env)
      | .comma =>
        let env ← evalD P n fd a env
        let (vb, env) ← evalE P n fd b env
        return (← conv (typeOf b) t vb, env)
      | .and | .or =>
        let (va, env) ← evalE P n fd a env
        if (op == .and) == !(truthOf (typeOf a) va) then return (if op == .and then 0 else 1, env)
        let (vb, env) ← evalE P n fd b env
        return (if truthOf (typeOf b) vb then 1 else 0, env)
      | _ =>
        let (va, env) ← evalE P n fd a env
        let (vb, env) ← evalE P n fd b env
        let ta := typeOf a
        let tb := typeOf b
        if ta matches .ptr _ || tb matches .ptr _ then
          let some r := C0.compare op (wrap 8 false va) (wrap 8 false vb)
            | .error (.unsupported "a binary operator")
          return (if r then 1 else 0, env)
        let u ← usualOf ta tb
        let ca ← conv ta u va
        let cb ← conv tb u vb
        let r := match u with
          | .float w => F.compareOp op w ca.toNat cb.toNat
          | _ => C0.compare op ca cb
        let some r := r | .error (.unsupported "a binary operator")
        return (if r then 1 else 0, env)
    | .assign l r => do
      let (v, env) ← evalE P n fd r env
      let (pl, env) ← evalL P n fd l env
      let v ← conv (typeOf r) (typeOf l) v
      return (v, ← writePlace env (typeOf l) v pl)
    | .compoundAssign l aop r => do
      let (vr, env) ← evalE P n fd r env
      let (pl, env) ← evalL P n fd l env
      let tl := typeOf l
      let tr := typeOf r
      let old ← readPlace fd env tl pl
      let res ← match tl, floatCommon tl tr with
        | .ptr _, _ => do
          let k ← P.pointee tl
          pure (wrap 8 false (if aop == .sub then old - vr * k else old + vr * k))
        | _, some u@(.float w) => do
          let x ← F.arith w aop (← conv tl u old).toNat (← conv tr u vr).toNat
          conv u tl x
        | _, _ => do
          let (w, s) ← if aop == .shl || aop == .shr then pure (promote (← shape tl))
            else pure (usual (← shape tl) (← shape tr))
          let cr := if aop == .shl || aop == .shr then vr else wrap w s vr
          convTo tl (← C1.arith aop w s (wrap w s old) cr)
      return (res, ← writePlace env tl res pl)
    | .cond c a b => do
      let (vc, env) ← evalE P n fd c env
      if truthOf (typeOf c) vc then
        match a with
        | some a => let (v, env) ← evalE P n fd a env; return (← conv (typeOf a) t v, env)
        | none => return (← conv (typeOf c) t vc, env)
      else
        let (v, env) ← evalE P n fd b env
        return (← conv (typeOf b) t v, env)
    | .call f args => do
      let .functionDecay ⟨_, _, _, .ident g⟩ := f.node
        | .error (.unsupported "an indirect call")
      let pts := (P.protos[g.number]?).getD []
      let (vs, env) ← evalArgs P n fd pts args env
      let (v, env) ← callFn P n g vs env
      match v with
      | .scalar v => return (← if t.isFloat then pure v else convTo t v, env)
      | .agg _ => .error (.unsupported "an aggregate result in a scalar position")
    | .assert a => do
      let (v, env) ← evalE P n fd a env
      if !truthOf (typeOf a) v then .error (.abort env.out) else return (0, env)
    | .sizeof _ ty => do return ((← P.sizeAlign ty).1, env)
    | .alignof _ ty => do return ((← P.sizeAlign ty).2, env)
    | .offsetof ty m => do return ((← P.member ty m).1, env)
    | .sizeofExpr a => do
      match a.annotation with
      | .lvalue _ ty _ => return ((← P.sizeAlign ty).1, env)
      | .rvalue _ =>
        match aggOf (typeOf a) with
        | some ty => return ((← P.sizeAlign ty).1, env)
        | none =>
          let some w := width (typeOf a) | .error (.unsupported "sizeof of an expression")
          return (w, env)
    | .generic _ (some i) assocs =>
      match assocs[i]? with
      | some (.type_ _ _ a) | some (.default a) => do
        let (v, env) ← evalE P n fd a env
        return (← conv (typeOf a) t v, env)
      | none => .error (.unsupported "_Generic without selection")
    | _ => .error (.unsupported "an expression outside the fragment")

/-- Evaluate arguments left to right, scalars converted to the parameter types `pts` (default
argument promotions beyond them, which C3 does not do on floating values), structs and unions
as their bytes. -/
def evalArgs (P : Prog) : Nat → FunDef → List CType → List TypedExpression → Env →
    Except Stop ((List Val) × Env)
  | 0, _, _, _, _ => .error .outOfFuel
  | _ + 1, _, _, [], env => .ok ([], env)
  | n + 1, fd, pts, a :: as, env => do
    let (v, env) ← match aggOf (typeOf a) with
      | some _ => do
        let (v, env) ← evalA P n fd a env
        pure (Val.agg v, env)
      | none => do
        let (v, env) ← evalE P n fd a env
        let v ← match pts, typeOf a with
          | pt :: _, ta => conv ta pt v
          | [], .ptr _ => pure v
          | [], .float _ => throw (.unsupported "a floating argument without a prototype")
          | [], ta => do let (w, s) := promote (← shape ta); pure (wrap w s v)
        pure (Val.scalar v, env)
    let (vs, env) ← evalArgs P n fd pts.tail as env
    return (v :: vs, env)

/-- Write the object of type `ty` at `a` from its initializer `init`. -/
def initAt (P : Prog) : Nat → FunDef → Nat → Ctype → TypedExpression → Env → Except Stop Env
  | 0, _, _, _, _, _ => .error .outOfFuel
  | n + 1, fd, a, ty, init, env =>
    match ty with
    | .mk _ (.array et _) => do
      let (size, _) ← P.sizeAlign ty
      let mut env ← env.withMem (·.writeBytes a (Array.replicate size 0))
      match init.node with
      | .array _ _ elems =>
        let (esize, _) ← P.sizeAlign et
        for (el, i) in elems.zipIdx do
          if let some x := el then
            if (i + 1) * esize > size then throw (.unsupported "an initializer too long")
            env ← initAt P n fd (a + i * esize) et x env
        return env
      | .str s =>
        let bs := (Silmaril.Compile.Forks.Csem.C.stringBytes s).toList.take size
        env.withMem (·.writeBytes a bs.toArray)
      | .const c => env.withMem (writeConst P · a ty c)
      | _ => .error (.unsupported "an array initializer outside the fragment")
    | .mk _ (.struct _) | .mk _ (.union _) => do
      let (size, _) ← P.sizeAlign ty
      match init.node with
      | .struct _ ms =>
        let mut env ← env.withMem (·.writeBytes a (Array.replicate size 0))
        for (x, el) in ms do
          if let some el := el then
            let (off, mty) ← P.member ty x
            env ← initAt P n fd (a + off) mty el env
        return env
      | .union _ x el =>
        let env ← env.withMem (·.writeBytes a (Array.replicate size 0))
        match el with
        | some el =>
          let (off, mty) ← P.member ty x
          initAt P n fd (a + off) mty el env
        | none => return env
      | .const c =>
        let env ← env.withMem (·.writeBytes a (Array.replicate size 0))
        env.withMem (writeConst P · a ty c)
      | _ =>
        let (v, env) ← evalA P n fd init env
        env.withMem (writeAgg · a v)
    | _ => do
      let t := ofCtype ty
      let (v, env) ← evalE P n fd init env
      let v ← conv (typeOf init) t v
      env.withMem (storeV · t a v)

/-- Call the function `g` on argument values (already converted to its parameter types). -/
def callFn (P : Prog) : Nat → Sym → List Val → Env → Except Stop (Val × Env)
  | 0, _, _, _ => .error .outOfFuel
  | n + 1, g, vs, env =>
    match P.funcs[g.number]? with
    | none => do
      let ints ← vs.mapM fun
        | .scalar v => pure v
        | .agg _ => throw (.unsupported "an aggregate argument of an external function")
      match F.libm (P.name g), ints with
      | some (_, f), [x] => return (.scalar (f x.toNat), env)
      | _, _ =>
        let (v, env) ← external (P.name g) ints env
        return (.scalar v, env)
    | some fd => do
      if fd.params.length != vs.length then
        .error (.unsupported s!"call of {P.name g} with {vs.length} arguments")
      let ⟨caller, callerFrame, mem, out⟩ := env
      let sp := mem.sp
      let mut mem := mem
      let mut frame : Std.HashMap Nat Nat := {}
      for (x, ty) in fd.memLocals do
        let (size, align) ← P.sizeAlign ty
        let (a, m) ← mem.alloc size align
        mem := m
        frame := frame.insert x a
      let mut regs : Std.HashMap Nat Int := {}
      for ((x, pt), v) in fd.params.zip vs do
        match v, frame[x]? with
        | .agg v, some a => mem ← writeAgg mem a v
        | .agg _, none => throw (.unsupported "an aggregate parameter outside memory")
        | .scalar v, some a => mem ← storeV mem pt a (← conv pt pt v)
        | .scalar v, none => regs := regs.insert x (← conv pt pt v)
      let (r, ⟨_, _, mem', out⟩) ← loop P n fd (some fd.body) .stop ⟨regs, frame, mem, out⟩
      let r ← match aggOf fd.ret, r with
        | some _, some (.agg v) => pure (Val.agg v)
        | some ty, _ => do
          -- a struct function that ends without `return`: an indeterminate value
          let (size, _) ← P.sizeAlign ty
          pure (Val.agg ⟨ByteArray.mk (Array.replicate size 0), ByteArray.mk (Array.replicate size 0)⟩)
        | none, some (.agg _) => throw (.unsupported "an aggregate result of a scalar function")
        | none, r => pure (Val.scalar (← conv fd.ret fd.ret ((r.map Val.int).getD 0)))
      return (r, ⟨caller, callerFrame, { mem' with sp }, out⟩)

/-- Run the statement machine of one activation to its return. -/
def loop (P : Prog) : Nat → FunDef → Option TypedStatement → Kont → Env →
    Except Stop ((Option Val) × Env)
  | 0, _, _, _, _ => .error .outOfFuel
  | n + 1, fd, focus, k, env =>
    match step P n fd focus k env with
    | .ok (.running focus k, env) => loop P n fd focus k env
    | .ok (.returned v, env) => .ok (v, env)
    | .error e => .error e

/-- One step of the statement machine. -/
def step (P : Prog) : Nat → FunDef → Option TypedStatement → Kont → Env → Except Stop (Next × Env)
  | 0, _, _, _, _ => .error .outOfFuel
  | n + 1, fd, none, k, env =>
    match k with
    | .stop => .ok (.returned none, env)
    | .seq [] k => .ok (.running none k, env)
    | .seq (s :: ss) k => .ok (.running (some s) (.seq ss k), env)
    | .while_ c b k' => do
      let (v, env) ← evalE P n fd c env
      return (if truthOf (typeOf c) v then .running (some b) k else .running none k', env)
    | .do_ b c k' => do
      let (v, env) ← evalE P n fd c env
      return (if truthOf (typeOf c) v then .running (some b) k else .running none k', env)
    | .switch k => .ok (.running none k, env)
  | n + 1, fd, some s, k, env =>
    match s.node with
    | .skip => .ok (.running none k, env)
    | .expr e => do let env ← evalD P n fd e env; return (.running none k, env)
    | .block _ ss => .ok (.running none (.seq ss k), env)
    | .declaration ds => do
      let mut env := env
      for (x, init) in ds do
        match env.frame[x.number]?, init with
        | some a, some e =>
          let ty := ((fd.memLocals.find? (·.1 == x.number)).map (·.2)).getD (.mk [] .void)
          env ← initAt P n fd a ty e env
        | some a, none =>
          let ty := ((fd.memLocals.find? (·.1 == x.number)).map (·.2)).getD (.mk [] .void)
          let (size, _) ← P.sizeAlign ty
          env ← env.withMem (fun m => .ok (m.clear a size))
        | none, some e =>
          if !fd.locals.contains x.number then continue
          let (v, env') ← evalE P n fd e env
          let v ← conv (typeOf e) ((fd.locals[x.number]?).getD (typeOf e)) v
          env := env'.setReg x.number v
        | none, none =>
          let ⟨regs, frame, mem, out⟩ := env
          env := ⟨regs.erase x.number, frame, mem, out⟩
      return (.running none k, env)
    | .if_ c a b => do
      let (v, env) ← evalE P n fd c env
      return (.running (some (if truthOf (typeOf c) v then a else b)) k, env)
    | .while_ c b _ => .ok (.running none (.while_ c b k), env)
    | .do_ b c _ => .ok (.running (some b) (.do_ b c k), env)
    | .break_ =>
      match k.breakTo with
      | some k => .ok (.running none k, env)
      | none => .error (.unsupported "break outside a loop or switch")
    | .continue_ =>
      match k.continueTo with
      | some k => .ok (.running none k, env)
      | none => .error (.unsupported "continue outside a loop")
    | .returnVoid => .ok (.returned none, env)
    | .return_ e => do
      match aggOf fd.ret with
      | some _ =>
        let (v, env) ← evalA P n fd e env
        return (.returned (some (.agg v)), env)
      | none =>
        let (v, env) ← evalE P n fd e env
        return (.returned (some (.scalar (← conv (typeOf e) fd.ret v))), env)
    | .switch e body => do
      let (v, env) ← evalE P n fd e env
      let (w, sg) := promote (← shape (typeOf e))
      let v := wrap w sg v
      match C0.findCase (C0.caseMatches w sg v) body (.switch k) with
      | some (s', k') => return (.running (some s') k', env)
      | none =>
        match C0.findCase (fun c => c.isNone) body (.switch k) with
        | some (s', k') => return (.running (some s') k', env)
        | none => return (.running none k, env)
    | .case_ _ b | .caseRangeGnu _ _ b | .default b | .label _ b _ | .marker _ b =>
      .ok (.running (some b) k, env)
    | .goto l =>
      match C0.findLabel l.number fd.body .stop with
      | some (s', k') => .ok (.running (some s') k', env)
      | none => .error (.unsupported s!"goto an unknown label {Silmaril.Compile.Forks.Csem.C.symName l}")
    | _ => .error (.unsupported "a statement outside the fragment")
end

/-! ## Whole programs -/

/-- The initial memory: string literals, objects of static storage duration (zeroed, then
written from their initializers in declaration order) and `argv`. -/
def initMemory (P : Prog) (fuel : Nat) : Except Stop Env := do
  let size := P.top - base
  let mut mem : Memory :=
    { bytes := ByteArray.mk (Array.replicate size 0), init := ByteArray.mk (Array.replicate size 1),
      roTop := base, sp := P.top }
  for (l, a) in P.strs.toList do
    mem ← mem.writeBytes a l.toArray
  mem := { mem with roTop := P.roTop }
  -- argv[0] = "" (at argv + 16), argv[1] = NULL
  mem ← mem.writeBytes P.argv (C1.Memory.le 8 (P.argv + 16))
  let mut env : Env := { mem }
  let mut done : Std.HashSet Nat := {}
  for (x, ty, init) in P.statics do
    if done.contains x then continue
    let (some a, some e) := (P.gaddr[x]?, init) | continue
    done := done.insert x
    -- objects of types outside the fragment are left zero (`check` rejects their uses)
    if !P.obj ty then continue
    env ← initAt P fuel C1.topFrame a ty e env
  return env

/-- **The C3 interpreter.** Run `main` with `fuel`. -/
def run (fuel : Nat) (p : TypedProgram) : Result :=
  let P := prepare p
  let r : Except Stop (Val × Env) := do
    let env ← initMemory P fuel
    let some ms := p.1 | .error (.unsupported "no main")
    let some fd := P.funcs[ms.number]? | .error (.unsupported "main is not defined")
    let args : List Val := match fd.params with
      | [] => []
      | [_] => [.scalar 1]
      | _ :: _ :: rest => [.scalar 1, .scalar (P.argv : Int)] ++ rest.map fun _ => .scalar 0
    callFn P (fuel + 1) ms args env
  match r with
  | .ok (v, env) => .done ⟨env.out.toList, C0.toStatus v.int⟩
  | .error (.exit c out) => .done ⟨out.toList, C0.toStatus c⟩
  | .error (.abort out) => .done ⟨out.toList, .signal 6⟩
  | .error (.undefined why) => .undefined why
  | .error .outOfFuel => .outOfFuel
  | .error (.unsupported why) => .unsupported why

/-! ## Behaviours and the language -/

/-- The behaviours of a program under C3, as for C0 (`C0.beh`). -/
def beh (p : TypedProgram) : Set Obs := {o |
  (∃ n, run n p = .done o) ∨ (∃ n why, run n p = .undefined why) ∨
    (o = ⟨[], .diverges⟩ ∧ ∀ n, run n p = .outOfFuel)}

/-- C3 as a semantics of C. -/
def sem : Semantics := beh

/-- C3 as a language of the zoo. -/
def lang : Language.{0} := cSyntax.lang sem

theorem beh_of_done {p : TypedProgram} {n : Nat} {o : Obs} (h : run n p = .done o) :
    o ∈ beh p := .inl ⟨n, h⟩

/-- Undefined behaviour allows every behaviour. -/
theorem beh_of_undefined {p : TypedProgram} {n : Nat} {why : String}
    (h : run n p = .undefined why) : beh p = Set.univ :=
  Set.eq_univ_of_forall fun _ => .inr (.inl ⟨n, why, h⟩)

/-! ## The fragment -/

/-- Is `t` the type of a scalar value of C3 (or `void`)? -/
def Prog.valueType (P : Prog) : CType → Bool
  | .int .. | .bool | .void | .float _ => true
  | .ptr t => C3.pointee P.layout depth t
  | _ => false

/-- Is `t` a struct or union type of C3? -/
def Prog.aggType (P : Prog) (t : CType) : Bool :=
  match aggOf t with
  | some ty => P.obj ty
  | none => false

/-- The member `m` of the struct or union type `ty`, for the checker. -/
def Prog.memberS (P : Prog) (ty : Ctype) (m : Identifier) : Except String (Nat × Ctype) :=
  match P.member ty m with
  | .ok r => .ok r
  | .error _ => .error s!"no member {m.name} in a struct or union of C3"

/-- Does `t` have a layout in C3 (for `sizeof` and `_Alignof`)? -/
def Prog.sized (P : Prog) (ty : Ctype) : Except String Unit :=
  match P.sizeAlign ty with
  | .ok _ => pure ()
  | .error _ => throw "sizeof of a type outside C3"

/-- Is a floating constant in C3 (not `long double`, and well formed)? -/
def checkFloat (fc : FloatingConstant) : Except String Unit :=
  match floatConst fc with
  | .ok _ => pure ()
  | .error _ => throw "a floating constant outside C3"

mutual
/-- Check that an rvalue is in the fragment. -/
def checkE (P : Prog) : TypedExpression → Except String Unit
  | .mk ann _ _ node => do
    match ann with
    | .lvalue .. => throw "an lvalue in value position"
    | .rvalue g =>
      let t := ofGenType g
      if P.aggType t then checkA P node
      else
        if !P.valueType t then throw "an expression of a type outside C3"
        checkN P node
/-- Check an expression of a struct or union type. -/
def checkA (P : Prog) : ExpressionNode GenTypeCategory → Except String Unit
  | .rvalue a => checkLv P a
  | .assign l r => do checkLv P l; checkE P r
  | .call f args => checkCall P f args
  | .cond c (some a) b => do checkE P c; checkE P a; checkE P b
  | .binary a .comma b => do checkE P a; checkE P b
  | .annot _ a => checkE P a
  | _ => throw "an aggregate expression outside C3"
def checkN (P : Prog) : ExpressionNode GenTypeCategory → Except String Unit
  | .rvalue a | .arrayDecay a => checkLv P a
  | .const c =>
    match c with
    | .integer _ | .character _ | .predefined _ | .null => pure ()
    | .floating fc => checkFloat fc
    | _ => throw "a constant outside C3"
  | .annot _ a | .cast _ _ a | .assert a => checkE P a
  | .unary op a =>
    match op with
    | .plus | .minus | .bnot => checkE P a
    | .address | .postfixIncr | .postfixDecr => checkLv P a
    | .indirection => throw "an indirection outside an lvalue"
  | .binary a _ b => do checkE P a; checkE P b
  | .assign l r | .compoundAssign l _ r => do checkLv P l; checkE P r
  | .cond c a b => do
    checkE P c
    match a with
    | some a => checkE P a
    | none => pure ()
    checkE P b
  | .call f args => checkCall P f args
  | .sizeof _ ty | .alignof _ ty => P.sized ty
  | .offsetof ty m => do let _ ← P.memberS ty m
  | .sizeofExpr _ => pure ()
  | .generic _ (some _) assocs => checkG P assocs
  | _ => throw "an expression outside the fragment"
/-- Check a direct call: of a function of the program (floating arguments only where a
prototype converts them), of an external of the fragment on scalar arguments that are not
floating, or of a function of `F.libm` declared with its prototype. -/
def checkCall (P : Prog) (f : TypedExpression) (args : List TypedExpression) :
    Except String Unit := do
  match f.node with
  | .functionDecay ⟨_, _, _, .ident g⟩ =>
    let pts := (P.protos[g.number]?).getD []
    match P.funcs[g.number]? with
    | some fd =>
      if pts.length != args.length &&
          (args.any (fun a => (typeOf a).isFloat) || fd.params.any (·.2.isFloat)) then
        throw s!"a floating argument or parameter of {P.name g} without a prototype"
    | none =>
      let name := P.name g
      if let some (w, _) := F.libm name then
        match pts, typeOf f with
        | [.float v], .ptr (.mk _ (.function (_, r) ..)) =>
          if v != w || !(match ofCtype r with | .float u => u == w | _ => false) then
            throw s!"{name} with another prototype"
        | _, _ => throw s!"{name} without its prototype"
      else
        if !(externals.contains name) then
          throw s!"call of the external function {name}"
        if args.any (fun a => (aggOf (typeOf a)).isSome) then
          throw s!"an aggregate argument of the external function {name}"
        if args.any (fun a => (typeOf a).isFloat) || pts.any (·.isFloat) then
          throw s!"a floating argument of the external function {name}"
  | _ => throw "an indirect call"
  checkL P args
/-- Check that an lvalue is in the fragment. -/
def checkLv (P : Prog) : TypedExpression → Except String Unit
  | .mk ann _ _ node => do
    match ann with
    | .lvalue _ ty _ => if !P.obj ty then throw "an object of a type outside C3"
    | .rvalue _ => throw "an rvalue in lvalue position"
    match node with
    | .ident _ => pure ()
    | .unary .indirection p => checkE P p
    | .memberof a _ => checkLv P a
    | .memberofptr p _ => do
      checkE P p
      match typeOf p with
      | .ptr sty => if !P.obj sty then throw "a member of an incomplete struct or union"
      | _ => throw "a member through a non-pointer"
    | .str s => if !plainString s then throw "a wide string literal"
    | .annot _ a => checkLv P a
    | _ => throw "an lvalue outside C3"
def checkL (P : Prog) : List TypedExpression → Except String Unit
  | [] => pure ()
  | e :: es => do checkE P e; checkL P es
def checkG (P : Prog) : List (GenericAssociation GenTypeCategory) → Except String Unit
  | [] => pure ()
  | .type_ _ _ e :: gs | .default e :: gs => do checkE P e; checkG P gs
end

mutual
/-- Check an aggregate constant. -/
def checkC : Constant → Except String Unit
  | .array _ cs => checkCs cs
  | .struct _ ms => checkCm ms
  | .union _ _ c => checkC c
  | .integer _ | .character _ | .predefined _ | .null | .indeterminate _ => pure ()
  | .floating fc => checkFloat fc
def checkCs : List Constant → Except String Unit
  | [] => pure ()
  | c :: cs => do checkC c; checkCs cs
def checkCm : List (Identifier × Constant) → Except String Unit
  | [] => pure ()
  | (_, c) :: cs => do checkC c; checkCm cs
end

/-- Check an initializer of an object of type `ty` (`n` bounds the nesting). -/
def checkI (P : Prog) : Nat → Ctype → TypedExpression → Except String Unit
  | 0, _, _ => throw "an initializer nested too deeply"
  | n + 1, ty, e@(.mk _ _ _ node) =>
    match ty with
    | .mk _ (.array et _) =>
      match node with
      | .array _ _ elems => elems.forM fun
        | some x => checkI P n et x
        | none => pure ()
      | .str s => if plainString s then pure () else throw "a wide string literal"
      | .const c => checkC c
      | _ => throw "an array initializer outside C3"
    | .mk _ (.struct _) | .mk _ (.union _) =>
      match node with
      | .struct _ ms => ms.forM fun
        | (m, some x) => do checkI P n (← P.memberS ty m).2 x
        | (_, none) => pure ()
      | .union _ m (some x) => do checkI P n (← P.memberS ty m).2 x
      | .union _ _ none => pure ()
      | .const c => checkC c
      | _ => checkE P e
    | _ => do
      if !P.valueType (ofCtype ty) then throw "an initializer of an object without values in C3"
      checkE P e

/-- The locals of a statement have types of C3. -/
def checkLocals (P : Prog) (bs : Bindings) : Except String Unit := do
  for (x, (_, _, _, ty)) in bs do
    if !P.obj ty then throw s!"local {Silmaril.Compile.Forks.Csem.C.symName x} of a type outside C3"

mutual
def checkS (P : Prog) (fd : FunDef) : TypedStatement → Except String Unit
  | .mk _ _ _ node => checkSN P fd node
def checkSN (P : Prog) (fd : FunDef) : StatementNode GenTypeCategory → Except String Unit
  | .skip | .break_ | .continue_ | .returnVoid | .goto _ => pure ()
  | .expr e | .return_ e => checkE P e
  | .block bs ss => do checkLocals P bs; checkSL P fd ss
  | .if_ c a b => do checkE P c; checkS P fd a; checkS P fd b
  | .while_ c b _ | .do_ b c _ => do checkE P c; checkS P fd b
  | .switch e b => do checkE P e; checkS P fd b
  | .case_ _ b | .caseRangeGnu _ _ b | .default b | .label _ b _ | .marker _ b => checkS P fd b
  | .declaration ds => checkD P fd ds
  | _ => throw "a statement outside the fragment"
def checkSL (P : Prog) (fd : FunDef) : List TypedStatement → Except String Unit
  | [] => pure ()
  | s :: ss => do checkS P fd s; checkSL P fd ss
def checkD (P : Prog) (fd : FunDef) : List (Sym × Option TypedExpression) → Except String Unit
  | [] => pure ()
  | (x, some e) :: ds => do
    match fd.memLocals.find? (·.1 == x.number) with
    | some (_, ty) => checkI P depth ty e
    | none => checkE P e
    checkD P fd ds
  | (_, none) :: ds => checkD P fd ds
end

/-- Is the program in the C3 fragment? The reason when it is not. Only the functions reachable
from `main` are checked, and the initializers of the objects of static storage duration whose
type is in C3 (the others are left zero, and their uses are rejected where they occur). -/
def check (p : TypedProgram) : Except String Unit := do
  let P := prepare p
  let some m := P.main | throw "no main"
  let some _ := P.funcs[m]? | throw "main is not defined"
  let live := C2.reachable P.toC2
    (m :: (P.statics.flatMap fun (_, _, i) => (i.map C2.callsE).getD []))
  for (x, (_, _, d)) in p.2.declarations do
    match d with
    | .function _ (_, ret) ps variadic _ _ =>
      if live.contains x.number then
        if variadic then throw s!"a variadic function {Silmaril.Compile.Forks.Csem.C.symName x}"
        let r := ofCtype ret
        if !P.valueType r && !P.aggType r then
          throw s!"a function with a result outside C3: {Silmaril.Compile.Forks.Csem.C.symName x}"
        if ps.any fun (_, t, _) =>
            !P.obj t || !((width (ofCtype t)).isSome || P.aggType (ofCtype t)) then
          throw s!"a function with a parameter outside C3: {Silmaril.Compile.Forks.Csem.C.symName x}"
    | .object .. => pure ()
  for (_, ty, init) in P.statics do
    if P.obj ty then
      if let some e := init then checkI P depth ty e
  for f in live do
    if let some fd := P.funcs[f]? then checkS P fd fd.body

/-- The C3 fragment. -/
def InFragment (p : TypedProgram) : Prop := check p = .ok ()

instance (p : TypedProgram) : Decidable (InFragment p) :=
  inferInstanceAs (Decidable (check p = .ok ()))

/-- The fragment as a set of programs. -/
def fragment : Set TypedProgram := {p | InFragment p}

end Silmaril.Compile.C.Sem.C3
