module

public import Silmaril.Compiler.C.Sem.C0.Defs
@[expose] public section

/-!
# C1: flat byte memory, on typed Ail

The second rung of the C semantics ladder. C1 extends C0 (`C0.lean`) with a
memory: a flat array of bytes addressed by integers, with Cerberus's LP64 layout
(`Silmaril.Compile.C.sizeAlign`, from `Cerberus/Mem/Layout.lean`). The **C1 fragment**
(`C1.InFragment`, decided by `C1.check`) adds to C0's:

* objects in memory: arrays (of any dimension) and address-taken scalars, automatic or of
  static storage duration, with their initializers (lists, string literals, aggregate
  constants);
* pointers to objects (`&`, `*`, array decay and subscripts, pointer arithmetic and
  differences, comparisons, casts between pointers and integers), as unsigned 64-bit
  integers (`void *` arithmetic is GNU's: size 1);
* string literals, read-only;
* `main(int argc, char **argv)` with `argc = 1`, `argv[0] = ""` and `argv[1] = NULL`;
* externals as specified functions over the memory: `putchar`, `puts`, `printf` (flags,
  width, precision and length modifiers of `%d %i %u %o %x %X %c %s %%`), `strlen`,
  `strcmp`, `strncmp`, `strcpy`, `strncpy`, `strcat`, `strchr`, `strrchr`, `memcpy`, `memmove`,
  `memset`, `memcmp`, `abs`, `labs`, `llabs`, `sprintf`, `snprintf`, and C0's `abort`,
  `exit`, `_Exit` (gcc's `__builtin_f` is `f`).

Still outside: structs and unions (C2), function pointers (C3), `malloc` (C4), floats (C5),
variadic definitions (C6).

## Memory

Addresses below `base` are invalid (`NULL` is 0). From `base` up lie the string literals
(read-only), the objects of static storage duration (zero-initialised, then initialised in
declaration order), `argv`, and the stack: each activation allocates its memory locals
(arrays and address-taken objects, parameters included) on entry and frees them on return.
Scalar locals whose address is never taken stay in registers, exactly as in C0.

A byte is initialised or not. Undefined behaviour reported, besides C0's: an access outside
`[base, top of the stack)` (null and dangling stack pointers, overruns past the last object),
a write to a string literal, a read of uninitialised memory, `printf` with too few arguments.
An overrun from one object into an adjacent one is not detected: pointers carry no
provenance, so C1 is *more defined* than C there.

## Choices

As in C0 (left-to-right evaluation, implementation-defined conversions modulo `2ᴺ`), plus:
an assignment evaluates its right operand before its left one (as gcc does; C leaves the
order unspecified); string literals with the same bytes share their storage (unspecified in
C, STD §6.4.5#7); `strcmp`, `strncmp` and `memcmp` return the difference of the first
differing bytes (glibc's choice); `puts` returns the number of bytes written; a read of an
uninitialised object is undefined (C11 §6.3.2.1#2 for register-like objects; for objects in
memory C leaves the value unspecified, so here C1 claims less than C, never something
different).

## Statement: C1 extends C0 on C0's fragment

The intended theorem of the rung is

  `C0.sem ⊑[C0.fragment] C1.sem`, i.e. `∀ p, C0.InFragment p → C0.beh p ⊆ C1.beh p`

(`Syntax.RefinesOn`): on a C0 program, C1 keeps C0's register locals and puts only the
objects of static storage duration in memory, zero-initialised as C0's globals are, so both
interpreters compute the same results step by step. Every C0 program is in C1's fragment
(`C1.check` accepts all that `C0.check` does). Like C0's refinement of the full semantics, it
is tested (the `csem` campaign runs `csem run`, which dispatches to C1, against gcc -O0 on the
corpus), not yet proved.
-/

namespace Silmaril.Compile.C.Sem.C1

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Compile.C
open Silmaril.Compile.Category
open C0 (Stop ub Kont Next Result)

/-! ## Integers

C0's integer operations (`C0.wrap`, `C0.inRange`, `arith`) with the bounds of the usual
widths as literals and a fast path for values already in range: `2 ^ (8 * w)` and the
reduction modulo it are big-integer operations, which dominated the run time. They are the
same functions. -/

/-- The lower bound of the integer type of `w` bytes and signedness `s`. -/
@[inline] def lo : Nat → Bool → Int
  | 1, true => -0x80
  | 2, true => -0x8000
  | 4, true => -0x80000000
  | 8, true => -0x8000000000000000
  | w, true => -(2 ^ (8 * w - 1))
  | _, false => 0

/-- The upper bound (exclusive) of the integer type of `w` bytes and signedness `s`. -/
@[inline] def hi : Nat → Bool → Int
  | 1, true => 0x80
  | 2, true => 0x8000
  | 4, true => 0x80000000
  | 8, true => 0x8000000000000000
  | 1, false => 0x100
  | 2, false => 0x10000
  | 4, false => 0x100000000
  | 8, false => 0x10000000000000000
  | w, true => 2 ^ (8 * w - 1)
  | w, false => 2 ^ (8 * w)

/-- `v` is a value of the integer type `(w, s)` (`C0.inRange`). -/
@[inline] def inRange (w : Nat) (s : Bool) (v : Int) : Bool := lo w s ≤ v && v < hi w s

/-- Reduce `v` into the integer type `(w, s)` (`C0.wrap`). -/
@[inline] def wrap (w : Nat) (s : Bool) (v : Int) : Int :=
  if inRange w s v then v else C0.wrap w s v

theorem lo_eq (w : Nat) (s : Bool) : lo w s = if s then -(2 ^ (8 * w - 1)) else 0 := by
  unfold lo; split <;> simp_all

theorem hi_eq (w : Nat) (s : Bool) : hi w s = if s then 2 ^ (8 * w - 1) else 2 ^ (8 * w) := by
  unfold hi; split <;> simp_all

theorem inRange_eq (w : Nat) (s : Bool) (v : Int) : inRange w s v = C0.inRange w s v := by
  cases s <;> simp [inRange, C0.inRange, lo_eq, hi_eq]

/-- `C0.wrap` fixes the values of the type. -/
theorem C0_wrap_self {w : Nat} {s : Bool} {v : Int} (hw : 0 < w)
    (h : C0.inRange w s v = true) : C0.wrap w s v = v := by
  have hm : (2 : Int) ^ (8 * w) = 2 * 2 ^ (8 * w - 1) := by
    rw [show 8 * w = (8 * w - 1) + 1 by omega, Int.pow_succ]; simp only [Nat.add_sub_cancel]
    exact Int.mul_comm _ _
  have hp : (0 : Int) < 2 ^ (8 * w - 1) := Int.pow_pos (by decide)
  cases s
  · simp only [C0.inRange, C0.wrap, Bool.false_eq_true, ite_false, decide_eq_true_eq,
      Bool.false_and] at h ⊢
    exact Int.emod_eq_of_lt h.1 h.2
  · simp only [C0.inRange, C0.wrap, ite_true, decide_eq_true_eq, Bool.true_and] at h ⊢
    obtain ⟨h1, h2⟩ := h
    rw [hm, Int.mul_ediv_cancel_left _ (by decide : (2 : Int) ≠ 0)]
    by_cases hv : 0 ≤ v
    · rw [Int.emod_eq_of_lt hv (by omega)]
      split <;> omega
    · have : v % (2 * 2 ^ (8 * w - 1)) = v + 2 * 2 ^ (8 * w - 1) := by
        rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
      rw [this]
      split <;> omega

/-- The fast `wrap` is C0's, on every width of a C type. -/
theorem wrap_eq (w : Nat) (s : Bool) (v : Int) (hw : 0 < w) : wrap w s v = C0.wrap w s v := by
  unfold wrap
  split
  · rename_i h; rw [inRange_eq] at h; exact (C0_wrap_self hw h).symm
  · rfl

/-- Bitwise operators, on the two's-complement representation (`C0.bitwise`). -/
def bitwise (f : Nat → Nat → Nat) (w : Nat) (s : Bool) (a b : Int) : Int :=
  wrap w s (f (wrap w false a).toNat (wrap w false b).toNat)

/-- `a aop b` in the integer type `(w, s)` (`arith`). -/
def arith (aop : ArithmeticOperator) (w : Nat) (s : Bool) (a b : Int) : Except Stop Int :=
  let chk (r : Int) : Except Stop Int :=
    if s then (if inRange w s r then .ok r else ub "signed integer overflow")
    else .ok (wrap w false r)
  let count : Except Stop Nat :=
    if 0 ≤ b ∧ b < 8 * w then .ok b.toNat else ub "shift count out of range"
  match aop with
  | .add => chk (a + b)
  | .sub => chk (a - b)
  | .mul => chk (a * b)
  | .div => if b = 0 then ub "division by zero" else chk (a.tdiv b)
  | .mod =>
    if b = 0 then ub "division by zero"
    else do let _ ← chk (a.tdiv b); .ok (a.tmod b)
  | .band => .ok (bitwise (· &&& ·) w s a b)
  | .bor => .ok (bitwise (· ||| ·) w s a b)
  | .bxor => .ok (bitwise (· ^^^ ·) w s a b)
  | .shl => do
    let k ← count
    if s && a < 0 then ub "left shift of a negative value" else chk (a * 2 ^ k)
  | .shr => do
    let k ← count
    .ok (a / 2 ^ k)

/-! ## Memory -/

/-- The lowest valid address. -/
def base : Nat := 4096

/-- The most bytes of memory a run may use. -/
def maxBytes : Nat := 1 <<< 28

def alignUp (n a : Nat) : Nat := if a ≤ 1 then n else (n + a - 1) / a * a

/-- The memory: the bytes at `base + i`, whether each is initialised, the end of the
read-only string literals and the top of the stack (the first free address). -/
structure Memory where
  bytes : ByteArray := .empty
  init : ByteArray := .empty
  roTop : Nat := base
  sp : Nat := base

namespace Memory

/-- `[a, a + n)` lies in allocated memory. -/
def valid (m : Memory) (a n : Nat) : Bool := base ≤ a && a + n ≤ m.sp

/-- Allocate `size` bytes aligned to `align` on top of the stack, uninitialised. -/
def alloc (m : Memory) (size align : Nat) : Except Stop (Nat × Memory) := do
  let a := alignUp m.sp align
  let top := a + max size 1
  if top - base > maxBytes then throw (.unsupported "a run using more than 256 MiB")
  let need := top - base
  let grow (b : ByteArray) : ByteArray :=
    if b.size ≥ need then b
    else b ++ ByteArray.mk (Array.replicate (max need (2 * b.size) - b.size) 0)
  let ⟨bytes, init, roTop, _⟩ := m
  let mut init := grow init
  for i in [a - base:top - base] do
    init := init.set! i 0
  return (a, ⟨grow bytes, init, roTop, top⟩)

/-- Mark `[a, a + n)` uninitialised (a declaration without initializer reached again). -/
def clear (m : Memory) (a n : Nat) : Memory := Id.run do
  let ⟨bytes, init, roTop, sp⟩ := m
  let mut init := init
  for i in [a - base:a - base + n] do
    init := init.set! i 0
  return ⟨bytes, init, roTop, sp⟩

/-- Read `n` bytes. -/
def readBytes (m : Memory) (a n : Nat) : Except Stop (Array UInt8) := do
  if !m.valid a n then ub "an access out of bounds"
  let mut out : Array UInt8 := Array.mkEmpty n
  for i in [a - base:a - base + n] do
    if m.init[i]! == 0 then ub "a read of uninitialised memory"
    out := out.push m.bytes[i]!
  return out

/-- Write bytes at `a`. -/
def writeBytes (m : Memory) (a : Nat) (bs : Array UInt8) : Except Stop Memory := do
  if !m.valid a bs.size then ub "an access out of bounds"
  if a < m.roTop then ub "a write to a string literal"
  let ⟨bytes, init, roTop, sp⟩ := m
  let mut bytes := bytes
  let mut init := init
  for h : i in [0:bs.size] do
    bytes := bytes.set! (a - base + i) bs[i]
    init := init.set! (a - base + i) 1
  return ⟨bytes, init, roTop, sp⟩

/-- Copy `n` bytes from `s` to `d`, initialisation included (overlap allowed). -/
def copy (m : Memory) (d s n : Nat) : Except Stop Memory := do
  if !m.valid s n || !m.valid d n then ub "an access out of bounds"
  if d < m.roTop then ub "a write to a string literal"
  let src := (m.bytes.extract (s - base) (s - base + n), m.init.extract (s - base) (s - base + n))
  let ⟨bytes, init, roTop, sp⟩ := m
  let mut bytes := bytes
  let mut init := init
  for i in [0:n] do
    bytes := bytes.set! (d - base + i) src.1[i]!
    init := init.set! (d - base + i) src.2[i]!
  return ⟨bytes, init, roTop, sp⟩

/-- Little-endian bytes of `v` in `w` bytes. -/
def le (w : Nat) (v : Int) : Array UInt8 := Id.run do
  let mut n := (wrap w false v).toNat
  let mut out : Array UInt8 := Array.mkEmpty w
  for _ in [0:w] do
    out := out.push (n % 256).toUInt8
    n := n / 256
  return out

/-- The unsigned value of little-endian bytes. -/
def ofLE (bs : Array UInt8) : Nat := bs.foldr (fun b acc => acc * 256 + b.toNat) 0

/-- The NUL-terminated string at `a`, without its NUL; at most `limit` bytes. -/
def cstr (m : Memory) (a : Nat) (limit : Nat := maxBytes) : Except Stop (Array UInt8) := do
  let mut out : Array UInt8 := #[]
  for i in [0:limit] do
    let b := (← m.readBytes (a + i) 1)[0]!
    if b == 0 then return out
    out := out.push b
  return out

end Memory

/-! ## Values -/

mutual
/-- Is `t` the type of an object of C1: an integer, a pointer to an object type of C1 or to
`void`, or an array of known size of objects of C1? -/
def objType : Ctype → Bool
  | .mk _ node => objNode node
def objNode : CtypeNode → Bool
  | .basic (.integer _) => true
  | .pointer _ t => pointee t
  | .array t (some _) => objType t
  | _ => false
/-- Can `t` be pointed to? -/
def pointee : Ctype → Bool
  | .mk _ .void => true
  | .mk _ node => objNode node
end


/-- The width in bytes of a scalar type of C1 (integers, `_Bool`, pointers). -/
def width : CType → Option Nat
  | .int w _ => some w
  | .bool => some 1
  | .ptr _ => some 8
  | _ => none

/-- Convert a value to a scalar type (`void`: discard). Pointers are unsigned 64-bit. -/
def convTo : CType → Int → Except Stop Int
  | .bool, v => .ok (if v = 0 then 0 else 1)
  | .int w s, v => .ok (wrap w s v)
  | .ptr _, v => .ok (wrap 8 false v)
  | .void, _ => .ok 0
  | _, _ => .error (.unsupported "a conversion to a type outside C1")

/-- The integer shape of an integer type. -/
def shape : CType → Except Stop (Nat × Bool)
  | .int w s => .ok (w, s)
  | .bool => .ok (1, false)
  | _ => .error (.unsupported "a non-integer operand")

/-- Load a scalar of type `t` at `a`. -/
def load (m : Memory) (t : CType) (a : Nat) : Except Stop Int := do
  let some w := width t | throw (.unsupported "a load of a type outside C1")
  let v := Memory.ofLE (← m.readBytes a w)
  match t with
  | .int w s => return wrap w s v
  | .bool => return (if v = 0 then 0 else 1)
  | _ => return v

/-- Store a scalar of type `t` (already converted) at `a`. -/
def store (m : Memory) (t : CType) (a : Nat) (v : Int) : Except Stop Memory := do
  let some w := width t | throw (.unsupported "a store of a type outside C1")
  m.writeBytes a (Memory.le w v)

/-! ## Programs -/

/-- A function definition, prepared. -/
structure FunDef extends C0.FunDef where
  /-- The locals kept in memory (arrays and address-taken objects, parameters included), in
  allocation order, with their types. -/
  memLocals : List (Nat × Ctype)
  inMem : Std.HashSet Nat

/-- A prepared program, with the layout of its static memory. -/
structure Prog where
  funcs : Std.HashMap Nat FunDef
  /-- Parameter types of every declared function (for argument conversion). -/
  protos : Std.HashMap Nat (List CType)
  /-- The source name of every declared function (externals are found by name). -/
  names : Std.HashMap Nat String
  /-- Objects of static storage duration: symbol number, type, initializer. -/
  statics : List (Nat × Ctype × Option TypedExpression)
  tags : Mem.Concrete.Tags
  main : Option Nat
  /-- String literals (their bytes, without NUL) and their addresses. -/
  strs : Std.HashMap (List UInt8) Nat
  /-- Addresses of the objects of static storage duration. -/
  gaddr : Std.HashMap Nat Nat
  /-- `argv`: two pointers (`argv[0]`, the empty string at `argv + 16`, and `NULL`). -/
  argv : Nat
  roTop : Nat
  /-- The end of static memory, where the stack starts. -/
  top : Nat

mutual
/-- Automatic locals declared in a statement, with their C types. -/
def localsS : TypedStatement → List (Nat × Ctype)
  | .mk _ _ _ node => localsN node
def localsN : StatementNode GenTypeCategory → List (Nat × Ctype)
  | .block bs ss =>
    (bs.filterMap fun (x, ((_, dur, _), _, _, ty)) =>
      if dur == .automatic then some (x.number, ty) else none) ++ localsL ss
  | .if_ _ a b => localsS a ++ localsS b
  | .while_ _ b _ | .do_ b _ _ | .switch _ b | .case_ _ b | .caseRangeGnu _ _ b | .default b
  | .label _ b _ | .marker _ b => localsS b
  | .par ss => localsL ss
  | _ => []
def localsL : List TypedStatement → List (Nat × Ctype)
  | [] => []
  | s :: ss => localsS s ++ localsL ss
end

mutual
/-- The string literals (bytes) and address-taken symbols of an expression. -/
def scanE : TypedExpression → List (List UInt8) × List Nat
  | .mk _ _ _ node => scanN node
def scanN : ExpressionNode GenTypeCategory → List (List UInt8) × List Nat
  | .str s => ([(Silmaril.Compile.Forks.Csem.C.stringBytes s).toList], [])
  | .unary .address a =>
    let (l, t) := scanE a
    match a.node with
    | .ident x => (l, x.number :: t)
    | _ => (l, t)
  | .unary _ a | .annot _ a | .cast _ _ a | .assert a | .rvalue a | .arrayDecay a
  | .functionDecay a | .memberof a _ | .memberofptr a _ | .compound _ _ a => scanE a
  | .binary a _ b | .assign a b | .compoundAssign a _ b =>
    let (l1, t1) := scanE a
    let (l2, t2) := scanE b
    (l1 ++ l2, t1 ++ t2)
  | .cond c a b =>
    let (l1, t1) := scanE c
    let (l2, t2) := match a with
      | some a => scanE a
      | none => ([], [])
    let (l3, t3) := scanE b
    (l1 ++ l2 ++ l3, t1 ++ t2 ++ t3)
  | .call f args =>
    let (l1, t1) := scanE f
    let (l2, t2) := scanL args
    (l1 ++ l2, t1 ++ t2)
  | .array _ _ es => scanO es
  | .generic _ _ gs => scanG gs
  | _ => ([], [])
def scanL : List TypedExpression → List (List UInt8) × List Nat
  | [] => ([], [])
  | e :: es =>
    let (l1, t1) := scanE e
    let (l2, t2) := scanL es
    (l1 ++ l2, t1 ++ t2)
def scanO : List (Option TypedExpression) → List (List UInt8) × List Nat
  | [] => ([], [])
  | none :: es => scanO es
  | some e :: es =>
    let (l1, t1) := scanE e
    let (l2, t2) := scanO es
    (l1 ++ l2, t1 ++ t2)
def scanG : List (GenericAssociation GenTypeCategory) → List (List UInt8) × List Nat
  | [] => ([], [])
  | .type_ _ _ e :: gs | .default e :: gs =>
    let (l1, t1) := scanE e
    let (l2, t2) := scanG gs
    (l1 ++ l2, t1 ++ t2)
end

mutual
/-- The string literals and address-taken symbols of a statement. -/
def scanS : TypedStatement → List (List UInt8) × List Nat
  | .mk _ _ _ node => scanSN node
def scanSN : StatementNode GenTypeCategory → List (List UInt8) × List Nat
  | .expr e | .return_ e => scanE e
  | .block _ ss | .par ss => scanSL ss
  | .if_ c a b =>
    let (l1, t1) := scanE c
    let (l2, t2) := scanS a
    let (l3, t3) := scanS b
    (l1 ++ l2 ++ l3, t1 ++ t2 ++ t3)
  | .while_ c b _ | .do_ b c _ | .switch c b =>
    let (l1, t1) := scanE c
    let (l2, t2) := scanS b
    (l1 ++ l2, t1 ++ t2)
  | .case_ _ b | .caseRangeGnu _ _ b | .default b | .label _ b _ | .marker _ b => scanS b
  | .declaration ds => scanD ds
  | _ => ([], [])
def scanSL : List TypedStatement → List (List UInt8) × List Nat
  | [] => ([], [])
  | s :: ss =>
    let (l1, t1) := scanS s
    let (l2, t2) := scanSL ss
    (l1 ++ l2, t1 ++ t2)
def scanD : List (Sym × Option TypedExpression) → List (List UInt8) × List Nat
  | [] => ([], [])
  | (_, some e) :: ds =>
    let (l1, t1) := scanE e
    let (l2, t2) := scanD ds
    (l1 ++ l2, t1 ++ t2)
  | (_, none) :: ds => scanD ds
end

/-- Prepare a typed-Ail program and lay out its static memory. -/
def prepare (p : TypedProgram) : Prog := Id.run do
  let σ := p.2
  let tags := tagsOf σ
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
    lits := lits ++ (scanE e).1
  let mut funcs : Std.HashMap Nat FunDef := {}
  for (x, fd) in σ.functionDefinitions do
    let pts := (protos[x.number]?).getD []
    let pcs := (pctys[x.number]?).getD []
    let params := fd.params.zipIdx.map fun (y, i) => (y.number, (pts[i]?).getD (.int 4 true))
    let blockLocals := localsS fd.body
    let locals := blockLocals.foldl (fun m (n, t) => m.insert n (ofCtype t))
      (params.foldl (fun m (n, t) => m.insert n t) {})
    let (ls, taken) := scanS fd.body
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
    match sizeAlign tags ty with
    | .ok (size, align) =>
      a := alignUp a (max align 1)
      gaddr := gaddr.insert x a
      a := a + max size 1
    | .error _ => pure ()
  let argv := alignUp a 16
  return { funcs, protos, names, statics := statics.toList, tags, main := p.1.map (·.number),
           strs, gaddr, argv, roTop, top := alignUp (argv + 17) 16 }

/-- The source name of a function; gcc's `__builtin_f` is the external `f`. -/
def Prog.name (P : Prog) (x : Sym) : String :=
  let n := (P.names[x.number]?).getD (Silmaril.Compile.Forks.Csem.C.symName x)
  if n.startsWith "__builtin_" then (n.drop 10).toString else n

/-- Size and alignment of a type (integers and pointers directly: LP64, aligned to their
size, as `typeLayout` lays them out). -/
def Prog.sizeAlign (P : Prog) (ty : Ctype) : Except Stop (Nat × Nat) :=
  match ty with
  | .mk _ (.basic (.integer it)) => let (w, _) := intLayout it; .ok (w, w)
  | .mk _ (.pointer ..) => .ok (8, 8)
  | _ => (C.sizeAlign P.tags ty).mapError Stop.unsupported

/-- The size of the pointee of a pointer type, for pointer arithmetic (`void`: 1). -/
def Prog.pointee (P : Prog) : CType → Except Stop Nat
  | .ptr ty => do return max 1 (← P.sizeAlign ty).1
  | _ => throw (.unsupported "pointer arithmetic on a non-pointer")

/-! ## States -/

/-- The store: register locals and memory locals of the current activation, the memory and
the output so far. -/
structure Env where
  regs : Std.HashMap Nat Int := {}
  frame : Std.HashMap Nat Nat := {}
  mem : Memory := {}
  out : ByteArray := .empty

/-! The store is taken apart before an update, so that its maps and arrays are updated in
place rather than copied (a field updated while the store is alive is shared). -/

/-- Update the memory. -/
@[inline] def Env.withMem (env : Env) (f : Memory → Except Stop Memory) : Except Stop Env :=
  let ⟨regs, frame, mem, out⟩ := env
  match f mem with
  | .ok mem => .ok ⟨regs, frame, mem, out⟩
  | .error e => .error e

/-- Set a register local. -/
@[inline] def Env.setReg (env : Env) (x : Nat) (v : Int) : Env :=
  let ⟨regs, frame, mem, out⟩ := env
  ⟨regs.insert x v, frame, mem, out⟩

/-- Append to the output. -/
@[inline] def Env.emit (env : Env) (bs : Array UInt8) : Env :=
  let ⟨regs, frame, mem, out⟩ := env
  ⟨regs, frame, mem, bs.foldl (·.push ·) out⟩

/-- Where an lvalue lives: a register local, or an address. -/
inductive Place where
  | reg (x : Nat)
  | mem (a : Nat)

def Place.addr : Place → Except Stop Nat
  | .mem a => .ok a
  | .reg _ => .error (.unsupported "the address of a register local")

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
  | .mem a => env.withMem (store · t a v)

/-! ## Externals -/

/-- Characters as bytes. -/
def bytesOf (s : String) : List UInt8 := s.toUTF8.toList

/-- A conversion of `printf`. -/
structure Spec where
  minus : Bool := false
  plus : Bool := false
  space : Bool := false
  alt : Bool := false
  zero : Bool := false
  width : Nat := 0
  prec : Option Nat := none
  /-- The width in bytes of the argument's type (`hh` 1, `h` 2, none 4, `l`/`ll`/`z`/`j`/`t` 8). -/
  len : Nat := 4

/-- Pad `body` (after its `pre`fix: sign, `0x`) to the width of the spec. -/
def Spec.pad (sp : Spec) (pre body : List UInt8) (zeroOk : Bool) : List UInt8 :=
  let n := pre.length + body.length
  let fill := sp.width - n
  if sp.minus then pre ++ body ++ List.replicate fill 32
  else if sp.zero && zeroOk then pre ++ List.replicate fill 48 ++ body
  else List.replicate fill 32 ++ pre ++ body

/-- An integer conversion (`d i u o x X`) of the argument `v`. -/
def Spec.int (sp : Spec) (c : Char) (v : Int) : List UInt8 :=
  let signed := c == 'd' || c == 'i'
  let v := wrap sp.len signed v
  let radix := if c == 'o' then 8 else if c == 'x' || c == 'X' then 16 else 10
  let mag := v.natAbs
  let ds : List UInt8 := if sp.prec == some 0 && mag == 0 then []
    else (Nat.toDigits radix mag).map fun d => (if c == 'X' then d.toUpper else d).toNat.toUInt8
  let ds := match sp.prec with
    | some p => List.replicate (p - ds.length) 48 ++ ds
    | none => ds
  let ds := if sp.alt && c == 'o' && ds.head? != some 48 then 48 :: ds else ds
  let pre := if !signed then [] else if v < 0 then [45] else if sp.plus then [43]
    else if sp.space then [32] else []
  let pre := if sp.alt && radix == 16 && mag != 0 then pre ++ [48, (if c == 'X' then 88 else 120)]
    else pre
  sp.pad pre ds sp.prec.isNone

/-- `printf`'s output for the format `fmt` and the (promoted) arguments `args`. -/
def format (m : Memory) (fmt : List UInt8) (args : List Int) : Except Stop (Array UInt8) := do
  let mut out : Array UInt8 := #[]
  let mut fmt := fmt
  let mut args := args
  let next (args : List Int) : Except Stop (Int × List Int) := match args with
    | a :: as => .ok (a, as)
    | [] => ub "printf with too few arguments"
  for _ in [0:fmt.length + 1] do
    match fmt with
    | [] => return out
    | c :: rest =>
      if c != 37 then out := out.push c; fmt := rest; continue
      let mut sp : Spec := {}
      let mut r := rest
      -- flags
      for _ in [0:r.length] do
        match r with
        | 45 :: r' => sp := { sp with minus := true }; r := r'
        | 43 :: r' => sp := { sp with plus := true }; r := r'
        | 32 :: r' => sp := { sp with space := true }; r := r'
        | 35 :: r' => sp := { sp with alt := true }; r := r'
        | 48 :: r' => sp := { sp with zero := true }; r := r'
        | _ => break
      -- width
      if r.head? == some 42 then
        let (w, as) ← next args
        args := as
        r := r.tail
        let w := wrap 4 true w
        if w < 0 then sp := { sp with minus := true, width := w.natAbs }
        else sp := { sp with width := w.toNat }
      else
        let ds := r.takeWhile fun b => 48 ≤ b && b ≤ 57
        sp := { sp with width := ds.foldl (fun a d => a * 10 + (d.toNat - 48)) 0 }
        r := r.drop ds.length
      -- precision
      if r.head? == some 46 then
        r := r.tail
        if r.head? == some 42 then
          let (p, as) ← next args
          args := as
          r := r.tail
          let p := wrap 4 true p
          sp := { sp with prec := if p < 0 then none else some p.toNat }
        else
          let ds := r.takeWhile fun b => 48 ≤ b && b ≤ 57
          sp := { sp with prec := some (ds.foldl (fun a d => a * 10 + (d.toNat - 48)) 0) }
          r := r.drop ds.length
      -- length
      match r with
      | 104 :: 104 :: r' => sp := { sp with len := 1 }; r := r'
      | 104 :: r' => sp := { sp with len := 2 }; r := r'
      | 108 :: 108 :: r' | 108 :: r' | 122 :: r' | 106 :: r' | 116 :: r' | 113 :: r' =>
        sp := { sp with len := 8 }; r := r'
      | _ => pure ()
      match r with
      | [] => throw (.unsupported "an incomplete printf conversion")
      | k :: r' =>
        fmt := r'
        let k := Char.ofNat k.toNat
        match k with
        | '%' => out := out.push 37
        | 'd' | 'i' | 'u' | 'o' | 'x' | 'X' =>
          let (v, as) ← next args
          args := as
          out := out ++ (sp.int k v).toArray
        | 'c' =>
          let (v, as) ← next args
          args := as
          out := out ++ (sp.pad [] [(wrap 1 false v).toNat.toUInt8] false).toArray
        | 's' =>
          if sp.len != 4 then throw (.unsupported "printf of a wide string")
          let (v, as) ← next args
          args := as
          let s ← match sp.prec with
            | some p => m.cstr v.toNat p
            | none => m.cstr v.toNat
          out := out ++ (sp.pad [] s.toList false).toArray
        | k => throw (.unsupported s!"the printf conversion %{k}")
  return out

/-- Compare `n` bytes (or up to a NUL, with `nul`): the difference of the first differing
bytes. -/
def compareBytes (m : Memory) (a b n : Nat) (nul : Bool) : Except Stop Int := do
  for i in [0:n] do
    let x := (← m.readBytes (a + i) 1)[0]!
    let y := (← m.readBytes (b + i) 1)[0]!
    if x != y then return (x.toNat : Int) - y.toNat
    if nul && x == 0 then return 0
  return 0

/-- The external functions of the fragment, by name. -/
def externals : List String :=
  ["abort", "exit", "_Exit", "putchar", "puts", "printf", "sprintf", "snprintf", "strlen",
   "strcmp", "strncmp", "strcpy", "strncpy", "strcat", "strchr", "strrchr", "memcpy",
   "memmove", "memset", "memcmp", "abs", "labs", "llabs"]

/-- Externals of the fragment, by name, on argument values. -/
def external (name : String) (args : List Int) (env : Env) : Except Stop (Int × Env) := do
  let m := env.mem
  let nat (v : Int) : Nat := v.toNat
  match name, args with
  | "abort", [] => throw (.abort env.out)
  | "exit", [c] | "_Exit", [c] => throw (.exit c env.out)
  | "putchar", [c] =>
    let b := wrap 1 false c
    return (b, env.emit #[b.toNat.toUInt8])
  | "puts", [s] =>
    let bs ← m.cstr (nat s)
    return (bs.size + 1, env.emit (bs.push 10))
  | "printf", f :: as =>
    let bs ← format m (← m.cstr (nat f)).toList as
    return (bs.size, env.emit bs)
  | "sprintf", d :: f :: as =>
    let bs ← format m (← m.cstr (nat f)).toList as
    return (bs.size, ← env.withMem (·.writeBytes (nat d) (bs.push 0)))
  | "snprintf", d :: k :: f :: as =>
    let bs ← format m (← m.cstr (nat f)).toList as
    if nat k = 0 then return (bs.size, env)
    return (bs.size, ← env.withMem (·.writeBytes (nat d) ((bs.extract 0 (nat k - 1)).push 0)))
  | "strlen", [s] => return ((← m.cstr (nat s)).size, env)
  | "strcmp", [a, b] => return (← compareBytes m (nat a) (nat b) maxBytes true, env)
  | "strncmp", [a, b, n] => return (← compareBytes m (nat a) (nat b) (nat n) true, env)
  | "memcmp", [a, b, n] => return (← compareBytes m (nat a) (nat b) (nat n) false, env)
  | "strcpy", [d, s] =>
    let bs ← m.cstr (nat s)
    return (d, ← env.withMem (·.writeBytes (nat d) (bs.push 0)))
  | "strncpy", [d, s, n] =>
    let bs ← m.cstr (nat s) (nat n)
    let bs := bs ++ Array.replicate (nat n - bs.size) 0
    return (d, ← env.withMem (·.writeBytes (nat d) bs))
  | "strcat", [d, s] =>
    let l := (← m.cstr (nat d)).size
    let bs ← m.cstr (nat s)
    return (d, ← env.withMem (·.writeBytes (nat d + l) (bs.push 0)))
  | "strchr", [s, c] =>
    let bs ← m.cstr (nat s)
    let c := (wrap 1 false c).toNat.toUInt8
    if c == 0 then return (s + bs.size, env)
    match bs.findIdx? (· == c) with
    | some i => return (s + i, env)
    | none => return (0, env)
  | "strrchr", [s, c] =>
    let bs ← m.cstr (nat s)
    let c := (wrap 1 false c).toNat.toUInt8
    if c == 0 then return (s + bs.size, env)
    match (bs.toList.zipIdx.filter (·.1 == c)).getLast? with
    | some (_, i) => return (s + i, env)
    | none => return (0, env)
  | "memcpy", [d, s, n] | "memmove", [d, s, n] =>
    return (d, ← env.withMem (·.copy (nat d) (nat s) (nat n)))
  | "memset", [d, c, n] =>
    let b := (wrap 1 false c).toNat.toUInt8
    return (d, ← env.withMem (·.writeBytes (nat d) (Array.replicate (nat n) b)))
  | "abs", [v] =>
    if v = -2147483648 then ub "abs of INT_MIN" else return (v.natAbs, env)
  | "labs", [v] | "llabs", [v] =>
    if v = -9223372036854775808 then ub "labs of LONG_MIN" else return (v.natAbs, env)
  | n, _ => throw (.unsupported s!"call of the external function {n}")

/-! ## Initializers -/

mutual
/-- Write the constant `c` of type `ty` at `a` (the object is already zeroed). -/
def writeConst (P : Prog) (m : Memory) (a : Nat) (ty : Ctype) : Constant → Except Stop Memory
  | .array et cs => do
    let (esize, _) ← P.sizeAlign et
    writeConsts P m a esize et cs
  | .indeterminate _ | .null => .ok m
  | .integer ic => do
    let t := ofCtype ty
    store m t a (← convTo t (Silmaril.Compile.Forks.Csem.C.intConstValue ic))
  | .character cc => do
    let t := ofCtype ty
    store m t a (← convTo t (Silmaril.Compile.Forks.Csem.C.charValue cc))
  | .predefined pc => do
    let t := ofCtype ty
    store m t a (← convTo t (if pc matches .true_ then 1 else 0))
  | _ => .error (.unsupported "a constant initializer outside C1")
def writeConsts (P : Prog) (m : Memory) (a esize : Nat) (et : Ctype) :
    List Constant → Except Stop Memory
  | [] => .ok m
  | c :: cs => do
    let m ← writeConst P m a et c
    writeConsts P m (a + esize) esize et cs
end

/-! ## Evaluation -/

/-- The usual arithmetic conversions of two operand types. -/
def usualOf (ta tb : CType) : Except Stop CType := do
  let (w, s) := usual (← shape ta) (← shape tb)
  return .int w s

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
    | .str s =>
      match P.strs[(Silmaril.Compile.Forks.Csem.C.stringBytes s).toList]? with
      | some a => .ok (.mem a, env)
      | none => .error (.unsupported "an unknown string literal")
    | .annot _ a => evalL P n fd a env
    | _ => .error (.unsupported "an lvalue outside the fragment")

/-- Evaluate an expression to a value of its type (`typeOf e`). -/
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
    | .const (.integer ic) => do return (← convTo t (Silmaril.Compile.Forks.Csem.C.intConstValue ic), env)
    | .const c => do return (← C0.constVal c t, env)
    | .annot _ a | .cast _ _ a => do
      let (v, env) ← evalE P n fd a env
      return (← convTo t (← convTo (typeOf a) v), env)
    | .unary op a => do
      match op with
      | .plus => let (v, env) ← evalE P n fd a env; return (← convTo t v, env)
      | .minus =>
        let (v, env) ← evalE P n fd a env
        let (w, s) ← shape t
        return (← arith .sub w s 0 (← convTo t v), env)
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
          | _ => do
            let (w, s) := usual (← shape ta) (4, true)
            convTo ta (← arith (if op == .postfixIncr then .add else .sub) w s (wrap w s old) 1)
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
        | _, _, _ =>
          let (w, s) ← shape t
          let ca ← convTo t va
          let cb ← if aop == .shl || aop == .shr then pure vb else convTo t vb
          return (← arith aop w s ca cb, env)
      | .comma =>
        let (_, env) ← evalE P n fd a env
        let (vb, env) ← evalE P n fd b env
        return (← convTo t vb, env)
      | .and | .or =>
        let (va, env) ← evalE P n fd a env
        if (op == .and) == (va == 0) then return (if op == .and then 0 else 1, env)
        let (vb, env) ← evalE P n fd b env
        return (if vb == 0 then 0 else 1, env)
      | _ =>
        let (va, env) ← evalE P n fd a env
        let (vb, env) ← evalE P n fd b env
        let ta := typeOf a
        let tb := typeOf b
        let (ca, cb) ← if ta matches .ptr _ || tb matches .ptr _ then
            pure (wrap 8 false va, wrap 8 false vb)
          else do
            let u ← usualOf ta tb
            pure (← convTo u va, ← convTo u vb)
        let some r := C0.compare op ca cb | .error (.unsupported "a binary operator")
        return (if r then 1 else 0, env)
    | .assign l r => do
      let (v, env) ← evalE P n fd r env
      let (pl, env) ← evalL P n fd l env
      let v ← convTo (typeOf l) v
      return (v, ← writePlace env (typeOf l) v pl)
    | .compoundAssign l aop r => do
      let (vr, env) ← evalE P n fd r env
      let (pl, env) ← evalL P n fd l env
      let tl := typeOf l
      let old ← readPlace fd env tl pl
      let res ← match tl with
        | .ptr _ => do
          let k ← P.pointee tl
          pure (wrap 8 false (if aop == .sub then old - vr * k else old + vr * k))
        | _ => do
          let (w, s) ← if aop == .shl || aop == .shr then pure (promote (← shape tl))
            else pure (usual (← shape tl) (← shape (typeOf r)))
          let cr := if aop == .shl || aop == .shr then vr else wrap w s vr
          convTo tl (← arith aop w s (wrap w s old) cr)
      return (res, ← writePlace env tl res pl)
    | .cond c a b => do
      let (vc, env) ← evalE P n fd c env
      if vc != 0 then
        match a with
        | some a => let (v, env) ← evalE P n fd a env; return (← convTo t v, env)
        | none => return (← convTo t vc, env)
      else
        let (v, env) ← evalE P n fd b env
        return (← convTo t v, env)
    | .call f args => do
      let .functionDecay ⟨_, _, _, .ident g⟩ := f.node
        | .error (.unsupported "an indirect call")
      let pts := (P.protos[g.number]?).getD []
      let (vs, env) ← evalArgs P n fd pts args env
      let (v, env) ← callFn P n g vs env
      return (← convTo t v, env)
    | .assert a => do
      let (v, env) ← evalE P n fd a env
      if v == 0 then .error (.abort env.out) else return (0, env)
    | .sizeof _ ty => do return ((← P.sizeAlign ty).1, env)
    | .alignof _ ty => do return ((← P.sizeAlign ty).2, env)
    | .sizeofExpr a => do
      match a.annotation with
      | .lvalue _ ty _ => return ((← P.sizeAlign ty).1, env)
      | .rvalue _ =>
        let some w := width (typeOf a) | .error (.unsupported "sizeof of an expression")
        return (w, env)
    | .generic _ (some i) assocs =>
      match assocs[i]? with
      | some (.type_ _ _ a) | some (.default a) => do
        let (v, env) ← evalE P n fd a env
        return (← convTo t v, env)
      | none => .error (.unsupported "_Generic without selection")
    | _ => .error (.unsupported "an expression outside the fragment")

/-- Evaluate arguments left to right, converted to the parameter types `pts` (default
argument promotions beyond them). -/
def evalArgs (P : Prog) : Nat → FunDef → List CType → List TypedExpression → Env →
    Except Stop ((List Int) × Env)
  | 0, _, _, _, _ => .error .outOfFuel
  | _ + 1, _, _, [], env => .ok ([], env)
  | n + 1, fd, pts, a :: as, env => do
    let (v, env) ← evalE P n fd a env
    let v ← match pts, typeOf a with
      | pt :: _, _ => convTo pt v
      | [], .ptr _ => pure v
      | [], ta => do let (w, s) := promote (← shape ta); pure (wrap w s v)
    let (vs, env) ← evalArgs P n fd pts.tail as env
    return (v :: vs, env)

/-- Initialize the object of type `ty` at `a` with `init`. -/
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
    | _ => do
      let t := ofCtype ty
      let (v, env) ← evalE P n fd init env
      let v ← convTo t v
      env.withMem (store · t a v)

/-- Call the function `g` on argument values. -/
def callFn (P : Prog) : Nat → Sym → List Int → Env → Except Stop (Int × Env)
  | 0, _, _, _ => .error .outOfFuel
  | n + 1, g, vs, env =>
    match P.funcs[g.number]? with
    | none => external (P.name g) vs env
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
        let v ← convTo pt v
        match frame[x]? with
        | some a => mem ← store mem pt a v
        | none => regs := regs.insert x v
      let (r, ⟨_, _, mem', out⟩) ← loop P n fd (some fd.body) .stop ⟨regs, frame, mem, out⟩
      return ((← convTo fd.ret (r.getD 0)), ⟨caller, callerFrame, { mem' with sp }, out⟩)

/-- Run the statement machine of one activation to its return. -/
def loop (P : Prog) : Nat → FunDef → Option TypedStatement → Kont → Env →
    Except Stop ((Option Int) × Env)
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
      return (if v != 0 then .running (some b) k else .running none k', env)
    | .do_ b c k' => do
      let (v, env) ← evalE P n fd c env
      return (if v != 0 then .running (some b) k else .running none k', env)
    | .switch k => .ok (.running none k, env)
  | n + 1, fd, some s, k, env =>
    match s.node with
    | .skip => .ok (.running none k, env)
    | .expr e => do let (_, env) ← evalE P n fd e env; return (.running none k, env)
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
          let v ← convTo ((fd.locals[x.number]?).getD (typeOf e)) v
          env := env'.setReg x.number v
        | none, none =>
          let ⟨regs, frame, mem, out⟩ := env
          env := ⟨regs.erase x.number, frame, mem, out⟩
      return (.running none k, env)
    | .if_ c a b => do
      let (v, env) ← evalE P n fd c env
      return (.running (some (if v != 0 then a else b)) k, env)
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
      let (v, env) ← evalE P n fd e env
      return (.returned (some (← convTo fd.ret v)), env)
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

/-- The function of a dummy activation (for static initializers). -/
def topFrame : FunDef :=
  { C0.topFrame with memLocals := [], inMem := {} }

/-- The initial memory: string literals, objects of static storage duration (zeroed, then
initialised in declaration order) and `argv`. -/
def initMemory (P : Prog) (fuel : Nat) : Except Stop Env := do
  let size := P.top - base
  let mut mem : Memory :=
    { bytes := ByteArray.mk (Array.replicate size 0), init := ByteArray.mk (Array.replicate size 1),
      roTop := base, sp := P.top }
  for (l, a) in P.strs.toList do
    mem ← mem.writeBytes a l.toArray
  mem := { mem with roTop := P.roTop }
  -- argv[0] = "" (at argv + 16), argv[1] = NULL
  mem ← mem.writeBytes P.argv (Memory.le 8 (P.argv + 16))
  let mut env : Env := { mem }
  let mut done : Std.HashSet Nat := {}
  for (x, ty, init) in P.statics do
    if done.contains x then continue
    let (some a, some e) := (P.gaddr[x]?, init) | continue
    done := done.insert x
    -- objects of types outside the fragment are left zero (`check` rejects their uses)
    if !objType ty then continue
    env ← initAt P fuel topFrame a ty e env
  return env

/-- **The C1 interpreter.** Run `main` with `fuel`. -/
def run (fuel : Nat) (p : TypedProgram) : Result :=
  let P := prepare p
  let r : Except Stop (Int × Env) := do
    let env ← initMemory P fuel
    let some ms := p.1 | .error (.unsupported "no main")
    let some fd := P.funcs[ms.number]? | .error (.unsupported "main is not defined")
    let args : List Int := match fd.params with
      | [] => []
      | [_] => [1]
      | _ :: _ :: rest => [1, (P.argv : Int)] ++ rest.map fun _ => (0 : Int)
    callFn P (fuel + 1) ms args env
  match r with
  | .ok (v, env) => .done ⟨env.out.toList, C0.toStatus v⟩
  | .error (.exit c out) => .done ⟨out.toList, C0.toStatus c⟩
  | .error (.abort out) => .done ⟨out.toList, .signal 6⟩
  | .error (.undefined why) => .undefined why
  | .error .outOfFuel => .outOfFuel
  | .error (.unsupported why) => .unsupported why

/-! ## Behaviours and the language -/

/-- The behaviours of a program under C1, as for C0 (`C0.beh`). -/
def beh (p : TypedProgram) : Set Obs := {o |
  (∃ n, run n p = .done o) ∨ (∃ n why, run n p = .undefined why) ∨
    (o = ⟨[], .diverges⟩ ∧ ∀ n, run n p = .outOfFuel)}

/-- C1 as a semantics of C. -/
def sem : Semantics := beh

/-- C1 as a language of the zoo. -/
def lang : Language.{0} := cSyntax.lang sem

theorem beh_of_done {p : TypedProgram} {n : Nat} {o : Obs} (h : run n p = .done o) :
    o ∈ beh p := .inl ⟨n, h⟩

/-- Undefined behaviour allows every behaviour. -/
theorem beh_of_undefined {p : TypedProgram} {n : Nat} {why : String}
    (h : run n p = .undefined why) : beh p = Set.univ :=
  Set.eq_univ_of_forall fun _ => .inr (.inl ⟨n, why, h⟩)

/-! ## The fragment -/


/-- Is `t` the type of a value of C1 (a scalar or `void`)? -/
def valueType : CType → Bool
  | .int .. | .bool | .void => true
  | .ptr t => pointee t
  | _ => false

/-- A string literal of C1: no encoding prefix. -/
def plainString (s : StringLiteral) : Bool := s.1.isNone || s.1 == some .utf8

mutual
/-- Check that an rvalue is in the fragment. -/
def checkE (P : Prog) : TypedExpression → Except String Unit
  | .mk ann _ _ node => do
    match ann with
    | .lvalue .. => throw "an lvalue in value position"
    | .rvalue g =>
      if !valueType (ofGenType g) then throw "an expression of a type outside C1"
    checkN P node
def checkN (P : Prog) : ExpressionNode GenTypeCategory → Except String Unit
  | .rvalue a | .arrayDecay a => checkLv P a
  | .const c =>
    match c with
    | .integer _ | .character _ | .predefined _ | .null => pure ()
    | _ => throw "a constant outside C1"
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
  | .call f args => do
    match f.node with
    | .functionDecay ⟨_, _, _, .ident g⟩ =>
      if !P.funcs.contains g.number && !(externals.contains (P.name g)) then
        throw s!"call of the external function {P.name g}"
    | _ => throw "an indirect call"
    checkL P args
  | .sizeof .. | .alignof .. => pure ()
  | .sizeofExpr _ => pure ()
  | .generic _ (some _) assocs => checkG P assocs
  | _ => throw "an expression outside the fragment"
/-- Check that an lvalue is in the fragment. -/
def checkLv (P : Prog) : TypedExpression → Except String Unit
  | .mk ann _ _ node => do
    match ann with
    | .lvalue _ ty _ => if !objType ty then throw "an object of a type outside C1"
    | .rvalue _ => throw "an rvalue in lvalue position"
    match node with
    | .ident _ => pure ()
    | .unary .indirection p => checkE P p
    | .str s => if !plainString s then throw "a wide string literal"
    | .annot _ a => checkLv P a
    | _ => throw "an lvalue outside C1"
def checkL (P : Prog) : List TypedExpression → Except String Unit
  | [] => pure ()
  | e :: es => do checkE P e; checkL P es
def checkG (P : Prog) : List (GenericAssociation GenTypeCategory) → Except String Unit
  | [] => pure ()
  | .type_ _ _ e :: gs | .default e :: gs => do checkE P e; checkG P gs
end

mutual
/-- Check an initializer of an object of type `ty`. -/
def checkI (P : Prog) : Ctype → TypedExpression → Except String Unit
  | .mk _ (.array et _), .mk _ _ _ node =>
    match node with
    | .array _ _ elems => checkIs P et elems
    | .str s => if plainString s then pure () else throw "a wide string literal"
    | .const c => checkC c
    | _ => throw "an array initializer outside C1"
  | _, e => checkE P e
def checkIs (P : Prog) (et : Ctype) : List (Option TypedExpression) → Except String Unit
  | [] => pure ()
  | none :: es => checkIs P et es
  | some e :: es => do checkI P et e; checkIs P et es
/-- Check an aggregate constant. -/
def checkC : Constant → Except String Unit
  | .array _ cs => checkCs cs
  | .integer _ | .character _ | .predefined _ | .null | .indeterminate _ => pure ()
  | _ => throw "a constant initializer outside C1"
def checkCs : List Constant → Except String Unit
  | [] => pure ()
  | c :: cs => do checkC c; checkCs cs
end

/-- The locals of a statement have types of C1. -/
def checkLocals (bs : Bindings) : Except String Unit := do
  for (x, (_, _, _, ty)) in bs do
    if !objType ty then throw s!"local {Silmaril.Compile.Forks.Csem.C.symName x} of a type outside C1"

mutual
def checkS (P : Prog) (fd : FunDef) : TypedStatement → Except String Unit
  | .mk _ _ _ node => checkSN P fd node
def checkSN (P : Prog) (fd : FunDef) : StatementNode GenTypeCategory → Except String Unit
  | .skip | .break_ | .continue_ | .returnVoid | .goto _ => pure ()
  | .expr e | .return_ e => checkE P e
  | .block bs ss => do checkLocals bs; checkSL P fd ss
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
    | some (_, ty) => checkI P ty e
    | none => checkE P e
    checkD P fd ds
  | (_, none) :: ds => checkD P fd ds
end

/-- The functions defined in the program and reachable from `roots` by direct calls. -/
def reachable (P : Prog) (roots : List Nat) : List Nat := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut todo := roots
  let mut out : Array Nat := #[]
  for _ in [0:P.funcs.size + roots.length + 1] do
    let mut next : List Nat := []
    for f in todo do
      if seen.contains f then continue
      seen := seen.insert f
      if let some fd := P.funcs[f]? then
        out := out.push f
        next := C0.callsS fd.body ++ next
    todo := next
  return out.toList

/-- Is the program in the C1 fragment? The reason when it is not. Only the functions reachable
from `main` are checked, and the initializers of the objects of static storage duration whose
type is in C1 (the others are left zero, and their uses are rejected where they occur). -/
def check (p : TypedProgram) : Except String Unit := do
  let P := prepare p
  let some m := P.main | throw "no main"
  let some _ := P.funcs[m]? | throw "main is not defined"
  let live := reachable P (m :: (P.statics.flatMap fun (_, _, i) => (i.map C0.callsE).getD []))
  for (x, (_, _, d)) in p.2.declarations do
    match d with
    | .function _ (_, ret) ps variadic _ _ =>
      if live.contains x.number then
        if variadic then throw s!"a variadic function {Silmaril.Compile.Forks.Csem.C.symName x}"
        if !valueType (ofCtype ret) then
          throw s!"a function with a result outside C1: {Silmaril.Compile.Forks.Csem.C.symName x}"
        if ps.any fun (_, t, _) => !objType t || !(width (ofCtype t)).isSome then
          throw s!"a function with a parameter outside C1: {Silmaril.Compile.Forks.Csem.C.symName x}"
    | .object .. => pure ()
  for (_, ty, init) in P.statics do
    if objType ty then
      if let some e := init then checkI P ty e
  for f in live do
    if let some fd := P.funcs[f]? then checkS P fd fd.body

/-- The C1 fragment. -/
def InFragment (p : TypedProgram) : Prop := check p = .ok ()

instance (p : TypedProgram) : Decidable (InFragment p) :=
  inferInstanceAs (Decidable (check p = .ok ()))

/-- The fragment as a set of programs. -/
def fragment : Set TypedProgram := {p | InFragment p}

end Silmaril.Compile.C.Sem.C1
