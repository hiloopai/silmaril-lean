module

public import Mathlib.Data.BitVec
public import Silmaril.Machine.LittleEndian
public import Silmaril.Numeric.Float.Instances

/-!
# Lir: a target-independent low-level IR

`Lir` is a register-transfer language with control flow, calls, a linear byte
memory, per-frame stack slots and explicit traps. It is parameterised by its
register type: source compilers use an unbounded type of virtual registers and
the spilling pass (`Lir.Alloc`) produces programs over a finite type of physical
registers. The language contains no calling convention, register class,
addressing-mode or immediate-range policy of any particular architecture.

## Values and 32-bit arithmetic

Every register and slot holds a 64-bit word. 32-bit arithmetic uses explicit
extension operators (`sext8/16/32`, `zext8/16/32`) together with a small set
of 32-bit operators. The rule is:

* operators whose low 32 result bits depend only on the low 32 bits of the
  operands (`add`, `sub`, `mul`, `and`, `or`, `xor`) exist only at 64 bits; a
  32-bit result is obtained by following them with `zext32` (or `sext32`)
  where a canonical form is required (a standard property of these operators;
  it is not proved in this file);
* operators whose low 32 bits also depend on the upper operand bits (shifts,
  rotates, division, remainder, comparisons, `clz`, `ctz`, `popcnt`) have
  explicit 32-bit forms. These read only the low 32 bits of their operands and
  produce a **zero-extended** 32-bit result.

The zero-extended convention is a choice: RV64 `*w` instructions sign-extend
and x86-64 32-bit operations zero-extend, so one of the two backends must emit
an extension for the 32-bit operators. Nothing in the language relies on the
upper bits of a register holding a 32-bit value unless an operator reads them.

## Floating point

A floating-point value is its IEEE 754 encoding in a word: binary64 in the whole
word, binary32 in the low 32 bits. The floating-point instruction `fop` reads
two registers and writes one (`FOp.eval`); its binary32 operands are the low 32
bits of the registers and its binary32 results are zero-extended. Every
operator is total: exceptions are masked, so a NaN or an out-of-range
conversion has a defined result. The results are those of the shared
floating-point profile `Lir.floatProfile` (x86 SSE under the default MXCSR:
nearest-even, gradual underflow, first-operand NaN propagation, the default NaN
`0xFFF8…`, and the "integer indefinite" `intMin` of out-of-range
conversions), which is also what C compiled by gcc for x86-64 computes. A
backend for another unit (RISC-V's canonical NaN, for one) must adjust NaN
results or reject `fop`.

## Undefined behaviour

Division and remainder have no defined result on a zero divisor or on signed
overflow (`intMin / -1` and `intMin % -1`); the step is stuck. Source
compilers must guard these cases (for WebAssembly: trap on zero and on
`div_s` overflow, return `0` for `rem_s` overflow). Memory accesses outside the
linear memory, reads of registers or slots that were never written in the
current frame, jumps to missing blocks, calls to missing functions and argument
or result count mismatches are also stuck. Backends need no checks for any of
these conditions.
-/

@[expose] public section

namespace Silmaril.Machine.Lir

/-- Registers, slots and memory addresses in Lir are 64-bit words. -/
abbrev Word := BitVec 64
abbrev Byte := BitVec 8

/-- Function identifiers index the program's function table. -/
abbrev FuncId := Nat
/-- Labels index a function's block list. -/
abbrev Label := Nat

/-- Comparisons producing `1` (true) or `0` (false). -/
inductive Cond where
  | eq | ne | lts | ltu | les | leu | gts | gtu | ges | geu
  deriving DecidableEq, Repr

/-- Operators with one register operand. The `32` forms read the low 32 bits
and produce a zero-extended result. -/
inductive Unop where
  | clz | ctz | popcnt
  | clz32 | ctz32 | popcnt32
  | sext8 | sext16 | sext32
  | zext8 | zext16 | zext32
  | eqz
  deriving DecidableEq, Repr

/-- Operators with two register operands. Shift and rotate counts are taken
modulo the operation width. Division and remainder are partial. -/
inductive Binop where
  | add | sub | mul | mulhs | mulhu | and | or | xor
  | shl | shrs | shru | rotl | rotr
  | shl32 | shrs32 | shru32 | rotl32 | rotr32
  | divs | divu | rems | remu
  | divs32 | divu32 | rems32 | remu32
  | cmp (c : Cond)
  | cmp32 (c : Cond)
  deriving DecidableEq, Repr

/-- Access widths of loads and stores, in bytes. -/
inductive Width where
  | b1 | b2 | b4 | b8
  deriving DecidableEq, Repr

def Width.bytes : Width → Nat
  | .b1 => 1
  | .b2 => 2
  | .b4 => 4
  | .b8 => 8

/-- How a narrow load fills the upper bits of the destination. -/
inductive Ext where
  | zero | sign
  deriving DecidableEq, Repr

/-- A location of the current frame: a register or a numbered stack slot.
Locations appear only at call boundaries (parameters, arguments, results and
returned values), where they model stack-passed values. -/
inductive Loc (R : Type) where
  | reg (r : R)
  | slot (n : Nat)
  deriving DecidableEq, Repr

/-- Straight-line operations. None of them changes control flow. The address of
a memory access is the unsigned value of `base` plus the constant `offset`,
computed without wrap-around. -/
inductive Op (R : Type) where
  | const (dest : R) (value : Word)
  | move (dest source : R)
  | unary (op : Unop) (dest source : R)
  | binary (op : Binop) (dest first second : R)
  | load (width : Width) (ext : Ext) (dest base : R) (offset : Nat)
  | store (width : Width) (base : R) (offset : Nat) (source : R)
  | slotGet (dest : R) (slot : Nat)
  | slotSet (slot : Nat) (source : R)
  deriving DecidableEq, Repr

/-- IEEE 754 formats of the floating-point operators. -/
inductive FFmt where
  | f32 | f64
  deriving DecidableEq, Repr

/-- Floating-point comparisons, as in C: `lt` and `le` are false, and `ne` is
true, when an operand is a NaN. `x > y` is `y < x` and `x ≥ y` is `y ≤ x`. -/
inductive FCond where
  | eq | ne | lt | le
  deriving DecidableEq, Repr

/-- Floating-point operators. Unary operators read only their first operand.

* `add sub mul div`: arithmetic in one format, rounded to nearest even;
* `cmp`: `1` or `0`;
* `ofInt`: the signed 64-bit integer to the format, rounded to nearest even;
* `toInt f wide`: truncation toward zero to a signed 64-bit integer (`wide`) or
  a signed 32-bit integer, zero-extended; NaN and out-of-range values give the
  most negative integer of the width;
* `widen`: binary32 to binary64 (exact); `narrow`: binary64 to binary32,
  rounded to nearest even. -/
inductive FOp where
  | add (f : FFmt) | sub (f : FFmt) | mul (f : FFmt) | div (f : FFmt)
  | cmp (f : FFmt) (c : FCond)
  | ofInt (f : FFmt)
  | toInt (f : FFmt) (wide : Bool)
  | widen | narrow
  deriving DecidableEq, Repr

/-- Instructions: straight-line operations, floating-point operations and
calls. `fop op d x y` writes `op.eval` of the values of `x` and `y` to `d`. A call
evaluates its argument locations, runs the callee in a fresh frame, and writes
the returned values to its result locations. -/
inductive Instr (R : Type) where
  | op (o : Op R)
  | call (callee : FuncId) (args : List (Loc R)) (results : List (Loc R))
  | fop (op : FOp) (dest first second : R)
  deriving DecidableEq, Repr

/-- Block terminators. `branch c l₁ l₂` continues at `l₁` when `c` is nonzero.
`ret` returns the listed values to the caller (or ends the program). -/
inductive Term (R : Type) where
  | jump (target : Label)
  | branch (cond : R) (ifNonzero ifZero : Label)
  | ret (values : List (Loc R))
  | trap
  deriving DecidableEq, Repr

structure Block (R : Type) where
  instrs : List (Instr R)
  term : Term R
  deriving DecidableEq, Repr

/-- A function: parameter locations of its fresh frame, an entry label and its
blocks, indexed by label. -/
structure Func (R : Type) where
  params : List (Loc R)
  entry : Label
  blocks : List (Block R)
  deriving DecidableEq, Repr

/-- A program is a function table indexed by `FuncId`. -/
structure Prog (R : Type) where
  funcs : List (Func R)
  deriving DecidableEq, Repr

/-! ## Operator semantics -/

def ofBool (b : Bool) : Word := if b then 1 else 0

/-- Zero-extend a 32-bit result. -/
def of32 (x : BitVec 32) : Word := x.setWidth 64

def lo32 (x : Word) : BitVec 32 := x.setWidth 32

def Cond.eval {w : Nat} : Cond → BitVec w → BitVec w → Bool
  | .eq, x, y => x == y
  | .ne, x, y => x != y
  | .lts, x, y => decide (x.toInt < y.toInt)
  | .ltu, x, y => decide (x.toNat < y.toNat)
  | .les, x, y => decide (x.toInt ≤ y.toInt)
  | .leu, x, y => decide (x.toNat ≤ y.toNat)
  | .gts, x, y => decide (x.toInt > y.toInt)
  | .gtu, x, y => decide (x.toNat > y.toNat)
  | .ges, x, y => decide (x.toInt ≥ y.toInt)
  | .geu, x, y => decide (x.toNat ≥ y.toNat)

def Unop.eval : Unop → Word → Word
  | .clz, x => x.clz
  | .ctz, x => x.ctz
  | .popcnt, x => x.cpop
  | .clz32, x => of32 (lo32 x).clz
  | .ctz32, x => of32 (lo32 x).ctz
  | .popcnt32, x => of32 (lo32 x).cpop
  | .sext8, x => (x.setWidth 8).signExtend 64
  | .sext16, x => (x.setWidth 16).signExtend 64
  | .sext32, x => (x.setWidth 32).signExtend 64
  | .zext8, x => (x.setWidth 8).setWidth 64
  | .zext16, x => (x.setWidth 16).setWidth 64
  | .zext32, x => of32 (lo32 x)
  | .eqz, x => ofBool (x == 0)

/-- Division and remainder at width `w`. `none` on a zero divisor and on signed
overflow; these are undefined, not traps. -/
def divOp {w : Nat} (signed rem : Bool) (x y : BitVec w) : Option (BitVec w) :=
  if y = 0 then none
  else if signed then
    if x = BitVec.intMin w ∧ y = -1 then none
    else some (if rem then x.srem y else x.sdiv y)
  else some (if rem then x % y else x / y)

/-- The high 64 bits of the 128-bit product. -/
def mulHigh (signed : Bool) (x y : Word) : Word :=
  if signed then ((x.signExtend 128) * (y.signExtend 128)).extractLsb' 64 64
  else ((x.setWidth 128) * (y.setWidth 128)).extractLsb' 64 64

def Binop.eval : Binop → Word → Word → Option Word
  | .add, x, y => some (x + y)
  | .sub, x, y => some (x - y)
  | .mul, x, y => some (x * y)
  | .mulhs, x, y => some (mulHigh true x y)
  | .mulhu, x, y => some (mulHigh false x y)
  | .and, x, y => some (x &&& y)
  | .or, x, y => some (x ||| y)
  | .xor, x, y => some (x ^^^ y)
  | .shl, x, y => some (x <<< (y.toNat % 64))
  | .shrs, x, y => some (x.sshiftRight (y.toNat % 64))
  | .shru, x, y => some (x >>> (y.toNat % 64))
  | .rotl, x, y => some (x.rotateLeft (y.toNat % 64))
  | .rotr, x, y => some (x.rotateRight (y.toNat % 64))
  | .shl32, x, y => some (of32 (lo32 x <<< (y.toNat % 32)))
  | .shrs32, x, y => some (of32 ((lo32 x).sshiftRight (y.toNat % 32)))
  | .shru32, x, y => some (of32 (lo32 x >>> (y.toNat % 32)))
  | .rotl32, x, y => some (of32 ((lo32 x).rotateLeft (y.toNat % 32)))
  | .rotr32, x, y => some (of32 ((lo32 x).rotateRight (y.toNat % 32)))
  | .divs, x, y => divOp true false x y
  | .divu, x, y => divOp false false x y
  | .rems, x, y => divOp true true x y
  | .remu, x, y => divOp false true x y
  | .divs32, x, y => (divOp true false (lo32 x) (lo32 y)).map of32
  | .divu32, x, y => (divOp false false (lo32 x) (lo32 y)).map of32
  | .rems32, x, y => (divOp true true (lo32 x) (lo32 y)).map of32
  | .remu32, x, y => (divOp false true (lo32 x) (lo32 y)).map of32
  | .cmp c, x, y => some (ofBool (c.eval x y))
  | .cmp32 c, x, y => some (ofBool (c.eval (lo32 x) (lo32 y)))

/-! ## Floating-point semantics -/

/-- The floating-point unit configuration of `FOp.eval`: x86 SSE with the
default MXCSR (no DAZ, no FZ). -/
def floatProfile : Numeric.Float.Profile := Numeric.Float.Profile.x86SSE {}

/-- The IEEE format of a Lir floating-point format. -/
def FFmt.fmt : FFmt → _root_.Float.Model.Format
  | .f32 => .binary32
  | .f64 => .binary64

/-- The encoding held in a word: its low `32` or `64` bits. -/
def FFmt.get (f : FFmt) (x : Word) : Numeric.Float.Bits f.fmt := x.setWidth _

/-- A word holding an encoding, zero-extended. -/
def FFmt.put (f : FFmt) (b : Numeric.Float.Bits f.fmt) : Word := b.setWidth 64

/-- The IEEE comparison predicate of a condition. The signaling flavour only
changes exception flags, which Lir does not observe. -/
def FCond.predicate : FCond → Numeric.Float.Predicate
  | .eq => .eqQuiet
  | .ne => .neQuiet
  | .lt => .ltSignaling
  | .le => .leSignaling

def FOp.eval : FOp → Word → Word → Word
  | .add f, x, y => f.put (floatProfile.binary f.fmt .add .nearestTiesToEven (f.get x) (f.get y)).value
  | .sub f, x, y => f.put (floatProfile.binary f.fmt .sub .nearestTiesToEven (f.get x) (f.get y)).value
  | .mul f, x, y => f.put (floatProfile.binary f.fmt .mul .nearestTiesToEven (f.get x) (f.get y)).value
  | .div f, x, y => f.put (floatProfile.binary f.fmt .div .nearestTiesToEven (f.get x) (f.get y)).value
  | .cmp f c, x, y => ofBool (floatProfile.comparePredicate c.predicate (f.get x) (f.get y)).value
  | .ofInt f, x, _ => f.put (floatProfile.ofInt f.fmt .nearestTiesToEven x.toInt).value
  | .toInt f true, x, _ =>
    (floatProfile.toInt f.fmt Numeric.IntFormat.i64 .towardZero (f.get x)).value.setWidth 64
  | .toInt f false, x, _ =>
    (floatProfile.toInt f.fmt Numeric.IntFormat.i32 .towardZero (f.get x)).value.setWidth 64
  | .widen, x, _ =>
    FFmt.f64.put (floatProfile.convert .binary32 .binary64 .nearestTiesToEven (FFmt.f32.get x)).value
  | .narrow, x, _ =>
    FFmt.f32.put (floatProfile.convert .binary64 .binary32 .nearestTiesToEven (FFmt.f64.get x)).value

/-- Every operator other than division and remainder is total. -/
def Binop.partial : Binop → Bool
  | .divs | .divu | .rems | .remu | .divs32 | .divu32 | .rems32 | .remu32 => true
  | _ => false

theorem Binop.eval_isSome (op : Binop) (h : op.partial = false) (x y : Word) :
    (op.eval x y).isSome := by
  cases op <;> simp_all [Binop.partial, Binop.eval]

theorem divOp_zero {w : Nat} (signed rem : Bool) (x : BitVec w) :
    divOp signed rem x 0 = none := by
  simp [divOp]

theorem divOp_overflow {w : Nat} (rem : Bool) :
    divOp true rem (BitVec.intMin w) (-1) = none := by
  unfold divOp
  split <;> simp

/-- `divOp` is defined exactly on a nonzero divisor without signed overflow,
and then it is the bitvector quotient or remainder. `divOp_zero` and
`divOp_overflow` are the two `none` directions; this is the characterisation
both of them and the backends' one-directional `divOp_some` specialise. -/
theorem divOp_eq_some {w : Nat} {signed rem : Bool} {x y z : BitVec w} :
    divOp signed rem x y = some z ↔
      y ≠ 0 ∧ (signed = true → ¬ (x = BitVec.intMin w ∧ y = -1)) ∧
        z = if signed then (if rem then x.srem y else x.sdiv y) else
          (if rem then x % y else x / y) := by
  unfold divOp
  by_cases hy : y = 0
  · simp [hy]
  · cases signed
    · simp only [hy, ite_false, Option.some.injEq, Bool.false_eq_true, ne_eq, not_false_eq_true,
        false_implies, true_and]
      exact eq_comm
    · by_cases hov : x = BitVec.intMin w ∧ y = -1
      · simp [hov]
      · simp only [hy, hov, ite_false, ite_true, Option.some.injEq, ne_eq, not_false_eq_true,
          forall_const, true_and]
        exact eq_comm

/-! ## Linear memory

A single linear memory of `size` bytes at addresses `0 … size - 1`. The size is
fixed during execution; there is no `grow` operation. -/

structure Memory where
  size : Nat
  bytes : Nat → Byte

/-- Little-endian read of `n` bytes starting at `addr`, zero-extended. -/
def readLE (bytes : Nat → Byte) (addr : Nat) : Nat → Word
  | 0 => 0
  | n + 1 => (bytes addr).setWidth 64 ||| (readLE bytes (addr + 1) n <<< 8)

/-- Little-endian write of the low `n` bytes of `value` starting at `addr`. -/
def writeLE (bytes : Nat → Byte) (addr n : Nat) (value : Word) : Nat → Byte :=
  fun a => if addr ≤ a ∧ a < addr + n then LittleEndian.wordByte value (a - addr) else bytes a

def extend (width : Width) (ext : Ext) (raw : Word) : Word :=
  match ext with
  | .zero => raw
  | .sign => (raw.setWidth (8 * width.bytes)).signExtend 64

namespace Memory

def InBounds (m : Memory) (addr : Nat) (width : Width) : Prop :=
  addr + width.bytes ≤ m.size

instance (m : Memory) (addr : Nat) (width : Width) : Decidable (m.InBounds addr width) :=
  inferInstanceAs (Decidable (_ ≤ _))

def load (m : Memory) (width : Width) (ext : Ext) (addr : Nat) : Option Word :=
  if m.InBounds addr width then some (extend width ext (readLE m.bytes addr width.bytes))
  else none

def store (m : Memory) (width : Width) (addr : Nat) (value : Word) : Option Memory :=
  if m.InBounds addr width then some { m with bytes := writeLE m.bytes addr width.bytes value }
  else none

/-- A memory of `size` bytes holding `init` at its start and zeros elsewhere. -/
def ofList (size : Nat) (init : List Byte) : Memory :=
  ⟨size, fun a => init.getD a 0⟩

theorem store_size {m m' : Memory} {width : Width} {addr : Nat} {value : Word}
    (h : m.store width addr value = some m') : m'.size = m.size := by
  unfold store at h
  split at h <;> cases h
  rfl

end Memory

/-! ## Program lookup -/

namespace Prog

variable {R : Type}

def func? (p : Prog R) (f : FuncId) : Option (Func R) := p.funcs[f]?

def block? (p : Prog R) (f : FuncId) (l : Label) : Option (Block R) :=
  (p.func? f).bind fun fn => fn.blocks[l]?

end Prog

end Silmaril.Machine.Lir
