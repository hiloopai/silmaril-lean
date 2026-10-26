module

public import Silmaril.Numeric.Ieee754.CoreFloat
public meta import Silmaril.Numeric.Ieee754.CoreFloat

/-!
# Differential test: runtime `Float`/`Float32` against Silmaril's IEEE operations

The `#eval` checks below run Lean's compiled float primitives (C `double` and
`float` arithmetic, `sqrt`, `fma`, `floor`, `ceil`, `round`, width and integer
conversions) and compare their bits with Silmaril's executable operations on
edge-case and pseudo-random encodings.

* For operations whose core definition is the float model (`+`, `-`, `*`, `/`,
  `sqrt`, `fma`, comparisons, integer conversions), `CoreFloat` proves the
  logical agreement by `rfl`; this test checks the remaining trust boundary,
  that the C implementation agrees with that model.
* Operations core leaves `opaque` (`floor`, `ceil`, `round`,
  `Float.toFloat32`, `Float32.toFloat`) cannot be related to Silmaril by proof
  without axioms. They are only tested here, against `roundIntegral`, `toF32`
  and `toF64`.

Runtime `toBits` canonicalizes NaNs, so every comparison is exact bit equality.
The checks evaluate with the host's floating-point unit and add no axioms; a
mismatch fails the build with the first failing operand encodings.
-/

namespace Silmaril.Numeric.Ieee754.CoreFloatTest

open Silmaril.Numeric.Ieee754

/-- SplitMix64, a deterministic generator for test encodings. -/
def splitMix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9e3779b97f4a7c15
  let z := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (z ^^^ (z >>> 31), s)

/-- `n` pseudo-random 64-bit words from `seed`. -/
def randomWords (seed : UInt64) (n : Nat) : List UInt64 :=
  (List.range n).foldl (fun (acc, s) _ => let (w, s) := splitMix s; (w :: acc, s))
    (([] : List UInt64), seed) |>.1

/-- Random binary64 encodings, half of them with exponents near `1.0`. -/
def random64 (seed : UInt64) (n : Nat) : List UInt64 :=
  (randomWords seed n).mapIdx fun (i : Nat) (w : UInt64) =>
    if i % 2 = 0 then w else (w &&& (0x800fffffffffffff : UInt64)) ||| (((0x3c0 : UInt64) + (w >>> 52) % 0x80) <<< 52)

/-- Random binary32 encodings, half of them with exponents near `1.0`. -/
def random32 (seed : UInt64) (n : Nat) : List UInt32 :=
  (randomWords seed n).mapIdx fun (i : Nat) (w : UInt64) =>
    let v := (w >>> 32).toUInt32
    if i % 2 = 0 then v else (v &&& (0x807fffff : UInt32)) ||| (((0x70 : UInt32) + (v >>> 23) % 0x20) <<< 23)

/-- binary64 edge cases: zeros, subnormals, normal limits, infinities, NaNs,
integers around `2^53`, ties for rounding to integers and inexact decimals. -/
def edge64 : List UInt64 :=
  let pos : List UInt64 := [
    0, 1, 2, 0x000fffffffffffff, 0x0010000000000000, 0x0010000000000001,
    0x3fe0000000000000, 0x3fe0000000000001, 0x3ff0000000000000, 0x3ff0000000000001,
    0x3ff8000000000000, 0x4004000000000000, 0x400c000000000000, 0x3fb999999999999a,
    0x3fd5555555555555, 0x4330000000000000, 0x4330000000000001, 0x4340000000000000,
    0x43e0000000000000, 0x43dfffffffffffff, 0x43f0000000000000, 0x7fefffffffffffff,
    0x7fe0000000000000, 0x7ff0000000000000, 0x7ff8000000000000, 0x7ff0000000000001,
    0x7ff4000000000000, 0x7fffffffffffffff]
  pos ++ pos.map (· ||| 0x8000000000000000)

/-- binary32 edge cases, as for `edge64`. -/
def edge32 : List UInt32 :=
  let pos : List UInt32 := [
    0, 1, 2, 0x007fffff, 0x00800000, 0x00800001, 0x3f000000, 0x3f000001, 0x3f800000,
    0x3f800001, 0x3fc00000, 0x40200000, 0x40600000, 0x3dcccccd, 0x3eaaaaab, 0x4b000000,
    0x4b000001, 0x4b800000, 0x4f000000, 0x4effffff, 0x5f000000, 0x7f7fffff, 0x7f000000,
    0x7f800000, 0x7fc00000, 0x7f800001, 0x7fa00000, 0x7fffffff]
  pos ++ pos.map (· ||| 0x80000000)

/-- binary64 operands: edge cases and random encodings. -/
def operands64 : List UInt64 := edge64 ++ random64 0x5eed64 256

/-- binary32 operands: edge cases and random encodings. -/
def operands32 : List UInt32 := edge32 ++ random32 0x5eed32 256

/-- Pairs: all edge-case pairs plus random pairs. -/
def pairs64 : List (UInt64 × UInt64) :=
  (edge64.flatMap fun a => edge64.map (a, ·)) ++
    (random64 1 512).zip (random64 2 512)

/-- Pairs: all edge-case pairs plus random pairs. -/
def pairs32 : List (UInt32 × UInt32) :=
  (edge32.flatMap fun a => edge32.map (a, ·)) ++
    (random32 1 512).zip (random32 2 512)

/-- Triples for fused multiply-add. -/
def triples64 : List (UInt64 × UInt64 × UInt64) :=
  ((edge64.take 24).flatMap fun a => (edge64.drop 28 |>.take 24).map fun b => (a, b, a ^^^ b)) ++
    ((random64 3 512).zip ((random64 4 512).zip (random64 5 512)))

/-- Triples for fused multiply-add. -/
def triples32 : List (UInt32 × UInt32 × UInt32) :=
  ((edge32.take 24).flatMap fun a => (edge32.drop 28 |>.take 24).map fun b => (a, b, a ^^^ b)) ++
    ((random32 3 512).zip ((random32 4 512).zip (random32 5 512)))

/-- Report the first mismatches of a check, or succeed. -/
def check {α : Type} [ToString α] (name : String) (cases : List α) (ok : α → Bool) :
    IO Unit := do
  let bad := cases.filter (! ok ·)
  unless bad.isEmpty do
    throw <| IO.userError s!"{name}: {bad.length} mismatches, e.g. {bad.take 4}"

-- Model-defined binary64 operations: the C implementation agrees with the model.
#eval check "Float +" pairs64 fun (a, b) => (F64.ofFloat (Float.ofBits a + Float.ofBits b)).bits == (F64.add ⟨a⟩ ⟨b⟩).bits
#eval check "Float -" pairs64 fun (a, b) => (F64.ofFloat (Float.ofBits a - Float.ofBits b)).bits == (F64.sub ⟨a⟩ ⟨b⟩).bits
#eval check "Float *" pairs64 fun (a, b) => (F64.ofFloat (Float.ofBits a * Float.ofBits b)).bits == (F64.mul ⟨a⟩ ⟨b⟩).bits
#eval check "Float /" pairs64 fun (a, b) => (F64.ofFloat (Float.ofBits a / Float.ofBits b)).bits == (F64.div ⟨a⟩ ⟨b⟩).bits
#eval check "Float ==" pairs64 fun (a, b) => (Float.ofBits a == Float.ofBits b) == F64.equal ⟨a⟩ ⟨b⟩
#eval check "Float <" pairs64 fun (a, b) => decide (Float.ofBits a < Float.ofBits b) == F64.lessThan ⟨a⟩ ⟨b⟩
#eval check "Float ≤" pairs64 fun (a, b) => decide (Float.ofBits a ≤ Float.ofBits b) == F64.lessEqual ⟨a⟩ ⟨b⟩
#eval check "Float.sqrt" operands64 fun a => (F64.ofFloat (Float.ofBits a).sqrt).bits == (F64.sqrt ⟨a⟩).bits
#eval check "Float.fma" triples64 fun (a, b, c) =>
  (F64.ofFloat (Float.fma (Float.ofBits a) (Float.ofBits b) (Float.ofBits c))).bits ==
    (F64.fma ⟨a⟩ ⟨b⟩ ⟨c⟩).bits
#eval check "Float.toBits ∘ ofBits" operands64 fun a =>
  (Float.ofBits a).toBits == (F64.ofModel (F64.mk a).model).bits
#eval check "Float.isNaN" operands64 fun a => (Float.ofBits a).isNaN == F64.isNaN ⟨a⟩
#eval check "Int64.toFloat" (random64 6 512 ++ edge64) fun a =>
  (Int64.toFloat a.toInt64).toBits == (F64.ofInt a.toInt64.toInt).bits
#eval check "UInt64.toFloat" (random64 7 512 ++ edge64) fun a =>
  (UInt64.toFloat a).toBits == (F64.ofInt a.toNat).bits
#eval check "Float.toInt64 (in range)" operands64 fun a =>
  match F64.toInt? ⟨a⟩ with
  | some v => !(-2 ^ 63 ≤ v && v < 2 ^ 63) || (Float.ofBits a).toInt64.toInt == v
  | none => true

-- Operations core leaves opaque: tested only.
#eval check "Float.floor" operands64 fun a =>
  (Float.ofBits a).floor.toBits == (F64.roundIntegral .towardNegative ⟨a⟩).bits
#eval check "Float.ceil" operands64 fun a =>
  (Float.ofBits a).ceil.toBits == (F64.roundIntegral .towardPositive ⟨a⟩).bits
#eval check "Float.round" operands64 fun a =>
  (Float.ofBits a).round.toBits == (F64.roundIntegral .nearestTiesToAway ⟨a⟩).bits
#eval check "Float.toFloat32" operands64 fun a =>
  (Float.ofBits a).toFloat32.toBits == (F64.toF32 ⟨a⟩).bits
#eval check "Float32.toFloat" operands32 fun a =>
  (Float32.ofBits a).toFloat.toBits == (F32.toF64 ⟨a⟩).bits

-- Model-defined binary32 operations.
#eval check "Float32 +" pairs32 fun (a, b) => (F32.ofFloat32 (Float32.ofBits a + Float32.ofBits b)).bits == (F32.add ⟨a⟩ ⟨b⟩).bits
#eval check "Float32 -" pairs32 fun (a, b) => (F32.ofFloat32 (Float32.ofBits a - Float32.ofBits b)).bits == (F32.sub ⟨a⟩ ⟨b⟩).bits
#eval check "Float32 *" pairs32 fun (a, b) => (F32.ofFloat32 (Float32.ofBits a * Float32.ofBits b)).bits == (F32.mul ⟨a⟩ ⟨b⟩).bits
#eval check "Float32 /" pairs32 fun (a, b) => (F32.ofFloat32 (Float32.ofBits a / Float32.ofBits b)).bits == (F32.div ⟨a⟩ ⟨b⟩).bits
#eval check "Float32 ==" pairs32 fun (a, b) => (Float32.ofBits a == Float32.ofBits b) == F32.equal ⟨a⟩ ⟨b⟩
#eval check "Float32 <" pairs32 fun (a, b) => decide (Float32.ofBits a < Float32.ofBits b) == F32.lessThan ⟨a⟩ ⟨b⟩
#eval check "Float32 ≤" pairs32 fun (a, b) => decide (Float32.ofBits a ≤ Float32.ofBits b) == F32.lessEqual ⟨a⟩ ⟨b⟩
#eval check "Float32.sqrt" operands32 fun a => (F32.ofFloat32 (Float32.ofBits a).sqrt).bits == (F32.sqrt ⟨a⟩).bits
#eval check "Float32.fma" triples32 fun (a, b, c) =>
  (F32.ofFloat32 (Float32.fma (Float32.ofBits a) (Float32.ofBits b) (Float32.ofBits c))).bits ==
    (F32.fma ⟨a⟩ ⟨b⟩ ⟨c⟩).bits
#eval check "Float32.isNaN" operands32 fun a => (Float32.ofBits a).isNaN == F32.isNaN ⟨a⟩
#eval check "Int32.toFloat32" (random32 8 512 ++ edge32) fun a =>
  (Int32.toFloat32 a.toInt32).toBits == (F32.ofInt a.toInt32.toInt).bits

end Silmaril.Numeric.Ieee754.CoreFloatTest
