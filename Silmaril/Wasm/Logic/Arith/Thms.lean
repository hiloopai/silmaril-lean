module

public import Silmaril.Wasm.Numerics.Integer
public import Mathlib.Data.BitVec

/-!
# `i32`/`i64` arithmetic for program proofs

Wasm's integer instructions are total functions on `BitVec 32`/`BitVec 64`
(`Silmaril.Wasm.Numerics.intBinOp` and friends), with shift and rotate counts
taken modulo the width. After symbolic execution (`wasm_step`, `Silmaril.Wasm.Logic.Tactic.Defs`) a proof is left
with terms such as `intBinOp .i32 .rotr x 7`. This file rewrites them to plain
`BitVec` operations (`@[simp]`, all by `rfl`), and relates those to the `UInt32`/
`UInt64` operations specifications are written with (`toBitVec_*`). What remains
is closed by `bv_decide`'s normalization (`wasm_arith`), by structured lemmas
such as `rotr32_eq`, or by `omega` on `toNat`.

Collected here:

* `intBinOp_i32_*`/`intBinOp_i64_*`: `add sub mul and or xor shl shr_u rotl rotr`;
* `intRelOp_i32_*`, `intTestOp_eqz`: comparisons as `bool32 (decide _)`;
* `bool32`: `bool32_and`, `bool32_eq_zero_iff`, `bool32_ne_zero_iff`;
* `rotr32_eq`/`rotl32_eq`: rotations as shifts, the form SHA-256 specifications use
  (`ROTR^n(x) = (x >> n) ∨ (x << w - n)`);
* `toOption_except_ok`; `ofNat_i32_width` and friends, which normalize
  `BitVec IntType.i32.width` to `BitVec 32`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Core

open Silmaril.Wasm Silmaril.Wasm.Numerics

@[simp] theorem toOption_except_ok {ε α : Type} (a : α) :
    (Except.ok a : Except ε α).toOption = some a := rfl

/-! ## Widths

Constants in decoded code have types `BitVec IntType.i32.width`; values a proof
writes have type `BitVec 32`. The two are defeq but not reducibly so, which
blocks `simp` from applying the lemmas below. These rewrite the width-indexed
forms to `BitVec 32`/`BitVec 64` (by `rfl`), so one normal form is used. -/

theorem ofNat_i32_width (n : Nat) :
    BitVec.ofNat IntType.i32.width n = (BitVec.ofNat 32 n : BitVec 32) := rfl

theorem ofNat_i64_width (n : Nat) :
    BitVec.ofNat IntType.i64.width n = (BitVec.ofNat 64 n : BitVec 64) := rfl

theorem setWidth_i32_width {w : Nat} (c : BitVec w) :
    c.setWidth IntType.i32.width = (c.setWidth 32 : BitVec 32) := rfl

theorem setWidth_i64_width {w : Nat} (c : BitVec w) :
    c.setWidth IntType.i64.width = (c.setWidth 64 : BitVec 64) := rfl

/-! ## `i32` -/

section I32
variable (x y : BitVec 32)

@[simp] theorem intBinOp_i32_add : intBinOp .i32 .add x y = .ok (x + y) := rfl
@[simp] theorem intBinOp_i32_sub : intBinOp .i32 .sub x y = .ok (x - y) := rfl
@[simp] theorem intBinOp_i32_mul : intBinOp .i32 .mul x y = .ok (x * y) := rfl
@[simp] theorem intBinOp_i32_and : intBinOp .i32 .and x y = .ok (x &&& y) := rfl
@[simp] theorem intBinOp_i32_or : intBinOp .i32 .or x y = .ok (x ||| y) := rfl
@[simp] theorem intBinOp_i32_xor : intBinOp .i32 .xor x y = .ok (x ^^^ y) := rfl
@[simp] theorem intBinOp_i32_shl : intBinOp .i32 .shl x y = .ok (x <<< (y.toNat % 32)) := rfl
@[simp] theorem intBinOp_i32_shrU :
    intBinOp .i32 (.shr .unsigned) x y = .ok (x >>> (y.toNat % 32)) := rfl
@[simp] theorem intBinOp_i32_rotl : intBinOp .i32 .rotl x y = .ok (x.rotateLeft y.toNat) := rfl
@[simp] theorem intBinOp_i32_rotr : intBinOp .i32 .rotr x y = .ok (x.rotateRight y.toNat) := rfl

@[simp] theorem intRelOp_i32_eq : intRelOp .i32 .eq x y = bool32 (x == y) := rfl
@[simp] theorem intRelOp_i32_ne : intRelOp .i32 .ne x y = bool32 (x != y) := rfl
@[simp] theorem intRelOp_i32_ltU :
    intRelOp .i32 (.lt .unsigned) x y = bool32 (decide (x.toNat < y.toNat)) := rfl
@[simp] theorem intRelOp_i32_leU :
    intRelOp .i32 (.le .unsigned) x y = bool32 (decide (x.toNat ≤ y.toNat)) := rfl
@[simp] theorem intRelOp_i32_gtU :
    intRelOp .i32 (.gt .unsigned) x y = bool32 (decide (x.toNat > y.toNat)) := rfl
@[simp] theorem intRelOp_i32_geU :
    intRelOp .i32 (.ge .unsigned) x y = bool32 (decide (x.toNat ≥ y.toNat)) := rfl

end I32

/-! ## `i64` -/

section I64
variable (x y : BitVec 64)

@[simp] theorem intBinOp_i64_add : intBinOp .i64 .add x y = .ok (x + y) := rfl
@[simp] theorem intBinOp_i64_sub : intBinOp .i64 .sub x y = .ok (x - y) := rfl
@[simp] theorem intBinOp_i64_mul : intBinOp .i64 .mul x y = .ok (x * y) := rfl
@[simp] theorem intBinOp_i64_and : intBinOp .i64 .and x y = .ok (x &&& y) := rfl
@[simp] theorem intBinOp_i64_or : intBinOp .i64 .or x y = .ok (x ||| y) := rfl
@[simp] theorem intBinOp_i64_xor : intBinOp .i64 .xor x y = .ok (x ^^^ y) := rfl
@[simp] theorem intBinOp_i64_shl : intBinOp .i64 .shl x y = .ok (x <<< (y.toNat % 64)) := rfl
@[simp] theorem intBinOp_i64_shrU :
    intBinOp .i64 (.shr .unsigned) x y = .ok (x >>> (y.toNat % 64)) := rfl
@[simp] theorem intBinOp_i64_rotl : intBinOp .i64 .rotl x y = .ok (x.rotateLeft y.toNat) := rfl
@[simp] theorem intBinOp_i64_rotr : intBinOp .i64 .rotr x y = .ok (x.rotateRight y.toNat) := rfl

end I64

@[simp] theorem intTestOp_eqz (t : IntType) (x : BitVec t.width) :
    intTestOp t .eqz x = bool32 (x == 0) := rfl

/-! ## Booleans as `i32` -/

theorem bool32_and (a b : Bool) : bool32 a &&& bool32 b = bool32 (a && b) := by
  cases a <;> cases b <;> decide

@[simp] theorem bool32_eq_zero_iff (b : Bool) : bool32 b = 0 ↔ b = false := by
  cases b <;> decide

@[simp] theorem bool32_ne_zero_iff (b : Bool) : bool32 b ≠ 0 ↔ b = true := by
  cases b <;> decide

/-! ## Rotations as shifts -/

/-- `ROTR^n(x) = (x >> n) ∨ (x << 32 - n)` for `n < 32`. -/
theorem rotr32_eq (x : BitVec 32) {n : Nat} (hn : n < 32) :
    x.rotateRight n = (x >>> n) ||| (x <<< (32 - n)) := by
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt hn]

/-- `ROTL^n(x) = (x << n) ∨ (x >> 32 - n)` for `n < 32`. -/
theorem rotl32_eq (x : BitVec 32) {n : Nat} (hn : n < 32) :
    x.rotateLeft n = (x <<< n) ||| (x >>> (32 - n)) := by
  rw [BitVec.rotateLeft_def, Nat.mod_eq_of_lt hn]

/-! ## `UInt32`/`UInt64` -/

theorem toBitVec_add32 (a b : UInt32) : (a + b).toBitVec = a.toBitVec + b.toBitVec := rfl
theorem toBitVec_xor32 (a b : UInt32) : (a ^^^ b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl
theorem toBitVec_and32 (a b : UInt32) : (a &&& b).toBitVec = a.toBitVec &&& b.toBitVec := rfl
theorem toBitVec_or32 (a b : UInt32) : (a ||| b).toBitVec = a.toBitVec ||| b.toBitVec := rfl

/-- A `UInt32` rotation written with shifts is the `BitVec` rotation. -/
theorem toBitVec_rotr32 (x : UInt32) {n : Nat} (hn : 0 < n) (hn' : n < 32) :
    ((x >>> n.toUInt32) ||| (x <<< (32 - n).toUInt32)).toBitVec = x.toBitVec.rotateRight n := by
  rw [rotr32_eq _ hn', UInt32.toBitVec_or, UInt32.toBitVec_shiftRight, UInt32.toBitVec_shiftLeft,
    BitVec.ushiftRight_eq', BitVec.shiftLeft_eq']
  congr 2
  · simp [BitVec.toNat_umod]; omega
  · simp [BitVec.toNat_umod]; omega

end Silmaril.Wasm.Logic.Core
