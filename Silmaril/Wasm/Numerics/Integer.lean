module

-- Kernel computation uses the body of the upstream derived instance.
import all Batteries.Data.Except

public import Silmaril.Wasm.Ops
public import Mathlib.Data.BitVec

@[expose] public section

/-! # Integer execution

Words wrap modulo their width. Shift counts are reduced modulo that width.
Division traps on zero and signed overflow; signed remainder only traps on zero.
-/

namespace Silmaril.Wasm
namespace Numerics

inductive IntTrap where
  | divideByZero | overflow
  deriving DecidableEq, Repr

abbrev IntValue (t : IntType) := BitVec t.width

/-- Execution on raw operators is total; source correspondence for `extend`
requires `op.valid t = true`, checked separately by instruction validation. -/
def intUnOp (t : IntType) (op : IntUnOp) (x : IntValue t) : IntValue t :=
  match op with
  | .clz => x.clz
  | .ctz => x.ctz
  | .popcnt => x.cpop
  | .extend size => (x.setWidth size.width).signExtend t.width

def intBinOp (t : IntType) (op : IntBinOp) (x y : IntValue t) :
    Except IntTrap (IntValue t) :=
  match op with
  | .add => .ok (x + y)
  | .sub => .ok (x - y)
  | .mul => .ok (x * y)
  | .div .unsigned =>
      if y = 0 then .error .divideByZero else .ok (x / y)
  | .div .signed =>
      if y = 0 then .error .divideByZero
      else if x = BitVec.intMin t.width ∧ y = -1 then .error .overflow
      else .ok (x.sdiv y)
  | .rem .unsigned =>
      if y = 0 then .error .divideByZero else .ok (x % y)
  | .rem .signed =>
      if y = 0 then .error .divideByZero else .ok (x.srem y)
  | .and => .ok (x &&& y)
  | .or => .ok (x ||| y)
  | .xor => .ok (x ^^^ y)
  | .shl => .ok (x <<< (y.toNat % t.width))
  | .shr .unsigned => .ok (x >>> (y.toNat % t.width))
  | .shr .signed => .ok (x.sshiftRight (y.toNat % t.width))
  | .rotl => .ok (x.rotateLeft y.toNat)
  | .rotr => .ok (x.rotateRight y.toNat)

def bool32 (b : Bool) : BitVec 32 := if b then 1 else 0

def intTestOp (t : IntType) (_ : IntTestOp) (x : IntValue t) : BitVec 32 :=
  bool32 (x == 0)

def intRelOp (t : IntType) (op : IntRelOp) (x y : IntValue t) : BitVec 32 :=
  bool32 <| match op with
  | .eq => x == y
  | .ne => x != y
  | .lt .unsigned => decide (x.toNat < y.toNat)
  | .le .unsigned => decide (x.toNat ≤ y.toNat)
  | .gt .unsigned => decide (x.toNat > y.toNat)
  | .ge .unsigned => decide (x.toNat ≥ y.toNat)
  | .lt .signed => decide (x.toInt < y.toInt)
  | .le .signed => decide (x.toInt ≤ y.toInt)
  | .gt .signed => decide (x.toInt > y.toInt)
  | .ge .signed => decide (x.toInt ≥ y.toInt)

@[simp] theorem intBinOp_add_zero (t : IntType) (x : IntValue t) :
    intBinOp t .add x 0 = .ok x := by simp [intBinOp]

@[simp] theorem intBinOp_div_zero (t : IntType) (s : Signedness) (x : IntValue t) :
    intBinOp t (.div s) x 0 = .error .divideByZero := by cases s <;> simp [intBinOp]

@[simp] theorem intBinOp_rem_zero (t : IntType) (s : Signedness) (x : IntValue t) :
    intBinOp t (.rem s) x 0 = .error .divideByZero := by cases s <;> simp [intBinOp]

theorem unsigned_division (t : IntType) (x y : IntValue t) (hy : y ≠ 0) :
    intBinOp t (.div .unsigned) x y =
      .ok (BitVec.ofNat t.width (x.toNat / y.toNat)) := by
  rw [intBinOp, ite_eq_right hy]
  exact congrArg Except.ok BitVec.udiv_def

theorem signed_division (t : IntType) (x y : IntValue t) (hy : y ≠ 0)
    (hov : x ≠ BitVec.intMin t.width ∨ y ≠ -1) :
    ∃ z, intBinOp t (.div .signed) x y = .ok z ∧ z.toInt = x.toInt.tdiv y.toInt := by
  refine ⟨x.sdiv y, ?_, BitVec.toInt_sdiv_of_ne_or_ne x y hov⟩
  have h : ¬ (x = BitVec.intMin t.width ∧ y = -1) := by
    rintro ⟨hx, hy'⟩
    cases hov with
    | inl hn => exact hn hx
    | inr hn => exact hn hy'
  rw [intBinOp, ite_eq_right hy, ite_eq_right h]

theorem signed_remainder (t : IntType) (x y : IntValue t) (hy : y ≠ 0) :
    ∃ z, intBinOp t (.rem .signed) x y = .ok z ∧ z.toInt = x.toInt.tmod y.toInt := by
  refine ⟨x.srem y, ?_, BitVec.toInt_srem x y⟩
  rw [intBinOp, ite_eq_right hy]

theorem addition_modulo (t : IntType) (x y : IntValue t) :
    ∃ z, intBinOp t .add x y = .ok z ∧
      z.toNat = (x.toNat + y.toNat) % 2 ^ t.width :=
  ⟨x + y, rfl, BitVec.toNat_add x y⟩

theorem multiplication_modulo (t : IntType) (x y : IntValue t) :
    ∃ z, intBinOp t .mul x y = .ok z ∧
      z.toNat = (x.toNat * y.toNat) % 2 ^ t.width :=
  ⟨x * y, rfl, BitVec.toNat_mul x y⟩

theorem sign_extension (t : IntType) (size : PackSize) (x : IntValue t)
    (h : (IntUnOp.extend size).valid t = true) :
    (intUnOp t (.extend size) x).toInt = (x.setWidth size.width).toInt := by
  apply BitVec.toInt_signExtend_of_le
  exact Nat.le_of_lt (of_decide_eq_true h)

theorem bool32_toNat_le_one (b : Bool) : (bool32 b).toNat ≤ 1 := by cases b <;> decide

theorem intRelOp_toNat_le_one (t : IntType) (op : IntRelOp) (x y : IntValue t) :
    (intRelOp t op x y).toNat ≤ 1 := bool32_toNat_le_one _

theorem shift_left_width (t : IntType) (x : IntValue t) :
    intBinOp t .shl x (BitVec.ofNat t.width t.width) = .ok x := by
  cases t
  all_goals
    change Except.ok (x <<< (0 : Nat)) = Except.ok x
    exact congrArg Except.ok (BitVec.shiftLeft_zero x)

example : intBinOp .i32 .add (4294967295#32) (1#32) = .ok (0#32) := by decide
example : intBinOp .i32 (.div .signed) (2147483648#32) (-1#32) = .error .overflow := by decide
example : intBinOp .i32 (.rem .signed) (2147483648#32) (-1#32) = .ok (0#32) := by decide
example : intBinOp .i64 .shl (1#64) (65#64) = .ok (2#64) := by decide
example : intBinOp .i32 (.div .signed) (-7#32) (3#32) = .ok (-2#32) := by decide
example : intRelOp .i64 (.lt .signed) (-1#64) (0#64) = (1#32) := by decide

end Numerics
end Silmaril.Wasm
