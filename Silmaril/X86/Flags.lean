module

public import Mathlib.Data.BitVec

/-!
# x86-64 status flags for a small integer subset

This file records the six arithmetic status flags of RFLAGS (CF, PF, AF, ZF, SF
and OF) and computes them for 64-bit ADD, SUB/CMP, NEG and the logical
operations AND/OR/XOR, following the flag descriptions in the Intel SDM
instruction reference. It is a handwritten local model; it is not derived from,
or proved to correspond with, the Sail, ACL2 or any hardware description.

Each flag is an `Option Bool`. `some b` is an architecturally defined value.
`none` is an architecturally *undefined* value: the SDM permits a processor to
leave any value there, so every concrete value refines it (`FlagValue.Admits`).
The model never replaces an undefined result by a chosen constant. No
instruction of the present subset reads a flag, so an undefined flag is never
consumed; a later flag-reading extension must decide how `none` is observed.

The semantic flag functions (`addCarry`, `subOverflow`, `parity`, ...) are
bit-level formulas over the operands and the wrapped result. The `Spec`
namespace gives an independent arithmetic specification over `Nat` and `Int`,
and `addFlags_eq_spec`, `subFlags_eq_spec`, `negFlags_eq_spec` and
`logicFlags_eq_spec` prove that the two agree for all operands.

The other RFLAGS bits (DF, IF, TF, ...) are outside this model.
-/

@[expose] public section

namespace Silmaril.X86

/-- The six arithmetic status flags of RFLAGS. `none` is an architecturally
undefined value (see `FlagValue.Admits`). -/
structure Flags where
  /-- CF, bit 0. -/
  carry : Option Bool
  /-- PF, bit 2. -/
  parity : Option Bool
  /-- AF, bit 4. -/
  adjust : Option Bool
  /-- ZF, bit 6. -/
  zero : Option Bool
  /-- SF, bit 7. -/
  sign : Option Bool
  /-- OF, bit 11. -/
  overflow : Option Bool
  deriving DecidableEq, Repr

/-- The six status flags as held by a concrete processor. -/
structure ConcreteFlags where
  carry : Bool
  parity : Bool
  adjust : Bool
  zero : Bool
  sign : Bool
  overflow : Bool
  deriving DecidableEq, Repr

/-- A concrete flag value refines a model flag: a defined value must be equal,
and an undefined value admits either Boolean. -/
def FlagValue.Admits : Option Bool → Bool → Prop
  | none, _ => True
  | some b, c => c = b

instance (v : Option Bool) (c : Bool) : Decidable (FlagValue.Admits v c) := by
  cases v <;> unfold FlagValue.Admits <;> infer_instance

@[simp] theorem FlagValue.admits_none (c : Bool) : FlagValue.Admits none c := trivial

@[simp] theorem FlagValue.admits_some (b c : Bool) : FlagValue.Admits (some b) c ↔ c = b :=
  Iff.rfl

/-- Every flag of `concrete` refines the corresponding model flag. -/
def Flags.Admits (model : Flags) (concrete : ConcreteFlags) : Prop :=
  FlagValue.Admits model.carry concrete.carry ∧
  FlagValue.Admits model.parity concrete.parity ∧
  FlagValue.Admits model.adjust concrete.adjust ∧
  FlagValue.Admits model.zero concrete.zero ∧
  FlagValue.Admits model.sign concrete.sign ∧
  FlagValue.Admits model.overflow concrete.overflow

/-- The fully defined model flags of a concrete flag register. -/
def ConcreteFlags.toFlags (c : ConcreteFlags) : Flags :=
  ⟨some c.carry, some c.parity, some c.adjust, some c.zero, some c.sign, some c.overflow⟩

theorem Flags.admits_toFlags_iff (c d : ConcreteFlags) : c.toFlags.Admits d ↔ d = c := by
  cases c; cases d
  simp [Flags.Admits, ConcreteFlags.toFlags]

/-! ## Bit-level result flags, as used by the semantics -/

/-- PF: set when the least-significant byte of the result has an even number of
one bits. -/
def parity (r : BitVec 64) : Bool :=
  !(r.getLsbD 0 ^^ r.getLsbD 1 ^^ r.getLsbD 2 ^^ r.getLsbD 3 ^^
    r.getLsbD 4 ^^ r.getLsbD 5 ^^ r.getLsbD 6 ^^ r.getLsbD 7)

/-- ZF. -/
def isZero (r : BitVec 64) : Bool := r == 0#64

/-- SF: the most-significant bit of the result. -/
def sign (r : BitVec 64) : Bool := r.msb

/-- CF of `x + y`: the carry out of bit 63, from operand and result sign bits. -/
def addCarry (x y : BitVec 64) : Bool :=
  ((x &&& y) ||| ((x ||| y) &&& ~~~(x + y))).msb

/-- OF of `x + y`: both operands differ in sign from the result. -/
def addOverflow (x y : BitVec 64) : Bool :=
  ((x ^^^ (x + y)) &&& (y ^^^ (x + y))).msb

/-- AF of `x + y`: the carry into bit 4. -/
def addAdjust (x y : BitVec 64) : Bool :=
  (x ^^^ y ^^^ (x + y)).getLsbD 4

/-- CF of `x - y`: the borrow out of bit 63. -/
def subBorrow (x y : BitVec 64) : Bool :=
  ((~~~x &&& y) ||| (~~~(x ^^^ y) &&& (x - y))).msb

/-- OF of `x - y`: the operands differ in sign and the result differs from `x`. -/
def subOverflow (x y : BitVec 64) : Bool :=
  ((x ^^^ y) &&& (x ^^^ (x - y))).msb

/-- AF of `x - y`: the borrow into bit 4. -/
def subAdjust (x y : BitVec 64) : Bool :=
  (x ^^^ y ^^^ (x - y)).getLsbD 4

/-- ADD sets all six flags according to the result. -/
def addFlags (x y : BitVec 64) : Flags where
  carry := some (addCarry x y)
  parity := some (parity (x + y))
  adjust := some (addAdjust x y)
  zero := some (isZero (x + y))
  sign := some (sign (x + y))
  overflow := some (addOverflow x y)

/-- SUB and CMP set all six flags according to `x - y`. -/
def subFlags (x y : BitVec 64) : Flags where
  carry := some (subBorrow x y)
  parity := some (parity (x - y))
  adjust := some (subAdjust x y)
  zero := some (isZero (x - y))
  sign := some (sign (x - y))
  overflow := some (subOverflow x y)

/-- NEG clears CF exactly when its operand is zero; OF, SF, ZF, AF and PF are
set according to the result, as for `0 - x`. -/
def negFlags (x : BitVec 64) : Flags where
  carry := some (x != 0#64)
  parity := some (parity (0#64 - x))
  adjust := some (subAdjust 0#64 x)
  zero := some (isZero (0#64 - x))
  sign := some (sign (0#64 - x))
  overflow := some (subOverflow 0#64 x)

/-- AND, OR and XOR clear CF and OF, set SF, ZF and PF according to the result
`r`, and leave AF undefined. -/
def logicFlags (r : BitVec 64) : Flags where
  carry := some false
  parity := some (parity r)
  adjust := none
  zero := some (isZero r)
  sign := some (sign r)
  overflow := some false

/-! ## Independent arithmetic specification -/

namespace Spec

/-- PF: the low byte of `n` has an even number of one bits. -/
def parity (n : Nat) : Bool :=
  decide (((List.range 8).countP fun i => (n % 2 ^ 8).testBit i) % 2 = 0)

/-- SF, read as a signed integer: the result is negative. Used only as a
second characterization of `X86.sign`; the flag specifications below state SF
over `Nat`. -/
def sign (r : BitVec 64) : Bool := decide (r.toInt < 0)

def addFlags (x y : BitVec 64) : Flags where
  carry := some (decide (2 ^ 64 ≤ x.toNat + y.toNat))
  parity := some (parity (x.toNat + y.toNat))
  adjust := some (decide (16 ≤ x.toNat % 16 + y.toNat % 16))
  zero := some (decide ((x.toNat + y.toNat) % 2 ^ 64 = 0))
  sign := some (decide (2 ^ 63 ≤ (x.toNat + y.toNat) % 2 ^ 64))
  overflow := some (decide (x.toInt + y.toInt < -2 ^ 63 ∨ 2 ^ 63 ≤ x.toInt + y.toInt))

def subFlags (x y : BitVec 64) : Flags where
  carry := some (decide (x.toNat < y.toNat))
  parity := some (parity (x.toNat + (2 ^ 64 - y.toNat)))
  adjust := some (decide (x.toNat % 16 < y.toNat % 16))
  zero := some (decide (x.toNat = y.toNat))
  sign := some (decide (2 ^ 63 ≤ (x.toNat + (2 ^ 64 - y.toNat)) % 2 ^ 64))
  overflow := some (decide (x.toInt - y.toInt < -2 ^ 63 ∨ 2 ^ 63 ≤ x.toInt - y.toInt))

def negFlags (x : BitVec 64) : Flags where
  carry := some (decide (x.toNat ≠ 0))
  parity := some (parity (2 ^ 64 - x.toNat))
  adjust := some (decide (x.toNat % 16 ≠ 0))
  zero := some (decide (x.toNat = 0))
  sign := some (decide (2 ^ 63 ≤ (2 ^ 64 - x.toNat) % 2 ^ 64))
  overflow := some (decide (x.toInt = -2 ^ 63))

def logicFlags (r : BitVec 64) : Flags where
  carry := some false
  parity := some (parity r.toNat)
  adjust := none
  zero := some (decide (r.toNat = 0))
  sign := some (decide (2 ^ 63 ≤ r.toNat))
  overflow := some false

end Spec

/-! ## Agreement of the two formulations -/

private theorem parity_bits (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    (!(b0 ^^ b1 ^^ b2 ^^ b3 ^^ b4 ^^ b5 ^^ b6 ^^ b7)) =
      decide (([b0, b1, b2, b3, b4, b5, b6, b7].countP id) % 2 = 0) := by
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide

theorem parity_eq_spec (r : BitVec 64) : parity r = Spec.parity r.toNat := by
  have hrange : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  have hbit : ∀ i, i < 8 → (r.toNat % 2 ^ 8).testBit i = r.getLsbD i := by
    intro i hi
    rw [Nat.testBit_mod_two_pow]
    simp [hi, BitVec.testBit_toNat]
  simp only [parity, Spec.parity, hrange, parity_bits]
  congr 3
  simp only [List.countP_cons, List.countP_nil, id, hbit _ (by decide : (0 : Nat) < 8),
    hbit _ (by decide : (1 : Nat) < 8), hbit _ (by decide : (2 : Nat) < 8),
    hbit _ (by decide : (3 : Nat) < 8), hbit _ (by decide : (4 : Nat) < 8),
    hbit _ (by decide : (5 : Nat) < 8), hbit _ (by decide : (6 : Nat) < 8),
    hbit _ (by decide : (7 : Nat) < 8)]

theorem isZero_eq_spec (r : BitVec 64) : isZero r = decide (r.toNat = 0) := by
  unfold isZero
  by_cases h : r = 0#64
  · subst h; simp
  · have hn : r.toNat ≠ 0 := fun hn => h (BitVec.eq_of_toNat_eq (by simpa using hn))
    simp [h, hn]

theorem sign_eq_toNat (r : BitVec 64) : sign r = decide (2 ^ 63 ≤ r.toNat) := by
  simp [sign, BitVec.msb_eq_decide]

theorem sign_eq_spec (r : BitVec 64) : sign r = Spec.sign r := by
  simp [sign, Spec.sign, BitVec.msb_eq_toInt]

private theorem msb_eq_bit63 (x : BitVec 64) : x.msb = x.getLsbD 63 := by
  simp [BitVec.msb_eq_getLsbD_last]

theorem addCarry_eq_spec (x y : BitVec 64) :
    addCarry x y = decide (2 ^ 64 ≤ x.toNat + y.toNat) := by
  have hc : decide (2 ^ 64 ≤ x.toNat + y.toNat) = BitVec.carry 64 x y false := by
    simp [BitVec.carry_width]
  rw [hc, BitVec.carry_succ]
  simp only [addCarry, msb_eq_bit63, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_add (by decide : 63 < 64)]
  cases x.getLsbD 63 <;> cases y.getLsbD 63 <;> cases BitVec.carry 63 x y false <;> decide

theorem addAdjust_eq_spec (x y : BitVec 64) :
    addAdjust x y = decide (16 ≤ x.toNat % 16 + y.toNat % 16) := by
  simp only [addAdjust, BitVec.getLsbD_xor, BitVec.getLsbD_add (by decide : 4 < 64)]
  have : BitVec.carry 4 x y false = decide (16 ≤ x.toNat % 16 + y.toNat % 16) := by
    simp [BitVec.carry]
  rw [this]
  cases x.getLsbD 4 <;> cases y.getLsbD 4 <;> simp

theorem addOverflow_eq_spec (x y : BitVec 64) :
    addOverflow x y = decide (x.toInt + y.toInt < -2 ^ 63 ∨ 2 ^ 63 ≤ x.toInt + y.toInt) := by
  have h := BitVec.saddOverflow_eq x y
  simp only [BitVec.saddOverflow] at h
  have hs : decide (x.toInt + y.toInt < -2 ^ 63 ∨ 2 ^ 63 ≤ x.toInt + y.toInt) =
      (decide (x.toInt + y.toInt ≥ 2 ^ (64 - 1)) || decide (x.toInt + y.toInt < -2 ^ (64 - 1))) := by
    simp [or_comm]
  rw [hs, h]
  simp only [addOverflow, BitVec.msb_and, BitVec.msb_xor]
  cases x.msb <;> cases y.msb <;> cases (x + y).msb <;> decide

/-- Subtraction as an addition with carry-in: `x - y = x + ~~~y + 1`. -/
private theorem sub_eq_add_not_add_one (x y : BitVec 64) :
    x - y = x + ~~~y + BitVec.setWidth 64 (BitVec.ofBool true) := by
  rw [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]
  rfl

private theorem getLsbD_sub' {i : Nat} (hi : i < 64) (x y : BitVec 64) :
    (x - y).getLsbD i = (x.getLsbD i ^^ (!y.getLsbD i ^^ BitVec.carry i x (~~~y) true)) := by
  rw [sub_eq_add_not_add_one, BitVec.getLsbD_add_add_bool hi]
  simp [hi]

theorem subBorrow_eq_spec (x y : BitVec 64) :
    subBorrow x y = decide (x.toNat < y.toNat) := by
  have hc : decide (x.toNat < y.toNat) = !BitVec.carry 64 x (~~~y) true := by
    have hy := y.isLt
    simp only [BitVec.carry, BitVec.toNat_not, Bool.toNat_true]
    rw [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt (by omega)]
    simp only [decide_eq_decide, ← decide_not]
    omega
  rw [hc, BitVec.carry_succ]
  simp only [subBorrow, msb_eq_bit63, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_xor, getLsbD_sub' (by decide : 63 < 64)]
  cases x.getLsbD 63 <;> cases y.getLsbD 63 <;> cases BitVec.carry 63 x (~~~y) true <;> decide

theorem subAdjust_eq_spec (x y : BitVec 64) :
    subAdjust x y = decide (x.toNat % 16 < y.toNat % 16) := by
  simp only [subAdjust, BitVec.getLsbD_xor, getLsbD_sub' (by decide : 4 < 64)]
  have : BitVec.carry 4 x (~~~y) true = !decide (x.toNat % 16 < y.toNat % 16) := by
    have hy := y.isLt
    simp only [BitVec.carry, BitVec.toNat_not, Bool.toNat_true, ← decide_not]
    simp only [decide_eq_decide]
    omega
  rw [this]
  cases x.getLsbD 4 <;> cases y.getLsbD 4 <;> simp

theorem subOverflow_eq_spec (x y : BitVec 64) :
    subOverflow x y = decide (x.toInt - y.toInt < -2 ^ 63 ∨ 2 ^ 63 ≤ x.toInt - y.toInt) := by
  have h := BitVec.ssubOverflow_eq x y
  simp only [BitVec.ssubOverflow] at h
  have hs : decide (x.toInt - y.toInt < -2 ^ 63 ∨ 2 ^ 63 ≤ x.toInt - y.toInt) =
      (decide (x.toInt - y.toInt ≥ 2 ^ (64 - 1)) || decide (x.toInt - y.toInt < -2 ^ (64 - 1))) := by
    simp [or_comm]
  rw [hs, h]
  simp only [subOverflow, BitVec.msb_and, BitVec.msb_xor]
  cases x.msb <;> cases y.msb <;> cases (x - y).msb <;> decide

/-- The flags of ADD agree with the arithmetic specification. -/
theorem addFlags_eq_spec (x y : BitVec 64) : addFlags x y = Spec.addFlags x y := by
  simp only [addFlags, Spec.addFlags, addCarry_eq_spec, addAdjust_eq_spec, addOverflow_eq_spec,
    parity_eq_spec, isZero_eq_spec, sign_eq_toNat, BitVec.toNat_add, Spec.parity,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 8 ∣ 2 ^ 64)]

private theorem toNat_sub' (x y : BitVec 64) :
    (x - y).toNat = (x.toNat + (2 ^ 64 - y.toNat)) % 2 ^ 64 := by
  rw [BitVec.toNat_sub]; omega

/-- The flags of SUB and CMP agree with the arithmetic specification. -/
theorem subFlags_eq_spec (x y : BitVec 64) : subFlags x y = Spec.subFlags x y := by
  have hz : isZero (x - y) = decide (x.toNat = y.toNat) := by
    have := x.isLt
    have := y.isLt
    rw [isZero_eq_spec, toNat_sub']
    simp only [decide_eq_decide]
    omega
  simp only [subFlags, Spec.subFlags, subBorrow_eq_spec, subAdjust_eq_spec, subOverflow_eq_spec,
    parity_eq_spec, hz, sign_eq_toNat, toNat_sub', Spec.parity,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 8 ∣ 2 ^ 64)]

/-- NEG's flags are those of `0 - x`: in particular CF is the borrow of `0 - x`. -/
theorem negFlags_eq_subFlags (x : BitVec 64) : negFlags x = subFlags 0#64 x := by
  have : (x != 0#64) = subBorrow 0#64 x := by
    have hz := isZero_eq_spec x
    rw [subBorrow_eq_spec]
    show (!(x == 0#64)) = _
    simp only [isZero] at hz
    rw [hz]
    simp [Nat.pos_iff_ne_zero]
  simp [negFlags, subFlags, this]

/-- The flags of NEG agree with the arithmetic specification. -/
theorem negFlags_eq_spec (x : BitVec 64) : negFlags x = Spec.negFlags x := by
  rw [negFlags_eq_subFlags, subFlags_eq_spec]
  have hx := x.isLt
  have hmin := BitVec.le_toInt x
  have hmax := BitVec.toInt_lt (x := x)
  simp only [Spec.subFlags, Spec.negFlags, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_add,
    BitVec.toInt_zero, Nat.lt_iff_add_one_le, Flags.mk.injEq, Option.some.injEq]
  push_cast at hmin hmax
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [decide_eq_decide, Int.reducePow, Int.reduceNeg, true_and] <;> omega

/-- The flags of AND, OR and XOR agree with the arithmetic specification. -/
theorem logicFlags_eq_spec (r : BitVec 64) : logicFlags r = Spec.logicFlags r := by
  simp [logicFlags, Spec.logicFlags, parity_eq_spec, isZero_eq_spec, sign_eq_toNat]

end Silmaril.X86
