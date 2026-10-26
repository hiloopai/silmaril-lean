module

public import Silmaril.X86.Ext.Syntax

/-!
# Width-generic status flags and condition codes

The flag formulas of `X86/Flags.lean` restated for any operand width, so that
the same definitions serve 32-bit and 64-bit operations. At width 64 they are
definitionally the formulas of the existing model (`addFlagsN_eq`,
`subFlagsN_eq`, `negFlagsN_eq`, `logicFlagsN_eq`).

Flags added here, following the Intel SDM instruction reference:

* IMUL (two-operand form): CF and OF are set exactly when the signed product
  does not fit in the destination; SF, ZF, AF and PF are undefined.
* MUL: CF and OF indicate a nonzero upper product half; SF, ZF, AF and PF
  are undefined.
* SHL/SHR/SAR by a nonzero masked count `c`: CF is the last bit shifted out, SF,
  ZF and PF follow the result, AF is undefined, and OF is defined only for
  `c = 1` (SHL: MSB of the result XOR CF; SHR: MSB of the operand; SAR: 0).
* ROL/ROR by a nonzero masked count: CF is the bit rotated into the result's
  LSB (ROL) or MSB (ROR), OF is defined only for `c = 1` (ROL: MSB XOR CF; ROR:
  XOR of the two most significant bits), and SF, ZF, AF, PF are unchanged.
* A masked count of zero leaves all flags unchanged.
* DIV/IDIV leave all six flags undefined.
* LZCNT/TZCNT: CF is set iff the source is zero, ZF iff the count is zero, and
  OF, SF, PF, AF are undefined. POPCNT clears all flags except ZF, which is set
  iff the source is zero.

## Condition codes

`Cond.holds` is the SDM definition of the sixteen conditions over concrete
flags. `Cond.eval` evaluates a condition over model flags in three-valued
(Kleene) logic: it is `none` when the outcome depends on an undefined flag, and
it never replaces an undefined flag by a constant. `Cond.eval_sound` shows that
a defined outcome is the outcome for every concrete flag register the model
flags admit.

`eval_subFlagsN` gives the meaning of every condition after CMP (for example
`l` is signed less-than and `b` unsigned less-than), and
`eval_logicFlagsN_isSome` shows that every condition is defined after TEST. Both
hold at every nonzero width.

This is a handwritten local model; it is not derived from, or proved to
correspond with, the Sail, ACL2 or any hardware description.
-/

@[expose] public section

namespace Silmaril.X86.Ext

open Silmaril.X86 (Flags ConcreteFlags)

/-! ## Flag formulas at any width -/

section Formulas

variable {n : Nat}

def parityN (r : BitVec n) : Bool :=
  !(r.getLsbD 0 ^^ r.getLsbD 1 ^^ r.getLsbD 2 ^^ r.getLsbD 3 ^^
    r.getLsbD 4 ^^ r.getLsbD 5 ^^ r.getLsbD 6 ^^ r.getLsbD 7)

def isZeroN (r : BitVec n) : Bool := r == 0#n

def addCarryN (x y : BitVec n) : Bool := ((x &&& y) ||| ((x ||| y) &&& ~~~(x + y))).msb
def addOverflowN (x y : BitVec n) : Bool := ((x ^^^ (x + y)) &&& (y ^^^ (x + y))).msb
def addAdjustN (x y : BitVec n) : Bool := (x ^^^ y ^^^ (x + y)).getLsbD 4
def subBorrowN (x y : BitVec n) : Bool := ((~~~x &&& y) ||| (~~~(x ^^^ y) &&& (x - y))).msb
def subOverflowN (x y : BitVec n) : Bool := ((x ^^^ y) &&& (x ^^^ (x - y))).msb
def subAdjustN (x y : BitVec n) : Bool := (x ^^^ y ^^^ (x - y)).getLsbD 4

def addFlagsN (x y : BitVec n) : Flags where
  carry := some (addCarryN x y)
  parity := some (parityN (x + y))
  adjust := some (addAdjustN x y)
  zero := some (isZeroN (x + y))
  sign := some (x + y).msb
  overflow := some (addOverflowN x y)

def subFlagsN (x y : BitVec n) : Flags where
  carry := some (subBorrowN x y)
  parity := some (parityN (x - y))
  adjust := some (subAdjustN x y)
  zero := some (isZeroN (x - y))
  sign := some (x - y).msb
  overflow := some (subOverflowN x y)

def negFlagsN (x : BitVec n) : Flags where
  carry := some (x != 0#n)
  parity := some (parityN (0#n - x))
  adjust := some (subAdjustN 0#n x)
  zero := some (isZeroN (0#n - x))
  sign := some (0#n - x).msb
  overflow := some (subOverflowN 0#n x)

/-- The flags of `inc`: those of adding one, except that CF is unchanged
(Intel SDM, Vol. 2, INC: "The CF flag is not affected"). -/
def incFlagsN (x : BitVec n) (old : Flags) : Flags :=
  { addFlagsN x 1#n with carry := old.carry }

/-- The flags of `dec`: those of subtracting one, with CF unchanged. -/
def decFlagsN (x : BitVec n) (old : Flags) : Flags :=
  { subFlagsN x 1#n with carry := old.carry }

/-- The byte reversal of BSWAP. -/
def byteSwap32 (v : BitVec 32) : BitVec 32 :=
  ((v.extractLsb' 0 8 ++ v.extractLsb' 8 8) ++ v.extractLsb' 16 8) ++ v.extractLsb' 24 8

/-- The byte reversal of BSWAP at 64 bits. -/
def byteSwap64 (v : BitVec 64) : BitVec 64 :=
  byteSwap32 (v.extractLsb' 0 32) ++ byteSwap32 (v.extractLsb' 32 32)

def logicFlagsN (r : BitVec n) : Flags where
  carry := some false
  parity := some (parityN r)
  adjust := none
  zero := some (isZeroN r)
  sign := some r.msb
  overflow := some false

/-- The signed product of `x` and `y` does not fit in `n` bits. -/
def imulOverflow (x y : BitVec n) : Bool := decide ((x * y).toInt ≠ x.toInt * y.toInt)

/-- IMUL (two-operand form). -/
def imulFlags (x y : BitVec n) : Flags where
  carry := some (imulOverflow x y)
  parity := none
  adjust := none
  zero := none
  sign := none
  overflow := some (imulOverflow x y)

/-- DIV and IDIV: all six flags are undefined. -/
def undefinedFlags : Flags := ⟨none, none, none, none, none, none⟩

/-- Unsigned full-width multiply flags: CF/OF indicate a nonzero upper half. -/
def mulFlags (highNonzero : Bool) : Flags :=
  { undefinedFlags with carry := some highNonzero, overflow := some highNonzero }

end Formulas

/-! ## Bit counts -/

section Counts

variable {n : Nat}

/-- The number of trailing zero bits; `n` for zero. -/
def tzcntN (x : BitVec n) : Nat := ((List.range n).find? fun i => x.getLsbD i).getD n

/-- The number of leading zero bits; `n` for zero. -/
def lzcntN (x : BitVec n) : Nat := ((List.range n).find? fun i => x.getLsbD (n - 1 - i)).getD n

/-- The number of one bits. -/
def popcntN (x : BitVec n) : Nat := (List.range n).countP fun i => x.getLsbD i

def BitCountOp.count : BitCountOp → BitVec n → Nat
  | .lzcnt, x => lzcntN x
  | .tzcnt, x => tzcntN x
  | .popcnt, x => popcntN x

/-- LZCNT and TZCNT set CF when the source is zero and ZF when the count is zero,
leaving OF, SF, PF and AF undefined. POPCNT clears OF, SF, AF, CF and PF and sets
ZF when the source is zero. -/
def BitCountOp.flags : BitCountOp → BitVec n → Flags
  | .popcnt, x => ⟨some false, some false, some false, some (x == 0#n), some false, some false⟩
  | op, x => ⟨some (x == 0#n), none, none, some (op.count x == 0), none, none⟩

end Counts

example : tzcntN (0x8#32) = 3 := by decide
example : lzcntN (0x1#32) = 31 := by decide
example : lzcntN (0x0#64) = 64 := by decide
example : popcntN (0xF0F0#32) = 8 := by decide

/-! ## Agreement with the 64-bit formulas -/

theorem addFlagsN_eq (x y : BitVec 64) : addFlagsN x y = X86.addFlags x y := rfl
theorem subFlagsN_eq (x y : BitVec 64) : subFlagsN x y = X86.subFlags x y := rfl
theorem negFlagsN_eq (x : BitVec 64) : negFlagsN x = X86.negFlags x := rfl
theorem logicFlagsN_eq (r : BitVec 64) : logicFlagsN r = X86.logicFlags r := rfl

/-- The ALU operations at any width; at width 64 these are `AluOp.result` and
`AluOp.flags` (`resultN_eq`, `flagsN_eq`). -/
def AluOp.resultN {n : Nat} : X86.AluOp → BitVec n → BitVec n → BitVec n
  | .add, x, y => x + y
  | .or, x, y => x ||| y
  | .and, x, y => x &&& y
  | .sub, x, y => x - y
  | .xor, x, y => x ^^^ y
  | .cmp, x, y => x - y

def AluOp.flagsN {n : Nat} : X86.AluOp → BitVec n → BitVec n → Flags
  | .add, x, y => addFlagsN x y
  | .sub, x, y => subFlagsN x y
  | .cmp, x, y => subFlagsN x y
  | .or, x, y => logicFlagsN (x ||| y)
  | .and, x, y => logicFlagsN (x &&& y)
  | .xor, x, y => logicFlagsN (x ^^^ y)

theorem AluOp.resultN_eq (op : X86.AluOp) (x y : BitVec 64) : AluOp.resultN op x y = op.result x y := by
  cases op <;> rfl

theorem AluOp.flagsN_eq (op : X86.AluOp) (x y : BitVec 64) : AluOp.flagsN op x y = op.flags x y := by
  cases op <;> rfl

/-! ## Shifts and rotates -/

/-- The result of a shift or rotate by a masked count `c` (`c < n`). -/
def ShiftOp.result {n : Nat} : ShiftOp → BitVec n → Nat → BitVec n
  | .shl, x, c => x <<< c
  | .shr, x, c => x >>> c
  | .sar, x, c => x.sshiftRight c
  | .rol, x, c => x.rotateLeft c
  | .ror, x, c => x.rotateRight c

/-- The flags after a shift or rotate of `x` by the masked count `c`, given the
incoming flags `old`. -/
def ShiftOp.flags {n : Nat} (op : ShiftOp) (x : BitVec n) (c : Nat) (old : Flags) : Flags :=
  if c = 0 then old else
  let r := op.result x c
  match op with
  | .shl =>
    let cf := x.getLsbD (n - c)
    ⟨some cf, some (parityN r), none, some (isZeroN r), some r.msb,
      if c = 1 then some (r.msb ^^ cf) else none⟩
  | .shr =>
    ⟨some (x.getLsbD (c - 1)), some (parityN r), none, some (isZeroN r), some r.msb,
      if c = 1 then some x.msb else none⟩
  | .sar =>
    ⟨some (x.getLsbD (c - 1)), some (parityN r), none, some (isZeroN r), some r.msb,
      if c = 1 then some false else none⟩
  | .rol =>
    { old with
      carry := some (r.getLsbD 0)
      overflow := if c = 1 then some (r.msb ^^ r.getLsbD 0) else none }
  | .ror =>
    { old with
      carry := some r.msb
      overflow := if c = 1 then some (r.msb ^^ r.getLsbD (n - 2)) else none }

theorem ShiftOp.flags_zero {n : Nat} (op : ShiftOp) (x : BitVec n) (old : Flags) :
    op.flags x 0 old = old := by
  simp [ShiftOp.flags]

/-- For a masked count above one, OF is undefined for every shift and rotate. -/
theorem ShiftOp.flags_overflow_of_one_lt {n : Nat} (op : ShiftOp) (x : BitVec n) {c : Nat}
    (hc : 1 < c) (old : Flags) : (op.flags x c old).overflow = none := by
  have h0 : c ≠ 0 := by omega
  have h1 : c ≠ 1 := by omega
  cases op <;> simp [ShiftOp.flags, h0, h1]

/-- For a nonzero masked count, CF is the last bit shifted out: bit `n - c` of
the operand for SHL, bit `c - 1` for SHR and SAR. -/
theorem ShiftOp.flags_carry_shift {n : Nat} (x : BitVec n) {c : Nat} (hc : c ≠ 0) (old : Flags) :
    (ShiftOp.shl.flags x c old).carry = some (x.getLsbD (n - c)) ∧
      (ShiftOp.shr.flags x c old).carry = some (x.getLsbD (c - 1)) ∧
      (ShiftOp.sar.flags x c old).carry = some (x.getLsbD (c - 1)) := by
  simp [ShiftOp.flags, hc]

/-- Masking an 8-bit count to six bits (`& 3FH`) is reduction modulo 64, and to
five bits (`& 1FH`) reduction modulo 32. -/
theorem count_mask (raw : BitVec 8) :
    raw.toNat % 64 = (raw &&& 0x3F#8).toNat ∧ raw.toNat % 32 = (raw &&& 0x1F#8).toNat := by
  revert raw; decide

/-! ## Condition codes -/

/-- Three-valued negation. -/
def kNot : Option Bool → Option Bool := Option.map (!·)

/-- Three-valued disjunction: true as soon as one side is. -/
def kOr : Option Bool → Option Bool → Option Bool
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

/-- Three-valued exclusive or: defined only when both sides are. -/
def kXor : Option Bool → Option Bool → Option Bool
  | some a, some b => some (a ^^ b)
  | _, _ => none

namespace Cond

/-- The SDM definition of each condition over a concrete flag register
(Intel SDM Vol. 1, Appendix B, Table B-1). -/
def holds (f : ConcreteFlags) : Cond → Bool
  | o => f.overflow
  | no => !f.overflow
  | b => f.carry
  | ae => !f.carry
  | e => f.zero
  | ne => !f.zero
  | be => f.carry || f.zero
  | a => !f.carry && !f.zero
  | s => f.sign
  | ns => !f.sign
  | p => f.parity
  | np => !f.parity
  | l => f.sign != f.overflow
  | ge => f.sign == f.overflow
  | le => f.zero || f.sign != f.overflow
  | g => !f.zero && f.sign == f.overflow

/-- A condition over model flags: `none` when it depends on an undefined flag. -/
def eval (f : Flags) : Cond → Option Bool
  | o => f.overflow
  | no => kNot f.overflow
  | b => f.carry
  | ae => kNot f.carry
  | e => f.zero
  | ne => kNot f.zero
  | be => kOr f.carry f.zero
  | a => kNot (kOr f.carry f.zero)
  | s => f.sign
  | ns => kNot f.sign
  | p => f.parity
  | np => kNot f.parity
  | l => kXor f.sign f.overflow
  | ge => kNot (kXor f.sign f.overflow)
  | le => kOr f.zero (kXor f.sign f.overflow)
  | g => kNot (kOr f.zero (kXor f.sign f.overflow))

/-- A defined outcome is the SDM outcome for every concrete flag register the
model flags admit. -/
theorem eval_sound {f : Flags} {cf : ConcreteFlags} (h : f.Admits cf) {c : Cond} {v : Bool}
    (he : c.eval f = some v) : c.holds cf = v := by
  obtain ⟨fc, fp, fa, fz, fs, fo⟩ := f
  obtain ⟨cc, cp, ca, cz, cs, co⟩ := cf
  obtain ⟨hc, hp, -, hz, hs, ho⟩ := h
  simp only at hc hp hz hs ho
  cases c <;> simp only [eval, holds] at he ⊢ <;>
    rcases fc with _ | ⟨_ | _⟩ <;> rcases fz with _ | ⟨_ | _⟩ <;>
    rcases fs with _ | ⟨_ | _⟩ <;> rcases fo with _ | ⟨_ | _⟩ <;>
    rcases fp with _ | ⟨_ | _⟩ <;>
    simp_all [kNot, kOr, kXor, X86.FlagValue.Admits]

/-- Every condition is defined when the flags it reads are. -/
theorem eval_isSome {f : Flags} (hc : f.carry.isSome) (hp : f.parity.isSome)
    (hz : f.zero.isSome) (hs : f.sign.isSome) (ho : f.overflow.isSome) (c : Cond) :
    (c.eval f).isSome := by
  obtain ⟨fc, fp, fa, fz, fs, fo⟩ := f
  simp only at hc hp hz hs ho
  obtain ⟨vc, rfl⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨vp, rfl⟩ := Option.isSome_iff_exists.mp hp
  obtain ⟨vz, rfl⟩ := Option.isSome_iff_exists.mp hz
  obtain ⟨vs, rfl⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨vo, rfl⟩ := Option.isSome_iff_exists.mp ho
  cases c <;> cases vc <;> cases vz <;> cases vs <;> cases vo <;> rfl

/-- On fully defined flags, `eval` is the SDM definition. -/
theorem eval_toFlags (cf : ConcreteFlags) (c : Cond) : c.eval cf.toFlags = some (c.holds cf) := by
  obtain ⟨cc, cp, ca, cz, cs, co⟩ := cf
  cases c <;> cases cc <;> cases cz <;> cases cs <;> cases co <;> cases cp <;> rfl

end Cond

/-! ## Conditions after CMP and TEST -/

/-- After TEST (and AND/OR/XOR), whose only undefined flag is AF, every
condition is defined. -/
theorem eval_logicFlagsN_isSome {n : Nat} (r : BitVec n) (c : Cond) :
    (c.eval (logicFlagsN r)).isSome :=
  Cond.eval_isSome rfl rfl rfl rfl rfl c

/-- After CMP (and SUB, ADD), every condition is defined. -/
theorem eval_subFlagsN_isSome {n : Nat} (x y : BitVec n) (c : Cond) :
    (c.eval (subFlagsN x y)).isSome :=
  Cond.eval_isSome rfl rfl rfl rfl rfl c

theorem eval_addFlagsN_isSome {n : Nat} (x y : BitVec n) (c : Cond) :
    (c.eval (addFlagsN x y)).isSome :=
  Cond.eval_isSome rfl rfl rfl rfl rfl c

section Cmp

variable {w : Nat}

private theorem msb_eq_last (x : BitVec (w + 1)) : x.msb = x.getLsbD w := by
  simp [BitVec.msb_eq_getLsbD_last]

private theorem sub_eq_add_not_add_one (x y : BitVec (w + 1)) :
    x - y = x + ~~~y + BitVec.setWidth (w + 1) (BitVec.ofBool true) := by
  rw [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]
  congr 2
  ext i
  simp

private theorem getLsbD_sub' {i : Nat} (hi : i < w + 1) (x y : BitVec (w + 1)) :
    (x - y).getLsbD i = (x.getLsbD i ^^ (!y.getLsbD i ^^ BitVec.carry i x (~~~y) true)) := by
  rw [sub_eq_add_not_add_one, BitVec.getLsbD_add_add_bool hi]
  simp [hi]

theorem subBorrowN_eq (x y : BitVec (w + 1)) : subBorrowN x y = x.ult y := by
  rw [BitVec.ult_eq_not_carry, BitVec.carry_succ]
  simp only [subBorrowN, msb_eq_last, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_xor, getLsbD_sub' (Nat.lt_succ_self w)]
  simp only [Nat.lt_succ_self, decide_true, Bool.true_and]
  cases x.getLsbD w <;> cases y.getLsbD w <;> cases BitVec.carry w x (~~~y) true <;> rfl

private theorem msb_sub' (x y : BitVec (w + 1)) :
    (x - y).msb = (x.msb ^^ (!y.msb ^^ BitVec.carry w x (~~~y) true)) := by
  rw [msb_eq_last, getLsbD_sub' (Nat.lt_succ_self w), msb_eq_last, msb_eq_last]

theorem subOverflowN_eq (x y : BitVec (w + 1)) :
    subOverflowN x y = (x.msb != y.msb && (x - y).msb != x.msb) := by
  simp only [subOverflowN, BitVec.msb_and, BitVec.msb_xor]
  cases x.msb <;> cases y.msb <;> cases (x - y).msb <;> rfl

/-- Signed less-than is `SF ≠ OF` after CMP. -/
theorem slt_eq_sign_xor_overflow (x y : BitVec (w + 1)) :
    x.slt y = ((x - y).msb ^^ subOverflowN x y) := by
  rw [subOverflowN_eq, msb_sub', BitVec.slt_eq_not_carry, BitVec.carry_succ]
  simp only [BitVec.getLsbD_not, msb_eq_last, Nat.lt_succ_self, decide_true, Bool.true_and]
  cases x.getLsbD w <;> cases y.getLsbD w <;> cases BitVec.carry w x (~~~y) true <;> rfl

theorem isZeroN_sub (x y : BitVec (w + 1)) : isZeroN (x - y) = (x == y) := by
  simp only [isZeroN]
  by_cases h : x = y
  · subst h; simp
  · have : x - y ≠ 0#(w + 1) := fun e => by
      have := BitVec.sub_add_cancel x y
      rw [e, BitVec.zero_add] at this
      exact h this.symm
    simp [h, this]

/-- The meaning of each condition after `cmp x, y`. -/
def Cond.afterCmp (x y : BitVec (w + 1)) : Cond → Bool
  | .o => subOverflowN x y
  | .no => !subOverflowN x y
  | .b => x.ult y
  | .ae => !x.ult y
  | .e => x == y
  | .ne => !(x == y)
  | .be => x.ule y
  | .a => !x.ule y
  | .s => (x - y).msb
  | .ns => !(x - y).msb
  | .p => parityN (x - y)
  | .np => !parityN (x - y)
  | .l => x.slt y
  | .ge => !x.slt y
  | .le => x.sle y
  | .g => !x.sle y

/-- Every condition after CMP is defined, and is the corresponding comparison:
`b`/`ae`/`be`/`a` are the unsigned and `l`/`ge`/`le`/`g` the signed orders. -/
theorem eval_subFlagsN (x y : BitVec (w + 1)) (c : Cond) :
    c.eval (subFlagsN x y) = some (c.afterCmp x y) := by
  have hb := subBorrowN_eq x y
  have hz := isZeroN_sub x y
  have hl := slt_eq_sign_xor_overflow x y
  have hule : x.ule y = (x.ult y || x == y) := by
    rw [Bool.eq_iff_iff]
    simp only [BitVec.ule_eq_decide, BitVec.ult_eq_decide, Bool.or_eq_true, decide_eq_true_eq,
      beq_iff_eq]
    constructor
    · intro h
      rcases Nat.lt_or_eq_of_le h with h | h
      · exact .inl h
      · exact .inr (BitVec.eq_of_toNat_eq h)
    · rintro (h | rfl)
      · omega
      · exact le_rfl
  have hsle : x.sle y = (x.slt y || x == y) := BitVec.sle_eq_slt_or_eq
  cases c <;>
    simp only [Cond.eval, Cond.afterCmp, subFlagsN, kNot, kOr, kXor, Option.map_some, hb, hz,
      hl, hule, hsle] <;>
    cases x.ult y <;> cases (x == y) <;> cases (x - y).msb <;> cases subOverflowN x y <;> rfl

end Cmp

end Silmaril.X86.Ext
