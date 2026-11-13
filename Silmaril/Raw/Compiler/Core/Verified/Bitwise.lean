module

public import Silmaril.Compiler.Core.Verified.Guard.Defs

/-! # Cerberus's bitwise `int` operators `&`, `|`, `^`

Cerberus elaborates `e₁ & e₂` (and `|`, `^`) on `int` operands to the `unseq` of the operands
bound to a tuple `(a, b)`, followed by the pure guard

```
case (a, b) of
| (Specified(x), Specified(y)) => Specified(ivand(int, conv_int(int, x), conv_int(int, y)))
| _ => Unspecified(int)
```

(`ivor`, `ivxor` for `|`, `^`). No arm is undefined. `guard file a b p = some o` recognises
the guard syntactically; `guard_eval`: with `int` operands `Specified n₁`, `Specified n₂` bound
to `a` and `b` it evaluates to `Specified (o.apply n₁ n₂)`, the unbounded two's-complement
operation (`Int.land`, `Int.lor`, `Int.xor`), which is again an `int` (`apply_int`).

On 64-bit words the Lir `and`, `or`, `xor` of the words of two integers are the word of the
integer operation (`ofInt_apply`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Bitwise

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval)
open ConvInt (Pure IsInt)

/-- The bitwise operators. -/
inductive Op where
  | and
  | or
  | xor
  deriving DecidableEq

/-- The value of a bitwise operator (unbounded two's complement). -/
def Op.apply : Op → Int → Int → Int
  | .and, x, y => Int.land x y
  | .or, x, y => Int.lor x y
  | .xor, x, y => Int.xor x y

/-- The operator of a Core constructor. -/
def ofCtor : Ctor → Option Op
  | .ivAnd => some .and
  | .ivOr => some .or
  | .ivXor => some .xor
  | _ => none

/-! ## Range -/

theorem isInt_ofNat {c : Nat} (h : c < 2 ^ 31) : IsInt (Int.ofNat c) :=
  ⟨by simp only [Int.ofNat_eq_natCast]; omega, by simp only [Int.ofNat_eq_natCast]; omega⟩

theorem isInt_negSucc {c : Nat} (h : c < 2 ^ 31) : IsInt (Int.negSucc c) :=
  ⟨by rw [Int.negSucc_eq]; omega, by rw [Int.negSucc_eq]; omega⟩

/-- The bitwise operation of two `int`s is an `int`. -/
theorem apply_int (o : Op) {x y : Int} (hx : IsInt x) (hy : IsInt y) : IsInt (o.apply x y) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  cases x with
  | ofNat a =>
    have ha : a < 2 ^ 31 := by simp only [Int.ofNat_eq_natCast] at hx2; omega
    cases y with
    | ofNat b =>
      have hb : b < 2 ^ 31 := by simp only [Int.ofNat_eq_natCast] at hy2; omega
      cases o
      · exact isInt_ofNat (Nat.and_lt_two_pow _ hb)
      · exact isInt_ofNat (Nat.or_lt_two_pow ha hb)
      · exact isInt_ofNat (Nat.xor_lt_two_pow ha hb)
    | negSucc b =>
      have hb : b < 2 ^ 31 := by rw [Int.negSucc_eq] at hy1; omega
      cases o
      · exact isInt_ofNat (Nat.bitwise_lt_two_pow ha hb)
      · exact isInt_negSucc (Nat.bitwise_lt_two_pow hb ha)
      · exact isInt_negSucc (Nat.xor_lt_two_pow ha hb)
  | negSucc a =>
    have ha : a < 2 ^ 31 := by rw [Int.negSucc_eq] at hx1; omega
    cases y with
    | ofNat b =>
      have hb : b < 2 ^ 31 := by simp only [Int.ofNat_eq_natCast] at hy2; omega
      cases o
      · exact isInt_ofNat (Nat.bitwise_lt_two_pow hb ha)
      · exact isInt_negSucc (Nat.bitwise_lt_two_pow ha hb)
      · exact isInt_negSucc (Nat.xor_lt_two_pow ha hb)
    | negSucc b =>
      have hb : b < 2 ^ 31 := by rw [Int.negSucc_eq] at hy1; omega
      cases o
      · exact isInt_negSucc (Nat.or_lt_two_pow ha hb)
      · exact isInt_negSucc (Nat.and_lt_two_pow _ hb)
      · exact isInt_ofNat (Nat.xor_lt_two_pow ha hb)

/-! ## Words -/

theorem getLsbD_ofInt {w : Nat} (x : Int) {i : Nat} (hi : i < w) :
    (BitVec.ofInt w x).getLsbD i = x.testBit i := by
  cases x with
  | ofNat n =>
    rw [show BitVec.ofInt w (Int.ofNat n) = BitVec.ofNat w n by simp, BitVec.getLsbD_ofNat]
    simp [Int.testBit, hi]
  | negSucc n =>
    rw [BitVec.ofInt_negSucc_eq_not_ofNat, BitVec.getLsbD_not, BitVec.getLsbD_ofNat]
    simp [Int.testBit, hi]

theorem ofInt_land {w : Nat} (x y : Int) :
    BitVec.ofInt w (Int.land x y) = BitVec.ofInt w x &&& BitVec.ofInt w y :=
  BitVec.eq_of_getLsbD_eq fun i hi => by simp [getLsbD_ofInt _ hi, Int.testBit_land]

theorem ofInt_lor {w : Nat} (x y : Int) :
    BitVec.ofInt w (Int.lor x y) = BitVec.ofInt w x ||| BitVec.ofInt w y :=
  BitVec.eq_of_getLsbD_eq fun i hi => by simp [getLsbD_ofInt _ hi, Int.testBit_lor]

theorem ofInt_xor {w : Nat} (x y : Int) :
    BitVec.ofInt w (Int.xor x y) = BitVec.ofInt w x ^^^ BitVec.ofInt w y :=
  BitVec.eq_of_getLsbD_eq fun i hi => by simp [getLsbD_ofInt _ hi, Int.testBit_lxor]

/-! ## The guard -/

/-- The guard of a bitwise `int` operator over the operand tuple `(a, b)`. -/
def guard (file : File Codec.wireModel Unit Unit) (a b : Sym) : Pure → Option Op
  | .mk _ () (.case_ (.mk _ () (.ctor .tuple [.mk _ () (.sym a'), .mk _ () (.sym b')]))
      ((.mk _ (.ctor .tuple [.mk _ (.ctor .specified [.mk _ (.base (some x, _))]),
          .mk _ (.ctor .specified [.mk _ (.base (some y, _))])]),
        .mk _ () (.ctor .specified [.mk _ () (.ctor c
          [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))), p, q])]))
        :: _)) =>
      if decide (a'.key = a.key ∧ b'.key = b.key ∧ b.key ≠ a.key ∧ y.key ≠ x.key) &&
          Guard.convOf file x p && Guard.convOf file y q then ofCtor c else none
  | _ => none

variable {file : Program} {tags : Mem.Concrete.Tags}

theorem ofCtor_primitive {c : Ctor} {o : Op} (hc : ofCtor c = some o) (ann : List Annot)
    (n₁ n₂ : Int) :
    primitive (.ctor c) [runtimeValue (.ctype (.mk ann (.basic (.integer (.signed .int))))),
      .object (.integer n₁), .object (.integer n₂)] tags = .ok (integer (o.apply n₁ n₂)) := by
  cases c <;> simp [ofCtor] at hc <;> subst hc <;> simp [primitive, runtimeValue, intType, Op.apply] <;> rfl

/-- **A bitwise guard** evaluates to `Specified (o.apply n₁ n₂)`. -/
theorem guard_eval {a b : Sym} {p : Pure} {o : Op} (h : guard file a b p = some o)
    (env : Env) {n₁ n₂ : Int} (h₁ : IsInt n₁) (h₂ : IsInt n₂) :
    Eval file tags (Guard.operands a b n₁ n₂ env) (.inl p)
      (.inl (.loaded (.specified (.integer (o.apply n₁ n₂))))) := by
  unfold guard at h
  split at h
  · split at h
    · rename_i cond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
      obtain ⟨⟨⟨e1, e2, ne, ne'⟩, cp⟩, cq⟩ := cond
      refine .case_ (.ctor (.cons (.sym (Guard.lookup_pair_first e1))
        (.cons (.sym (Guard.lookup_pair_second e2 ne)) .nil)) (by simp [primitive]; rfl))
        (by simp [selectCase, matchPattern, matchPatterns]; exact ⟨rfl, rfl⟩) ?_
      refine .ctor (.cons (.ctor (.cons .val (.cons (Guard.convOf_eval cp h₁ (Guard.lookup_pair_first rfl))
        (.cons (Guard.convOf_eval cq h₂ (Guard.lookup_pair_second rfl ne')) .nil)))
        (ofCtor_primitive h _ n₁ n₂)) .nil) (by simp [primitive, integer]; rfl)
    · cases h
  · cases h

end Silmaril.Compile.Core.Verified.Bitwise
