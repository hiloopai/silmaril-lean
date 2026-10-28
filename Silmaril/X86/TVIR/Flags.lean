module

public import Silmaril.X86.TVIR.Core
public import Silmaril.X86.SegVC.Tactic
public import Silmaril.X86.Ext8.Lemmas

/-! # TVIR: flag elimination and value normal forms for x86 blocks

Status: **VERIFIED** (no `sorry`, standard axioms only).

A translation-validation coupling never mentions flags: every flag a block sets is consumed
by the `jcc` (or `setcc`) that follows it, and the pair is one IR condition. This file states
that elimination once, as rewrite rules from `Cond.eval` of the flags a `cmp`/`test` leaves to
a Boolean on the operands, and the IR side (`BExp.eval`) to the same Boolean. The rules are
the existing `X86.Ext` facts (`eval_subFlagsN`, `Cond.afterCmp`, `SegVC.eval_logic_*`),
specialised to the conditions compiled code uses, so a block's symbolic execution leaves
`if x == y then … else …` and the TV proof matches it against the IR condition.

**Values.** The width bookkeeping of byte and 32-bit operations (a `movzbl` load is
`setWidth 64 (setWidth 32 (setWidth 8 (leValue [b])))`, an 8-bit shift of a zero-extended
byte, a 32-bit `and`) has normal forms in terms of the zero-extended byte `b.setWidth 64`, the
IR's `zext`.

* `cmp_e`, `cmp_ne`, `cmp_b`, `cmp_ae`, `cmp_a`, `cmp_be` (64-, 32- and 8-bit): fused
  `cmp`/`jcc` → comparison;
* `test_e`, `test_ne`: fused `test r, r`/`jcc` → zero test;
* `BExp.eval_eq`, `BExp.eval_ne`, `BExp.eval_ult`: the IR conditions;
* `movzx_byte`, `zext32_byte`, `zext_byte_lt`: values.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.X86.TVIR

open Silmaril.X86.Ext (Cond subFlagsN logicFlagsN leValue)

/-! ## Fused compare and branch -/

section Cmp
variable {w : Nat} (x y : BitVec (w + 1))

theorem cmp_e : Cond.e.eval (subFlagsN x y) = some (x == y) :=
  Silmaril.X86.Ext.eval_subFlagsN x y .e
theorem cmp_ne : Cond.ne.eval (subFlagsN x y) = some (!(x == y)) :=
  Silmaril.X86.Ext.eval_subFlagsN x y .ne
theorem cmp_b : Cond.b.eval (subFlagsN x y) = some (x.ult y) :=
  Silmaril.X86.Ext.eval_subFlagsN x y .b
theorem cmp_ae : Cond.ae.eval (subFlagsN x y) = some (!x.ult y) :=
  Silmaril.X86.Ext.eval_subFlagsN x y .ae
theorem cmp_be : Cond.be.eval (subFlagsN x y) = some (x.ule y) :=
  Silmaril.X86.Ext.eval_subFlagsN x y .be
theorem cmp_a : Cond.a.eval (subFlagsN x y) = some (!x.ule y) :=
  Silmaril.X86.Ext.eval_subFlagsN x y .a

end Cmp

/-- `cmp` at 64 bits (the operand width as a literal, as `x86_simp` leaves it). -/
theorem cmp64 (x y : BitVec 64) (c : Cond) :
    c.eval (subFlagsN x y) = some (Cond.afterCmp (w := 63) x y c) :=
  Silmaril.X86.SegVC.eval_sub_64 x y c

/-- `cmp` at 32 bits. -/
theorem cmp32 (x y : BitVec 32) (c : Cond) :
    c.eval (subFlagsN x y) = some (Cond.afterCmp (w := 31) x y c) :=
  Silmaril.X86.SegVC.eval_sub_32 x y c

/-- `cmp` at 8 bits. -/
theorem cmp8 (x y : BitVec 8) (c : Cond) :
    c.eval (subFlagsN x y) = some (Cond.afterCmp (w := 7) x y c) :=
  Silmaril.X86.SegVC.eval_sub_8 x y c

/-- `test r, r` then `je`: `r = 0`. -/
theorem test_e {w : Nat} (r : BitVec w) : Cond.e.eval (logicFlagsN r) = some (r == 0#w) :=
  Silmaril.X86.SegVC.eval_logic_e r

/-- `test r, r` then `jne`: `r ≠ 0`. -/
theorem test_ne {w : Nat} (r : BitVec w) : Cond.ne.eval (logicFlagsN r) = some (!(r == 0#w)) :=
  Silmaril.X86.SegVC.eval_logic_ne r

/-! ## The IR side -/

section IR
variable {V : Type} (ro : Nat → UInt8) (env : V → Word) (a b : Exp V)

@[simp] theorem BExp.eval_eq : (BExp.eq a b).eval ro env = (a.eval ro env == b.eval ro env) := rfl
@[simp] theorem BExp.eval_ne : (BExp.ne a b).eval ro env = !(a.eval ro env == b.eval ro env) := rfl
@[simp] theorem BExp.eval_ult :
    (BExp.ult a b).eval ro env = decide ((a.eval ro env).toNat < (b.eval ro env).toNat) := rfl

end IR

/-- A fused `cmp a, b`/`je` decides the IR condition `b != a` (the `jne` arm continues). -/
theorem cmp_e_bexp_ne {V : Type} (ro : Nat → UInt8) (env : V → Word) (p q : Exp V) :
    Cond.afterCmp (w := 63) (q.eval ro env) (p.eval ro env) .e =
      !((BExp.ne p q).eval ro env) := by
  simp only [Cond.afterCmp, BExp.eval_ne, Bool.not_not]
  exact Bool.beq_comm

/-! ## Values -/

/-- A `movzbl` load: the byte zero-extended. -/
theorem movzx_byte (x : BitVec 8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.ofNat 64 (leValue [x])))) =
      x.setWidth 64 := by
  have := x.isLt
  apply BitVec.eq_of_toNat_eq
  simp [leValue, BitVec.toNat_setWidth]

/-- A 32-bit move of a zero-extended byte. -/
theorem zext32_byte (x : BitVec 8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (x.setWidth 64)) = x.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp [BitVec.toNat_setWidth]

/-- A zero-extended byte is below 256. -/
theorem zext_byte_lt (x : BitVec 8) : (x.setWidth 64).toNat < 256 := by
  have := x.isLt; simp [BitVec.toNat_setWidth]; omega

end Silmaril.X86.TVIR
