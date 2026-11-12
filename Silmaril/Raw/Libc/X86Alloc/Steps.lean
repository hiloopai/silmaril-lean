module

public import Silmaril.Raw.Libc.X86Alloc.Frame

/-!
# Proofs: conditions after `cmp`/`test`, and `ret` at a known stack pointer
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Steps

open Silmaril.X86 (Word Byte Reg Flags Insn)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.Raw.Libc.X86Alloc.Frame

variable {σ : Type} {I : Isa σ}

/-- `jb` after `cmp y, x`: taken iff `x < y` unsigned. -/
theorem eval_b_cmp (x y : Word) :
    Silmaril.X86.Ext.Cond.b.eval (Silmaril.X86.Ext.AluOp.flagsN .cmp x y) =
      some (decide (x.toNat < y.toNat)) := by
  simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.subFlagsN,
    Silmaril.X86.Ext.subBorrowN_eq, BitVec.ult]

/-- `ja` after `cmp y, x`: taken iff `y < x` unsigned. -/
theorem eval_a_cmp (x y : Word) :
    Silmaril.X86.Ext.Cond.a.eval (Silmaril.X86.Ext.AluOp.flagsN .cmp x y) =
      some (decide (y.toNat < x.toNat)) := by
  simp only [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.subFlagsN,
    Silmaril.X86.Ext.subBorrowN_eq, BitVec.ult, Silmaril.X86.Ext.isZeroN]
  simp only [Silmaril.X86.Ext.kNot, Silmaril.X86.Ext.kOr, Option.some.injEq]
  by_cases h : x = y
  · subst h; simp
  · have : (x - y == 0#64) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro e; exact h (by have := congrArg (· + y) e; simpa using this)
    rw [this]
    have hne : x.toNat ≠ y.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    by_cases hl : x.toNat < y.toNat
    · simp [hl]; omega
    · simp [hl]; omega

/-- `je` after `test r, r`: taken iff `r = 0`. -/
theorem eval_e_test (x : Word) :
    Silmaril.X86.Ext.Cond.e.eval (Silmaril.X86.Ext.logicFlagsN (x &&& x)) = some (x == 0) := by
  simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.isZeroN]


/-- `x &&& (2^64 - 16)` clears the low four bits. -/
theorem nat_and_mask16 (x : Nat) (hx : x < 2 ^ 64) : x &&& (2 ^ 64 - 16) = x / 16 * 16 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have h16 : (2 ^ 64 - 16 : Nat) = (2 ^ 60 - 1) * 2 ^ 4 := by decide
  have h16' : x / 16 * 16 = x / 2 ^ 4 * 2 ^ 4 := rfl
  rw [h16, h16', Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases hi : 4 ≤ i
  · simp only [hi, decide_true, Bool.true_and]
    rw [Nat.sub_add_cancel hi]
    by_cases h64 : i < 64
    · simp [show i - 4 < 60 by omega]
    · have : x.testBit i = false := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [this]
  · simp [hi]

/-- `and $0xfffffffffffffff0` (the sign-extended `imm8` `0xf0`) rounds down to 16. -/
theorem toNat_and_neg16 (x : Word) :
    (x &&& BitVec.signExtend 64 (0xf0#8)).toNat = x.toNat / 16 * 16 := by
  rw [BitVec.toNat_and, show (BitVec.signExtend 64 (0xf0#8)).toNat = 2 ^ 64 - 16 by decide]
  exact nat_and_mask16 _ x.isLt

/-- `ret` with the return slot at a known stack pointer. -/
theorem c_retAt (E : Silmaril.X86.Open.isa.Extends I) {b : Nat} {code : List Byte} {o k : Nat}
    {pc : Word} (hpc : pc.toNat = b + o) (hfit : o + k ≤ code.length) {f : Reg → Word}
    {fl : Flags} {s ret : Word} {M : SProp} (hs : f .rsp = s)
    (hcode : (code.drop o).take k = Insn.encode .ret) :
    SPEC I (codePt b code) (St pc f fl (wordPt s.toNat ret ∗ M))
      (St ret (Function.update f .rsp (s + 8#64)) fl (wordPt s.toNat ret ∗ M)) := by
  subst hs; exact c_ret E hpc hfit hcode

end Silmaril.Raw.Libc.X86Alloc.Steps

namespace Silmaril.Raw.Libc.X86Alloc.Steps

open Silmaril.X86 (Word Byte Reg Flags)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.Raw.Libc.X86Alloc.Frame

variable {σ : Type} {I : Isa σ}

/-- Re-arrange the memory part. -/
theorem SPEC.mem {C : SProp} {pc : Word} {f : Reg → Word} {fl : Flags} {M M' Q : SProp}
    (h : M = M') (k : SPEC I C (St pc f fl M') Q) : SPEC I C (St pc f fl M) Q := h ▸ k

/-- A pure fact in the memory part. -/
theorem St_pure (pc : Word) (f : Reg → Word) (fl : Flags) (φ : Prop) (A B : SProp) :
    St pc f fl (A ∗ (⌜φ⌝ ∗ B)) = (⌜φ⌝ ∗ St pc f fl (A ∗ B)) := by
  simp only [St]; ac_rfl

end Silmaril.Raw.Libc.X86Alloc.Steps

namespace Silmaril.Raw.Libc.X86Alloc.Steps

open Silmaril.X86 (Word Byte Reg Flags)
open Silmaril.X86.Sep
open Silmaril.Raw.Libc.X86Alloc.Frame

/-- An existential in the memory part. -/
theorem St_ex {α : Sort _} (pc : Word) (f : Reg → Word) (fl : Flags) (A : SProp)
    (P : α → SProp) :
    St pc f fl (A ∗ sexists P) = sexists fun x => St pc f fl (A ∗ P x) := by
  simp only [St, sep_sexists]

end Silmaril.Raw.Libc.X86Alloc.Steps

namespace Silmaril.Raw.Libc.X86Alloc.Steps

open Silmaril.X86 (Word Byte Reg Flags)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.Raw.Libc.X86Alloc.Frame

variable {σ : Type} {I : Isa σ}

/-- Weaken the memory part of the precondition. -/
theorem SPEC.memPre {C : SProp} {pc : Word} {f : Reg → Word} {fl : Flags} {M M' Q : SProp}
    (h : M ⊢ₛ M') (k : SPEC I C (St pc f fl M') Q) : SPEC I C (St pc f fl M) Q :=
  SPEC.conseq (sep_mono_right _ (sep_mono_right _ (sep_mono_right _ h))) k (entails_refl _)

end Silmaril.Raw.Libc.X86Alloc.Steps

namespace Silmaril.Raw.Libc.X86Alloc.Steps

open Silmaril.X86 (Word)

/-- `je` after `cmp y, x`: taken iff `x = y`. -/
theorem eval_e_cmp (x y : Word) :
    Silmaril.X86.Ext.Cond.e.eval (Silmaril.X86.Ext.AluOp.flagsN .cmp x y) = some (decide (x = y)) := by
  simp only [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.subFlagsN,
    Silmaril.X86.Ext.isZeroN, Option.some.injEq]
  by_cases h : x = y
  · subst h; simp
  · have : (x - y == 0#64) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro e; exact h (by have := congrArg (· + y) e; simpa using this)
    rw [this]; simp [h]

end Silmaril.Raw.Libc.X86Alloc.Steps

namespace Silmaril.Raw.Libc.X86Alloc.Steps

open Silmaril.X86 (Word)

/-- `jae` after `cmp y, x`: taken iff `y ≤ x` unsigned. -/
theorem eval_ae_cmp (x y : Word) :
    Silmaril.X86.Ext.Cond.ae.eval (Silmaril.X86.Ext.AluOp.flagsN .cmp x y) =
      some (decide (y.toNat ≤ x.toNat)) := by
  simp only [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.subFlagsN,
    Silmaril.X86.Ext.subBorrowN_eq, BitVec.ult, Silmaril.X86.Ext.kNot, Option.some.injEq]
  by_cases h : x.toNat < y.toNat
  · simp [h]
  · simp [h]; omega

end Silmaril.Raw.Libc.X86Alloc.Steps
