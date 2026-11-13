module

public import Silmaril.Compiler.Native.Correctness.LiteralEmission.Defs
import Silmaril.Prelude.BVDecide.Defs
/-! Universal reduction of the real O0 lowering/SSA/ABI/emission path. Local
cbv rules are proved equations for actual integer extraction and word bits;
private opaque aliases retain symbolic input during the reduction. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.LiteralEmission
open Silmaril.Cerberus
open Silmaril.Compiler.Native
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 2000000

private theorem decimalDigits (n : Nat) :
    Nat.toDigits 10 n = if n < 10 then [n.digitChar]
      else Nat.toDigits 10 (n / 10) ++ [(n % 10).digitChar] :=
  Nat.toDigits_eq_ite (by decide)
attribute [local cbv_eval] decimalDigits Nat.repr_eq_ofList_toDigits Nat.toString_eq_ofList_toDigits Int.repr_eq_ite
private theorem decimalDigit0 : Nat.digitChar 0 = '0' :=
  Nat.digitChar_eq_zero.mpr rfl
attribute [local cbv_eval] decimalDigit0
private theorem decimalDigit1 : Nat.digitChar 1 = '1' :=
  Nat.digitChar_eq_one.mpr rfl
attribute [local cbv_eval] decimalDigit1
private theorem decimalDigit2 : Nat.digitChar 2 = '2' :=
  Nat.digitChar_eq_two.mpr rfl
attribute [local cbv_eval] decimalDigit2
private theorem decimalDigit3 : Nat.digitChar 3 = '3' :=
  Nat.digitChar_eq_three.mpr rfl
attribute [local cbv_eval] decimalDigit3
private theorem decimalDigit4 : Nat.digitChar 4 = '4' :=
  Nat.digitChar_eq_four.mpr rfl
attribute [local cbv_eval] decimalDigit4
private theorem decimalDigit5 : Nat.digitChar 5 = '5' :=
  Nat.digitChar_eq_five.mpr rfl
attribute [local cbv_eval] decimalDigit5
private theorem decimalDigit6 : Nat.digitChar 6 = '6' :=
  Nat.digitChar_eq_six.mpr rfl
attribute [local cbv_eval] decimalDigit6
private theorem decimalDigit7 : Nat.digitChar 7 = '7' :=
  Nat.digitChar_eq_seven.mpr rfl
attribute [local cbv_eval] decimalDigit7
private theorem decimalDigit8 : Nat.digitChar 8 = '8' :=
  Nat.digitChar_eq_eight.mpr rfl
attribute [local cbv_eval] decimalDigit8
private theorem decimalDigit9 : Nat.digitChar 9 = '9' :=
  Nat.digitChar_eq_nine.mpr rfl
attribute [local cbv_eval] decimalDigit9


private def Bounded := { number : Int // IsInt32 number }

private def signedValue (number : Bounded) : Int := number.val
attribute [local cbv_opaque] signedValue

private def word (number : Bounded) : Silmaril.X86.Word := BitVec.ofInt 64 (signedValue number)
attribute [local cbv_opaque] word

private theorem word_bits (number : Bounded) :
    BitVec.ofInt 64 (signedValue number) = word number := rfl
attribute [local cbv_eval] word_bits

private theorem value (number : Bounded) :
    Silmaril.Compiler.Native.Types.integerConstantValue
      (.iconstant (signedValue number) .decimal none) = .ok (signedValue number) := by
  change Silmaril.Compiler.Native.Types.integerConstantValue (.iconstant number.val .decimal none) = .ok number.val
  have lower : -(2147483648 : Int) ≤ number.val := number.property.1
  have upper : number.val < (2147483648 : Int) := number.property.2
  simp [Silmaril.Compiler.Native.Types.integerConstantValue,
    Silmaril.Compiler.Native.Types.constantIntegerLayout,
    Silmaril.Compile.C.constantType, lower, upper]
  rfl
attribute [local cbv_opaque] Silmaril.Compiler.Native.Types.integerConstantValue
attribute [local cbv_eval] value


private theorem rawAppend_assoc (a b c : String) :
    (a.append b).append c = a.append (b.append c) := String.append_assoc

attribute [local cbv_opaque] String.append

private theorem compile_bounded (number : Bounded) :
    Driver.compile {opt := some .O0} "literal-linkage" (literal (signedValue number)).program =
      .ok (assembly (word number)) := by
  cbv
  simp only [rawAppend_assoc]
  simp only [String.append]
  cbv


/-- The actual compiler emits this template for every independently bounded
signed32 literal. No successful compile, desired text or execution is assumed. -/
theorem compile_O0 (number : Int) (bounded : IsInt32 number) :
    Driver.compile {opt := some .O0} "literal-linkage" (literal number).program =
      .ok (assembly (BitVec.ofInt 64 number)) :=
  compile_bounded ⟨number, bounded⟩

/-- The same input bounds justify the immediate's signed32 representation. -/
theorem word_signed (number : Int) (bounded : IsInt32 number) :
    (BitVec.ofInt 32 number).signExtend 64 = BitVec.ofInt 64 number := by
  rw [BitVec.signExtend,
    BitVec.toInt_ofInt_eq_self (by decide : 0 < 32) bounded.1 bounded.2]


private theorem narrow_signed (value : BitVec 32) :
    (value.signExtend 64).setWidth 32 = value := by
  bv_decide_kernel

/-- Each independently bounded literal is already the value produced by either
of the emitted signed32 normalizations. -/
theorem word_normalized (number : Int) (bounded : IsInt32 number) :
    ((BitVec.ofInt 64 number).setWidth 32).signExtend 64 = BitVec.ofInt 64 number := by
  rw [← word_signed number bounded, narrow_signed]

/-- The native process projection agrees with the integer's modulo256 status. -/
theorem word_status (number : Int) :
    (BitVec.ofInt 64 number).toNat % 256 = (number % 256).toNat := by
  rw [BitVec.toNat_ofInt]
  omega

end Silmaril.Compiler.Native.Correctness.LiteralEmission
