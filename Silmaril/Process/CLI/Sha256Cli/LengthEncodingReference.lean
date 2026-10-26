module

public import Silmaril.Process.CLI.Sha256Cli.LengthStore

/-! # The actual modular length store and canonical SHA bytes -/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.LengthStore

open Silmaril.X86 (Word)
open Silmaril.Machine.LittleEndian (wordByte)

theorem swapped_bytes (value : Word) :
    X86.Ext.leBytes (X86.Ext.byteSwap64 value) 8 =
      [wordByte value 7, wordByte value 6, wordByte value 5, wordByte value 4,
       wordByte value 3, wordByte value 2, wordByte value 1, wordByte value 0] := by
  simp only [X86.Ext.leBytes, List.ofFn_succ, List.ofFn_zero, List.cons.injEq, and_true]
  simp only [Fin.val_zero, Fin.val_succ, Nat.reduceAdd]
  unfold wordByte X86.Ext.byteSwap64 X86.Ext.byteSwap32
  repeat' constructor
  all_goals
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro bit bound
    interval_cases bit <;>
      simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
        Nat.reduceMul, Nat.reduceAdd, Nat.reduceLT, decide_true, Bool.true_and]
    all_goals
      repeat' first
        | (rw [BitVec.getLsbD_append]; simp only [Nat.reduceLT, ite_true, ite_false, Nat.reduceSub])
        | (rw [BitVec.getLsbD_extractLsb'];
            simp only [Nat.reduceLT, decide_true, Bool.true_and, Nat.reduceAdd])

theorem canonical_bytes (value : Word) :
    [wordByte value 7, wordByte value 6, wordByte value 5, wordByte value 4,
     wordByte value 3, wordByte value 2, wordByte value 1, wordByte value 0] =
      (Silmaril.Crypto.natToBytesBE64 value.toNat).map UInt8.toBitVec := by
  simp only [Silmaril.Crypto.natToBytesBE64, Nat.mod_eq_of_lt value.isLt,
    List.map_cons, List.map_nil, List.cons.injEq, and_true]
  repeat' constructor
  all_goals
    apply BitVec.eq_of_toNat_eq
    simp [wordByte, Nat.shiftRight_eq_div_pow]

/-- Both the source counter and SHA length encoding wrap modulo 2^64. This
holds for every natural byte length, including byte-total and bit-length wrap. -/
theorem encoded_nat (length : Nat) :
    encoded (BitVec.ofNat 64 length) =
      (Silmaril.Crypto.natToBytesBE64 (length * 8)).map UInt8.toBitVec := by
  change X86.Ext.leBytes (X86.Ext.byteSwap64 ((BitVec.ofNat 64 length) <<< 3)) 8 = _
  rw [swapped_bytes, canonical_bytes]
  have shifted : ((BitVec.ofNat 64 length) <<< 3).toNat = (length * 8) % 2^64 := by
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
    omega
  rw [shifted]
  simp only [Silmaril.Crypto.natToBytesBE64, Nat.mod_mod]

theorem encoded_word (total : Word) :
    encoded total = (Silmaril.Crypto.natToBytesBE64 (total.toNat * 8)).map UInt8.toBitVec := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using encoded_nat total.toNat

end Silmaril.Process.CLI.Sha256Cli.LengthStore
