module

public import Silmaril.Process.CLI.Sha256Cli.TailPaddingFrame

/-! # Canonical SHA padding after exactly one full input block

Reference-only facts connect two proved compression steps to the existing
SHA hash. They do not assume any machine-code execution or installed answer.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.FullBlockReference

open Silmaril.Crypto

/-- A nonempty full block has a distinct empty-tail block with bit length512. -/
theorem final_bytes :
    (TailPaddingFrame.block [] 64).map UInt8.ofBitVec =
      [padFirstByte] ++ List.replicate 55 padZero ++ natToBytesBE64 512 := by decide

theorem padding_expansion (message : List Byte) (full : message.length = 64) :
    paddingMD (message.map UInt8.ofBitVec) =
      message.map UInt8.ofBitVec ++ (TailPaddingFrame.block [] 64).map UInt8.ofBitVec := by
  rw [final_bytes]
  simp [paddingMD, List.length_map, full, paddingZeroCount, List.append_assoc]

/-- The canonical driver block sequence is the input block followed by the
actual empty-tail/total64 padding block. The strict input extent is essential. -/
theorem paddedBlocks_pair (message : List Byte) (full : message.length = 64) :
    Driver.paddedBlocks message = [message, TailPaddingFrame.block [] 64] := by
  have inputLength : (message.map UInt8.ofBitVec).length = 64 := by
    simpa only [List.length_map] using full
  have finalLength : ((TailPaddingFrame.block [] 64).map UInt8.ofBitVec).length = 64 := by
    simp only [List.length_map]
    exact TailPaddingFrame.block_length [] (by decide) 64
  have paddedLength : (paddingMD (message.map UInt8.ofBitVec)).length = 128 := by
    rw [padding_expansion message full, List.length_append, inputLength, finalLength]
  have first : ((paddingMD (message.map UInt8.ofBitVec)).take 64).map UInt8.toBitVec = message := by
    rw [padding_expansion message full, List.take_left' inputLength]
    simp only [List.map_map, Function.comp_def, List.map_id']
  have last : (((paddingMD (message.map UInt8.ofBitVec)).drop 64).take 64).map UInt8.toBitVec =
      TailPaddingFrame.block [] 64 := by
    rw [padding_expansion message full, List.drop_left' inputLength,
      List.take_of_length_le (Nat.le_of_eq finalLength)]
    simp only [List.map_map, Function.comp_def, List.map_id']
  simp only [Driver.paddedBlocks, paddedLength, Nat.reduceDiv]
  change [((paddingMD (message.map UInt8.ofBitVec)).take 64).map UInt8.toBitVec,
    (((paddingMD (message.map UInt8.ofBitVec)).drop 64).take 64).map UInt8.toBitVec] = _
  rw [first, last]

/-- Two reference compression steps are the complete existing SHA hash.
The actual driver/callee must independently establish both steps. -/
theorem compress_eq_hash (message : List Byte) (full : message.length = 64) :
    Driver.compressBlock (Driver.compressBlock SHA256.H0 message)
      (TailPaddingFrame.block [] 64) = SHA256.hash (message.map UInt8.ofBitVec) := by
  have folded := Driver.fold_paddedBlocks message
  rw [paddedBlocks_pair message full] at folded
  simpa only [List.foldl_cons, List.foldl_nil] using folded

end Silmaril.Process.CLI.Sha256Cli.FullBlockReference
