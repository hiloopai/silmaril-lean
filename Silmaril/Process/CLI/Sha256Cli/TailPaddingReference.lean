module

public import Silmaril.Process.CLI.Sha256Cli.AlignedPaddingReference

/-! # Canonical SHA padding after arbitrary full blocks and a remainder

All remainders below64 are covered at the reference level. The short branch
uses the actual `TailPaddingFrame.block`; the long branch describes two
reference blocks without claiming machine execution of that separate path.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.TailPaddingReference

open Silmaril.X86 (Word)
open Silmaril.Crypto

/-- The remainder's one or two final blocks, with the actual modular total
serialization. This definition alone makes no machine execution assertion. -/
def blocks (tail : List Byte) (total : Word) : List (List Byte) :=
  if tail.length < 56 then [TailPaddingFrame.block tail total]
  else [tail ++ [0x80] ++ List.replicate (63 - tail.length) 0,
    List.replicate 56 0 ++ LengthStore.encoded total]

theorem full (tail : List Byte) (room : tail.length < 64) (total : Word) :
    ∀ block ∈ blocks tail total, block.length = 64 := by
  intro block member
  by_cases short : tail.length < 56
  · simp only [blocks, ite_eq_left short, List.mem_singleton] at member
    subst block
    exact TailPaddingFrame.block_length tail short total
  · simp only [blocks, ite_eq_right short, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simp only [List.length_append, List.length_singleton, List.length_replicate]
      omega
    · simp only [List.length_append, List.length_replicate, LengthStore.encoded_length]

theorem padding_expansion (prefixBlocks : List (List Byte)) (tail : List Byte)
    (full : ∀ block ∈ prefixBlocks, block.length = 64) (room : tail.length < 64) :
    paddingMD ((prefixBlocks.flatten ++ tail).map UInt8.ofBitVec) =
      (prefixBlocks ++ blocks tail (BitVec.ofNat 64 (prefixBlocks.flatten ++ tail).length)).flatten.map UInt8.ofBitVec := by
  have remainder : (prefixBlocks.flatten ++ tail).length % 64 = tail.length :=
    (⟨rfl, full, room⟩ : Driver.ReadInv (prefixBlocks.flatten ++ tail) prefixBlocks tail).remainder
  simp only [paddingMD, List.length_map]
  by_cases short : tail.length < 56
  · simp only [paddingZeroCount, remainder, ite_eq_left short]
    simp only [blocks, ite_eq_left short, List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil, TailPaddingFrame.block, LengthStore.encoded_nat, List.map_append,
      List.map_cons, List.map_replicate, List.map_map, Function.comp_def,
      UInt8.ofBitVec_toBitVec, List.map_id']
    simp only [padFirstByte, padZero, List.append_assoc, List.singleton_append]
    rfl
  · have zeros : 119 - tail.length = (63 - tail.length) + 56 := by omega
    simp only [paddingZeroCount, remainder, ite_eq_right short, zeros, List.replicate_add]
    simp only [blocks, ite_eq_right short, List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil, LengthStore.encoded_nat, List.map_append, List.map_cons,
      List.map_nil, List.map_replicate, List.map_map, Function.comp_def,
      UInt8.ofBitVec_toBitVec, List.map_id', List.append_assoc]
    rfl

/-- Every finite message decomposition into full blocks and a remainder has
this canonical block list, including remainders56..63 and modular length wrap. -/
theorem paddedBlocks (prefixBlocks : List (List Byte)) (tail : List Byte)
    (prefixFull : ∀ block ∈ prefixBlocks, block.length = 64) (room : tail.length < 64) :
    Driver.paddedBlocks (prefixBlocks.flatten ++ tail) =
      prefixBlocks ++ blocks tail (BitVec.ofNat 64 (prefixBlocks.flatten ++ tail).length) := by
  let completed := prefixBlocks ++ blocks tail (BitVec.ofNat 64 (prefixBlocks.flatten ++ tail).length)
  have allFull : ∀ block ∈ completed, block.length = 64 := by
    intro block member
    rcases List.mem_append.mp member with old | final
    · exact prefixFull block old
    · exact full tail room _ block final
  have expanded : paddingMD ((prefixBlocks.flatten ++ tail).map UInt8.ofBitVec) =
      completed.flatten.map UInt8.ofBitVec := padding_expansion prefixBlocks tail prefixFull room
  have count : (paddingMD ((prefixBlocks.flatten ++ tail).map UInt8.ofBitVec)).length / 64 =
      completed.length := by
    rw [expanded, List.length_map, AlignedPaddingReference.flatten_length completed allFull]
    omega
  have source : (paddingMD ((prefixBlocks.flatten ++ tail).map UInt8.ofBitVec)).map UInt8.toBitVec =
      completed.flatten := by
    rw [expanded]
    simp only [List.map_map, Function.comp_def, List.map_id']
  simp only [Driver.paddedBlocks, count]
  have slices := AlignedPaddingReference.slices_flatten 64 completed allFull
  simpa only [List.map_take, List.map_drop, source] using slices

theorem paddedBlocks_short (prefixBlocks : List (List Byte)) (tail : List Byte)
    (full : ∀ block ∈ prefixBlocks, block.length = 64) (short : tail.length < 56) :
    Driver.paddedBlocks (prefixBlocks.flatten ++ tail) =
      prefixBlocks ++ [TailPaddingFrame.block tail (BitVec.ofNat 64 (prefixBlocks.flatten ++ tail).length)] := by
  simpa only [blocks, ite_eq_left short] using paddedBlocks prefixBlocks tail full (by omega)

/-- Reference fold identification only: actual memory/callee premises are
separately supplied by the machine EOF/output adapter. -/
theorem fold_short (prefixBlocks : List (List Byte)) (tail : List Byte)
    (full : ∀ block ∈ prefixBlocks, block.length = 64) (short : tail.length < 56) :
    Driver.compressBlock (prefixBlocks.foldl Driver.compressBlock SHA256.H0)
      (TailPaddingFrame.block tail (BitVec.ofNat 64 (prefixBlocks.flatten ++ tail).length)) =
        SHA256.hash ((prefixBlocks.flatten ++ tail).map UInt8.ofBitVec) := by
  have folded := Driver.fold_paddedBlocks (prefixBlocks.flatten ++ tail)
  rw [paddedBlocks_short prefixBlocks tail full short, List.foldl_append] at folded
  simpa only [List.foldl_cons, List.foldl_nil] using folded

end Silmaril.Process.CLI.Sha256Cli.TailPaddingReference
