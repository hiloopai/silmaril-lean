module

public import Silmaril.Process.CLI.Sha256Cli.LengthEncodingReference
public import Silmaril.Process.CLI.Sha256Cli.TailPaddingFrame

/-! # Canonical padding for every supplied block-aligned input -/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.AlignedPaddingReference

open Silmaril.X86 (Word)
open Silmaril.Crypto

/-- Uniform block lists are recovered by the reference's indexed slices. -/
theorem slices_flatten {α : Type} (size : Nat) (blocks : List (List α))
    (full : ∀ block ∈ blocks, block.length = size) :
    (List.range blocks.length).map (fun index => (blocks.flatten.drop (size * index)).take size) = blocks := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
    have length := full block (by simp)
    have rest : ∀ b ∈ blocks, b.length = size := by
      intro b member
      exact full b (by simp [member])
    have shifted (index : Nat) :
        ((block ++ blocks.flatten).drop (size * (index + 1))).take size =
          (blocks.flatten.drop (size * index)).take size := by
      rw [Nat.mul_succ, Nat.add_comm (size * index) size, ← List.drop_drop, ← length,
        List.drop_append_length]
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.flatten_cons, Nat.mul_zero, List.drop_zero, List.take_left' length, Function.comp_def,
      Nat.succ_eq_add_one, shifted, ih rest]

theorem flatten_length (blocks : List (List Byte))
    (full : ∀ block ∈ blocks, block.length = 64) : blocks.flatten.length = 64 * blocks.length :=
  (Driver.ReadInv.block_bytes (⟨by simp, full, by decide⟩ : Driver.ReadInv blocks.flatten blocks []))

theorem final_bytes (length : Nat) :
    (TailPaddingFrame.block [] (BitVec.ofNat 64 length)).map UInt8.ofBitVec =
      [padFirstByte] ++ List.replicate 55 padZero ++ natToBytesBE64 (length * 8) := by
  rw [TailPaddingFrame.block, LengthStore.encoded_nat]
  simp only [List.length_nil, Nat.sub_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_replicate, List.map_map, Function.comp_def,
    UInt8.ofBitVec_toBitVec, List.map_id']
  rfl

theorem padding_expansion (blocks : List (List Byte))
    (full : ∀ block ∈ blocks, block.length = 64) :
    paddingMD (blocks.flatten.map UInt8.ofBitVec) =
      (blocks ++ [TailPaddingFrame.block [] (BitVec.ofNat 64 blocks.flatten.length)]).flatten.map UInt8.ofBitVec := by
  have aligned : blocks.flatten.length % 64 = 0 := by rw [flatten_length blocks full]; omega
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.map_append]
  rw [final_bytes]
  simp only [paddingMD, List.length_map, paddingZeroCount, aligned, List.append_assoc]
  rfl

/-- Every supplied aligned input has exactly its original full blocks and the
actual empty-tail padding block, for arbitrary natural total byte length. -/
theorem paddedBlocks (blocks : List (List Byte))
    (full : ∀ block ∈ blocks, block.length = 64) :
    Driver.paddedBlocks blocks.flatten =
      blocks ++ [TailPaddingFrame.block [] (BitVec.ofNat 64 blocks.flatten.length)] := by
  let completed := blocks ++ [TailPaddingFrame.block [] (BitVec.ofNat 64 blocks.flatten.length)]
  have allFull : ∀ block ∈ completed, block.length = 64 := by
    intro block member
    rcases List.mem_append.mp member with old | final
    · exact full block old
    · have same := List.mem_singleton.mp final
      subst block
      exact TailPaddingFrame.block_length [] (by decide) _
  have expanded : paddingMD (blocks.flatten.map UInt8.ofBitVec) = completed.flatten.map UInt8.ofBitVec :=
    padding_expansion blocks full
  have count : (paddingMD (blocks.flatten.map UInt8.ofBitVec)).length / 64 = completed.length := by
    rw [expanded, List.length_map, flatten_length completed allFull]
    omega
  have source : (paddingMD (blocks.flatten.map UInt8.ofBitVec)).map UInt8.toBitVec = completed.flatten := by
    rw [expanded]
    simp only [List.map_map, Function.comp_def, List.map_id']
  simp only [Driver.paddedBlocks, count]
  have slices := slices_flatten 64 completed allFull
  simpa only [List.map_take, List.map_drop, source] using slices

end Silmaril.Process.CLI.Sha256Cli.AlignedPaddingReference
