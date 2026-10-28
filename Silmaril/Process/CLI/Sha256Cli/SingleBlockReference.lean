module

public import Silmaril.Process.CLI.Sha256Cli.Driver
public import Silmaril.Crypto.X86.Sha256O2.Reference

/-! # Canonical SHA padding and compression for a short message

Messages shorter than 56 bytes have exactly one canonical padded block. The
hash equation reuses the existing driver fold and SHA specification. These
are reference facts until actual memory reads and a proved machine callee
postcondition are supplied to `compressed_hash`; no execution is assumed.
The representation bridge is the explicit external dependency PR #3052.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.SingleBlockReference

open Silmaril.Crypto
open Silmaril.Crypto.X86.Sha256O2 (Layout Post stateOf)
open Silmaril.X86 (Word MState)

/-- The existing canonical padding, represented as process bytes. -/
def block (message : List Byte) : List Byte :=
  (paddingMD (message.map UInt8.ofBitVec)).map UInt8.toBitVec

/-- The strict 56-byte boundary retains room for the marker and length field. -/
theorem padding_length (message : List UInt8) (short : message.length < 56) :
    (paddingMD message).length = 64 := by
  have remainder : message.length % 64 = message.length := Nat.mod_eq_of_lt (by omega)
  have zeros : paddingZeroCount message.length = 55 - message.length := by
    simp only [paddingZeroCount, remainder, ite_eq_left short]
  simp only [paddingMD, List.length_append, List.length_singleton, List.length_replicate,
    natToBytesBE64_length, zeros]
  omega

theorem block_length (message : List Byte) (short : message.length < 56) :
    (block message).length = 64 := by
  simp only [block, List.length_map]
  exact padding_length _ (by simpa only [List.length_map] using short)

/-- Exact bytes for binding the actual pad/zero-fill and length stores. -/
theorem block_expansion (message : List Byte) (short : message.length < 56) :
    block message =
      (message ++ (0x80 :: List.replicate (55 - message.length) 0)) ++
        (natToBytesBE64 (message.length * 8)).map UInt8.toBitVec := by
  have remainder : message.length % 64 = message.length := Nat.mod_eq_of_lt (by omega)
  simp [block, paddingMD, paddingZeroCount, remainder, short, List.map_append,
    List.map_map, Function.comp_def, padFirstByte, padZero,
    List.append_assoc]

/-- The existing driver block sequence contains precisely this one block. -/
theorem paddedBlocks_singleton (message : List Byte) (short : message.length < 56) :
    Driver.paddedBlocks message = [block message] := by
  have length : (paddingMD (message.map UInt8.ofBitVec)).length = 64 :=
    padding_length _ (by simpa only [List.length_map] using short)
  dsimp only [Driver.paddedBlocks]
  rw [length]
  simp only [Nat.reduceDiv, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, Nat.mul_zero, List.drop_zero]
  rw [List.take_of_length_le (by omega)]
  rfl

/-- One compression from H0 is the canonical complete hash, by the existing
fold theorem; no compression rounds are recomputed by this proof. -/
theorem compress_eq_hash (message : List Byte) (short : message.length < 56) :
    Driver.compressBlock SHA256.H0 (block message) =
      SHA256.hash (message.map UInt8.ofBitVec) := by
  have folded := Driver.fold_paddedBlocks message
  rw [paddedBlocks_singleton message short] at folded
  simpa only [List.foldl_cons, List.foldl_nil] using folded

theorem processBlock_eq_hash (message : List Byte) (short : message.length < 56) :
    SHA256.processBlock SHA256.H0
      (SHA256.parseBlock (paddingMD (message.map UInt8.ofBitVec))) =
        SHA256.hash (message.map UInt8.ofBitVec) := by
  simpa only [Driver.compressBlock, block, List.map_map, Function.comp_def,
    UInt8.ofBitVec_toBitVec, List.map_id'] using compress_eq_hash message short

/-- A proved machine compression postcondition gives the canonical short
message hash once its actual initial-state and padded-block reads are bound.
The driver must establish every read/ABI/return premise independently. -/
theorem compressed_hash {L : Layout} {state buffer rspEntry : Word} {frame : Nat}
    {initial final : MState} (post : Post L state buffer rspEntry frame initial final)
    {message stateBytes : List Byte} (short : message.length < 56)
    (stateRead : initial.memory.readBytes state.toNat 32 = some stateBytes)
    (initialHash : (stateOf stateBytes).toState = SHA256.H0)
    (blockRead : initial.memory.readBytes buffer.toNat 64 = some (block message)) :
    ∃ bytes, final.memory.readBytes state.toNat 32 = some bytes ∧
      (stateOf bytes).toState = SHA256.hash (message.map UInt8.ofBitVec) := by
  obtain ⟨bytes, read, value⟩ :=
    post.compressed_reference stateRead blockRead (block_length message short)
  rw [initialHash] at value
  change (stateOf bytes).toState = Driver.compressBlock SHA256.H0 (block message) at value
  exact ⟨bytes, read, value.trans (compress_eq_hash message short)⟩

end Silmaril.Process.CLI.Sha256Cli.SingleBlockReference
