module

public import Silmaril.Crypto.X86.Sha256O2
public import Silmaril.Crypto.SHA256.Equiv

/-! # Reading the compression contract in the canonical SHA specification

The machine contract uses `BitVec 32` hash words and big-endian byte reads.
The source/driver specification uses `UInt32` and `SHA256.parseBlock`.
Only byte parsing and representation round trips are proved here; the
cryptographic equivalence is the existing `SHA256.processBlock_eq_compressBlock`.
All byte-block applications require the actual 64-byte block length.
-/

@[expose] public section

namespace Silmaril.Crypto.X86.Sha256O2

open Silmaril.Process (Byte Memory)
open Silmaril.X86 (Word MState)

/-- A backed state buffer determines a unique hash value. -/
theorem StateHolds.unique {memory : Memory} {state : Word} {H H' : SHA256.Kernel.InitHash}
    (first : StateHolds memory state H) (second : StateHolds memory state H') : H = H' := by
  obtain ⟨bytes, read, value⟩ := first
  obtain ⟨bytes', read', value'⟩ := second
  have same := Option.some.inj (read.symm.trans read')
  subst bytes'
  exact value.symm.trans value'

/-- The canonical parser's arithmetic and the machine contract's byte shifts
assemble the same big-endian word, for every four bytes. -/
theorem ofBytesBE32_toBitVec (b0 b1 b2 b3 : Byte) :
    (Silmaril.Crypto.ofBytesBE32 (UInt8.ofBitVec b0) (UInt8.ofBitVec b1)
      (UInt8.ofBitVec b2) (UInt8.ofBitVec b3)).toBitVec =
      (b0.setWidth 32 <<< 24) ||| (b1.setWidth 32 <<< 16) |||
        (b2.setWidth 32 <<< 8) ||| b3.setWidth 32 := by
  have assembled :
      (Silmaril.Crypto.ofBytesBE32 (UInt8.ofBitVec b0) (UInt8.ofBitVec b1)
        (UInt8.ofBitVec b2) (UInt8.ofBitVec b3)).toBitVec =
        (b0 ++ b1 ++ b2 ++ b3 : BitVec 32) := by
    apply BitVec.eq_of_toNat_eq
    simp only [Silmaril.Crypto.ofBytesBE32, UInt32.toBitVec_ofNat',
      UInt8.toNat_ofBitVec, Nat.mod_eq_of_lt b0.isLt, Nat.mod_eq_of_lt b1.isLt,
      Nat.mod_eq_of_lt b2.isLt, Nat.mod_eq_of_lt b3.isLt,
      BitVec.toNat_ofNat, BitVec.toNat_append]
    rw [← Nat.shiftLeft_add_eq_or_of_lt b3.isLt,
      ← Nat.shiftLeft_add_eq_or_of_lt b2.isLt,
      ← Nat.shiftLeft_add_eq_or_of_lt b1.isLt]
    simp only [Nat.shiftLeft_eq]
    have h0 := b0.isLt
    have h1 := b1.isLt
    have h2 := b2.isLt
    have h3 := b3.isLt
    norm_num at h0 h1 h2 h3 ⊢
    omega
  rw [assembled]
  simpa only [BitVec.setWidth_eq, Nat.reduceAdd] using
    (BitVec.setWidth_append_append_append_eq_shiftLeft_setWidth_or
      (b := b0) (b' := b1) (b'' := b2) (b''' := b3) (w'''' := 32))

/-- A complete parsed word has exactly the byte value used by the callee
contract. Incomplete trailing groups are excluded by the explicit bound. -/
theorem parseBlock_getD_toBitVec (bytes : List Byte) (i : Nat)
    (complete : 4 * i + 4 ≤ bytes.length) :
    ((SHA256.parseBlock (bytes.map UInt8.ofBitVec)).getD i 0).toBitVec =
      beWordAt bytes i := by
  induction i generalizing bytes with
  | zero =>
    cases bytes with
    | nil => simp at complete
    | cons b0 rest =>
      cases rest with
      | nil => simp at complete
      | cons b1 rest =>
        cases rest with
        | nil => simp at complete
        | cons b2 rest =>
          cases rest with
          | nil => simp at complete
          | cons b3 rest =>
            simpa only [List.map_cons, SHA256.parseBlock, List.getD_cons_zero,
              List.getD_cons_succ, beWordAt, byteAt, Nat.mul_zero, Nat.zero_add] using
              ofBytesBE32_toBitVec b0 b1 b2 b3
  | succ i ih =>
    cases bytes with
    | nil => simp at complete
    | cons b0 rest =>
      cases rest with
      | nil => simp at complete
      | cons b1 rest =>
        cases rest with
        | nil => simp at complete
        | cons b2 rest =>
          cases rest with
          | nil => simp at complete
          | cons b3 rest =>
            have bound : 4 * i + 4 ≤ rest.length := by
              simp only [List.length_cons] at complete
              omega
            simpa [List.map_cons, SHA256.parseBlock, beWordAt, byteAt,
              Nat.mul_add, Nat.add_assoc] using ih rest bound

/-- A complete 64-byte block parses to exactly the callee's sixteen words. -/
theorem parseBlock_toBitVec (block : List Byte) (length : block.length = 64) :
    (SHA256.parseBlock (block.map UInt8.ofBitVec)).map UInt32.toBitVec =
      (List.range 16).map (beWordAt block) := by
  apply List.ext_getElem
  · simp only [List.length_map, SHA256.parseBlock_length, length, List.length_range]
  · intro i hi _
    have parsedLength : (SHA256.parseBlock (block.map UInt8.ofBitVec)).length = 16 := by
      simp only [SHA256.parseBlock_length, List.length_map, length]
    have small : i < 16 := by simpa only [List.length_map, parsedLength] using hi
    simp only [List.getElem_map, List.getElem_range]
    have bound : 4 * i + 4 ≤ block.length := by omega
    have inBounds : i < (SHA256.parseBlock (block.map UInt8.ofBitVec)).length := by omega
    simpa only [List.getD_eq_getElem?_getD,
      getElem?_pos (SHA256.parseBlock (block.map UInt8.ofBitVec)) i inBounds,
      Option.getD_some] using parseBlock_getD_toBitVec block i bound

/-- The machine contract's compression is the existing canonical reference
compression, on every hash state and complete byte block. -/
theorem compressBlock_toState (H : SHA256.Kernel.InitHash) (block : List Byte)
    (length : block.length = 64) :
    (compressBlock H block).toState =
      SHA256.processBlock H.toState (SHA256.parseBlock (block.map UInt8.ofBitVec)) := by
  rw [SHA256.processBlock_eq_compressBlock, parseBlock_toBitVec block length]
  have roundtrip : SHA256.State.toInitHash H.toState = H := by cases H; rfl
  rw [roundtrip]
  rfl

/-- The same transition beginning with the canonical driver's state type. -/
theorem compressBlock_fromState (H : SHA256.State) (block : List Byte)
    (length : block.length = 64) :
    (compressBlock (SHA256.State.toInitHash H) block).toState =
      SHA256.processBlock H (SHA256.parseBlock (block.map UInt8.ofBitVec)) := by
  rw [compressBlock_toState _ _ length]
  have roundtrip : (SHA256.State.toInitHash H).toState = H := by
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := H
    rfl
  rw [roundtrip]

/-- Read a machine compression result in the driver's `UInt32` vocabulary. -/
theorem StateHolds.compressed_reference {memory : Memory} {state : Word}
    {H : SHA256.Kernel.InitHash} {block : List Byte}
    (holds : StateHolds memory state (compressBlock H block))
    (length : block.length = 64) :
    ∃ bytes, memory.readBytes state.toNat 32 = some bytes ∧
      (stateOf bytes).toState =
        SHA256.processBlock H.toState (SHA256.parseBlock (block.map UInt8.ofBitVec)) := by
  obtain ⟨bytes, read, value⟩ := holds
  exact ⟨bytes, read, (congrArg SHA256.Kernel.InitHash.toState value).trans
    (compressBlock_toState H block length)⟩

/-- A proved callee postcondition establishes one source-driver compression
transition, once the actual entry buffer reads and block length are known. -/
theorem Post.compressed_reference {L : Layout} {state block rspEntry : Word} {frame : Nat}
    {initial final : MState} (post : Post L state block rspEntry frame initial final)
    {stateBytes blockBytes : List Byte}
    (stateRead : initial.memory.readBytes state.toNat 32 = some stateBytes)
    (blockRead : initial.memory.readBytes block.toNat 64 = some blockBytes)
    (length : blockBytes.length = 64) :
    ∃ bytes, final.memory.readBytes state.toNat 32 = some bytes ∧
      (stateOf bytes).toState = SHA256.processBlock (stateOf stateBytes).toState
        (SHA256.parseBlock (blockBytes.map UInt8.ofBitVec)) :=
  (post.compressed stateBytes blockBytes stateRead blockRead).compressed_reference length

end Silmaril.Crypto.X86.Sha256O2
