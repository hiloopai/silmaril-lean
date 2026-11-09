module

public import Silmaril.Formats.Compression.Inflate.Stream.Checksums
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.Protocol
public import Silmaril.Raw.Formats.Compression.Bits.Bit
public import Silmaril.Formats.Compression.Bits.Bitstream
public import Silmaril.Raw.Formats.Compression.Deflate.Huffman
public import Silmaril.Formats.Compression.Deflate.Decompress
public import Silmaril.Raw.Formats.Compression.Deflate.Stored
public import Silmaril.Raw.Formats.Compression.Deflate.WithHistory
public import Silmaril.Formats.Compression.Deflate.Compress
public import Silmaril.Raw.Formats.Compression.Deflate.LZ77
public import Silmaril.Raw.Formats.Compression.Bits.ByteFields
public import Silmaril.Raw.Formats.Compression.Checksum.Adler32
public import Silmaril.Raw.Formats.Compression.Checksum.CRC32
public import Silmaril.Raw.Formats.Compression.Zlib.Basic
public import Silmaril.Raw.Formats.Compression.Zlib.Take
public import Silmaril.Raw.Formats.Compression.Zlib.Dictionary
public import Silmaril.Raw.Formats.Compression.Gzip.Basic

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.Checksums`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.Checksums

open Silmaril.Formats.Compression
open Protocol

/-- The Adler seed is one; the gzip data-CRC seed is zero. -/
theorem checksum_empty : checksum .adler32 [] = 1 ∧ checksum .crc32 [] = 0 := by
  decide

theorem update_prefix (kind : ChecksumKind) (committed added : List UInt8) :
    update kind (checksum kind committed) added = checksum kind (committed ++ added) := by
  cases kind with
  | adler32 =>
    let state := adler32Fold (1, 0) (committed.map UInt8.toNat)
    have hbound := adler32Fold_lt (1, 0) (committed.map UInt8.toNat) (by decide) (by decide)
    have ha : state.1 < 65536 := by unfold state; unfold adlerMod at hbound; omega
    have hb : state.2 < 65536 := by unfold state; unfold adlerMod at hbound; omega
    have hsplit : (checksum .adler32 committed % 65536, checksum .adler32 committed / 65536) = state := by
      change ((state.2 * 65536 + state.1) % 65536,
        (state.2 * 65536 + state.1) / 65536) = state
      apply Prod.ext <;> dsimp only <;> omega
    simp only [update]
    rw [hsplit]
    simp only [checksum, adler32OfList, List.map_append, adler32Fold_append]
    rfl
  | crc32 =>
    simpa only [update, checksum, List.map_append] using
      (crc32List_append (committed.map UInt8.toNat) (added.map UInt8.toNat)).symm

theorem checksum_lt_word32 (kind : ChecksumKind) (bytes : List UInt8) :
    checksum kind bytes < word32 := by
  cases kind with
  | adler32 => exact adler32OfList_lt _
  | crc32 =>
    apply crc32List_lt
    intro value hv
    obtain ⟨byte, _, rfl⟩ := List.mem_map.mp hv
    exact byte.toNat_lt

theorem checksum_lt_word64 (kind : ChecksumKind) (bytes : List UInt8) :
    checksum kind bytes < word64 :=
  Nat.lt_trans (checksum_lt_word32 kind bytes) (by decide)

theorem update_prefix_mod64 (kind : ChecksumKind) (committed added : List UInt8) :
    update kind (checksum kind committed) added % word64 = checksum kind (committed ++ added) := by
  rw [update_prefix, Nat.mod_eq_of_lt (checksum_lt_word64 _ _)]

theorem checksumKind_checkOutput_with (updater : UpdateCheck) (fields : ExitFields) :
    checksumKind (checkOutput updater fields) = checksumKind fields := by
  by_cases hwrap : fields.wrap = 0
  · simp only [checkOutput, hwrap, ite_true]
  · simp only [checkOutput, hwrap, ite_false, checksumKind]

theorem checksumKind_checkOutput (fields : ExitFields) :
    checksumKind (checkOutput update fields) = checksumKind fields :=
  checksumKind_checkOutput_with update fields

theorem checkOutput_prefix (fields : ExitFields) (committed : List UInt8)
    (hprefix : PrefixInvariant fields committed) (hcounts : CountsCoherent fields)
    (hwrap : fields.wrap ≠ 0) (hvalidate : validateChecks fields = true) :
    PrefixInvariant (checkOutput update fields) (committed ++ fields.pendingOutput) := by
  obtain ⟨hcheck, hpublic⟩ := hprefix
  unfold PrefixInvariant
  rw [checksumKind_checkOutput]
  by_cases hzero : produced fields = 0
  · have hpending : fields.pendingOutput = [] := by
      have hlength := hcounts.2.2.2.2.trans hzero
      cases hs : fields.pendingOutput with
      | nil => rfl
      | cons byte rest => simp only [hs, List.length_cons] at hlength; omega
    simp only [checkOutput, ite_eq_right hwrap, hvalidate, hzero, ne_eq,
      not_true_eq_false, decide_false, Bool.and_false, Bool.false_eq_true, ite_false]
    exact ⟨by simpa only [hpending, List.append_nil] using hcheck, hpublic⟩
  · have hupdate : update (checksumKind fields) fields.check fields.pendingOutput % word64 =
        checksum (checksumKind fields) (committed ++ fields.pendingOutput) := by
      rw [hcheck, update_prefix_mod64]
    have hchanged : (validateChecks fields && decide (produced fields ≠ 0)) = true := by
      simp only [hvalidate, Bool.true_and, decide_eq_true_eq]
      exact hzero
    simp only [checkOutput, ite_eq_right hwrap, hchanged, ite_true]
    exact ⟨hupdate, trivial⟩

/-- CHECK commits the bytes once and clears/rebases the source's local output
accounting view, including when the offered output buffer is empty. -/
theorem checkOutput_commit (fields : ExitFields) (committed : List UInt8)
    (hprefix : PrefixInvariant fields committed) (hcounts : CountsCoherent fields)
    (hwrap : fields.wrap ≠ 0) (hvalidate : validateChecks fields = true) :
    PrefixInvariant (checkOutput update fields) (committed ++ fields.pendingOutput) ∧
      (checkOutput update fields).pendingOutput = [] ∧
      (checkOutput update fields).savedOut = fields.left ∧
      produced (checkOutput update fields) = 0 := by
  refine ⟨checkOutput_prefix fields committed hprefix hcounts hwrap hvalidate, ?_, ?_,
    checkOutput_rebases update fields hwrap⟩ <;>
    simp only [checkOutput, ite_eq_right hwrap]

end Silmaril.Formats.Compression.Inflate.Stream.Checksums
