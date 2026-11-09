module

public import Silmaril.Formats.Compression.Inflate.Stream.MemberExamples
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.MemberMachine

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.MemberExamples`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.MemberExamples

open Silmaril.Formats.Compression

/-! ## Split zlib header, an output stall, and a split Adler-32 trailer -/

theorem zlib_header_suspends (version : Version) :
    (zlibNeedsHeader version).reservoir.input = [] ∧
      (zlibNeedsHeader version).reservoir.consumed = 8 ∧
      (zlibNeedsHeader version).output = [] := by
  cases version <;> exact ⟨rfl, rfl, rfl⟩

theorem zlib_zero_capacity_retains_copy (version : Version) :
    copyRemaining (zlibOutputStall version) = some 1 ∧
      (zlibOutputStall version).output = [] ∧
      (zlibOutputStall version).reservoir.input = [65] ∧
      (zlibOutputStall version).reservoir.consumed = 56 := by
  cases version <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem zlib_trailer_suspends (version : Version) :
    (zlibSplitTrailer version).output = [65] ∧
      (zlibSplitTrailer version).reservoir.input = [] ∧
      (zlibSplitTrailer version).reservoir.consumed = 80 := by
  cases version <;> exact ⟨rfl, rfl, rfl⟩

private theorem zlib_split_exact (version : Version) :
    zlibSplitTrailer version =
      .trailer zlibTrailerTail ⟨⟨0, 0, [], 80⟩, ⟨[65]⟩, [65]⟩ := by
  cases version <;> rfl

theorem zlib_done_exact (version : Version) (tail : List UInt8) :
    zlibDone version tail = .done ⟨⟨0, 0, tail, 96⟩, ⟨[65]⟩, [65]⟩ := by
  unfold zlibDone
  rw [zlib_split_exact]
  simp [MemberMachine.applyCall, MemberMachine.feed, call, RawState.feed,
    Reservoir.feed, MemberMachine.step, zlibTrailerTail, ContainerFields.byte,
    Parser.bind, Parser.run, Reservoir.readBits, Reservoir.needBits,
    Reservoir.needBitsAux, Reservoir.needBitsAux_ready, Reservoir.lowBits,
    Reservoir.dropBits, be32Val]

/-! ## Gzip's byte-at-a-time header and a trailer split inside CRC and ISIZE -/

theorem gzip_header_suspends (version : Version) :
    (gzipNeedsHeader version).reservoir.input = [] ∧
      (gzipNeedsHeader version).reservoir.consumed = 8 ∧
      (gzipNeedsHeader version).output = [] := by
  cases version <;> exact ⟨rfl, rfl, rfl⟩

theorem gzip_zero_capacity_retains_copy (version : Version) :
    copyRemaining (gzipOutputStall version) = some 1 ∧
      (gzipOutputStall version).output = [] ∧
      (gzipOutputStall version).reservoir.input = [65] ∧
      (gzipOutputStall version).reservoir.consumed = 120 := by
  cases version <;> exact ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 16384 in
theorem gzip_split_fields_suspend (version : Version) :
    (gzipSplitCRC version).output = [65] ∧
      (gzipSplitCRC version).reservoir.consumed = 152 ∧
      (gzipSplitISIZE version).reservoir.consumed = 176 := by
  cases version <;> exact ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 16384 in
private theorem gzip_split_exact (version : Version) :
    gzipSplitISIZE version =
      .trailer gzipTrailerTail ⟨⟨0, 0, [], 176⟩, ⟨[65]⟩, [65]⟩ := by
  cases version <;> rfl

set_option maxRecDepth 16384 in
theorem gzip_done_exact (version : Version) (tail : List UInt8) :
    gzipDone version tail = .done ⟨⟨0, 0, tail, 192⟩, ⟨[65]⟩, [65]⟩ := by
  unfold gzipDone
  rw [gzip_split_exact]
  simp [MemberMachine.applyCall, MemberMachine.feed, call, RawState.feed,
    Reservoir.feed, MemberMachine.step, gzipTrailerTail, ContainerFields.byte,
    Parser.bind, Parser.run, Reservoir.readBits, Reservoir.needBits,
    Reservoir.needBitsAux, Reservoir.needBitsAux_ready, Reservoir.lowBits,
    Reservoir.dropBits, le32Val]

set_option maxRecDepth 16384 in
theorem gzip_wrong_crc_rejected (version : Version) :
    trailerRejected (gzipWrongCRC version) = true ∧ (gzipWrongCRC version).output = [65] := by
  cases version <;> decide

set_option maxRecDepth 16384 in
theorem gzip_wrong_isize_rejected (version : Version) :
    trailerRejected (gzipWrongISIZE version) = true ∧ (gzipWrongISIZE version).output = [65] := by
  cases version <;> decide

/-! ## Fixed Huffman with an overlapping match and one-byte output calls -/

set_option maxRecDepth 16384 in
theorem fixed_zlib_done (version : Version) :
    fixedZlib version =
      .done ⟨⟨0, 0, [0xaa, 0xbb], 88⟩, ⟨List.replicate 8 65⟩, List.replicate 8 65⟩ := by
  cases version <;> rfl

set_option maxRecDepth 16384 in
theorem fixed_gzip_done (version : Version) :
    fixedGzip version =
      .done ⟨⟨0, 0, [0xaa, 0xbb], 184⟩, ⟨List.replicate 8 65⟩, List.replicate 8 65⟩ := by
  cases version <;> rfl

end Silmaril.Formats.Compression.Inflate.Stream.MemberExamples
