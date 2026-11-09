module

public import Silmaril.Formats.Compression.Inflate.Stream.RawContainers
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.RawRuns
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

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.RawContainers`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.RawContainers

open Silmaril.Formats.Compression

/-- Isolate the header observation without changing the gzip specification. -/
theorem gzipMember_eq_body (bytes : List UInt8) :
    gzipMember bytes =
      match gzipBody bytes with
      | none => none
      | some body =>
        match Deflate.deflateTake body with
        | .error _ => none
        | .ok (data, afterData) =>
          match gzipCheckTrailer data afterData with
          | none => none
          | some tail => some (data, tail) := by
  unfold gzipBody gzipMember
  split <;> split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  rfl

theorem zlibTake_of_header_raw_trailer
    (member body data afterData tail : List UInt8)
    (hheader : zlibCheckHeader member = some body)
    (hraw : Deflate.deflateTake body = .ok (data, afterData))
    (htrailer : zlibCheckTrailer data afterData = some tail) :
    zlibTake member = some (data, tail) := by
  simp only [zlibTake, hheader, hraw, htrailer]

theorem gzipMember_of_header_raw_trailer
    (member body data afterData tail : List UInt8)
    (hheader : gzipBody member = some body)
    (hraw : Deflate.deflateTake body = .ok (data, afterData))
    (htrailer : gzipCheckTrailer data afterData = some tail) :
    gzipMember member = some (data, tail) := by
  simp only [gzipMember_eq_body, hheader, hraw, htrailer]

/-- An actually completed raw schedule satisfies the shared zlib member
specification after the independent header and Adler-32 checks succeed. The
future suffix can contain trailer bytes not delivered to the raw controller. -/
theorem zlib_done_feed (version : Version) (initial : List UInt8)
    (calls : List RawMachine.Call) (completed : RawState)
    (hdone : RawMachine.runCalls version (RawMachine.start initial) calls = .done completed) :
    ∃ rest, Reservoir.Normalizes completed.reservoir rest ∧
      ∀ future member tail,
        zlibCheckHeader member = some (initial ++ RawRuns.deliveredInput calls ++ future) →
        zlibCheckTrailer completed.output (rest.input ++ future) = some tail →
        zlibTake member = some (completed.output, tail) := by
  obtain ⟨rest, hnorm, hraw⟩ := RawRuns.done_correct_feed version initial calls completed hdone
  refine ⟨rest, hnorm, ?_⟩
  intro future member tail hheader htrailer
  exact zlibTake_of_header_raw_trailer member _ _ _ tail hheader (hraw future) htrailer

/-- The same completed raw schedule satisfies the shared gzip member
specification after its header, CRC-32, and ISIZE checks succeed. This stops at
one member; concatenating members belongs to the gzip client loop. -/
theorem gzip_done_feed (version : Version) (initial : List UInt8)
    (calls : List RawMachine.Call) (completed : RawState)
    (hdone : RawMachine.runCalls version (RawMachine.start initial) calls = .done completed) :
    ∃ rest, Reservoir.Normalizes completed.reservoir rest ∧
      ∀ future member tail,
        gzipBody member = some (initial ++ RawRuns.deliveredInput calls ++ future) →
        gzipCheckTrailer completed.output (rest.input ++ future) = some tail →
        gzipMember member = some (completed.output, tail) := by
  obtain ⟨rest, hnorm, hraw⟩ := RawRuns.done_correct_feed version initial calls completed hdone
  refine ⟨rest, hnorm, ?_⟩
  intro future member tail hheader htrailer
  exact gzipMember_of_header_raw_trailer member _ _ _ tail hheader (hraw future) htrailer

/-- Imposing the older exact-end boundary recovers `zlibDecompress`, rather
than merely its suffix-preserving member observation. -/
theorem zlibDecompress_of_member (member : ByteArray) (data : List UInt8)
    (h : zlibTake member.data.toList = some (data, [])) :
    zlibDecompress member = some ⟨data.toArray⟩ := by
  rw [zlibDecompress_eq_exactMember, h]
  rfl

/-- A successful single member with no remaining bytes is a complete gzip
file. Additional members are handled by the existing `gzipMembers` loop. -/
theorem gzipDecompress_of_member (member : ByteArray) (data : List UInt8)
    (h : gzipMember member.data.toList = some (data, [])) :
    gzipDecompress member = some ⟨data.toArray⟩ := by
  simp only [gzipDecompress, gzipMembers, h, List.nil_append]

/-! ## Nonvacuity: one stored A, with the trailer supplied only afterward -/

theorem storedA_completes (version : Version) :
    RawMachine.runCalls version (RawMachine.start storedAInput) storedACalls =
      .done storedAState := by
  cases version <;> rfl

theorem storedA_reader_empty (rest : LSBReader)
    (h : Reservoir.Normalizes storedAState.reservoir rest) : rest.input = [] := by
  have hlength := congrArg List.length h.2.2.1.2
  change (natBits rest.buffer rest.count ++ bytesBits rest.input).length = 0 at hlength
  simp only [List.length_append, length_natBits, length_bytesBits] at hlength
  cases hinput : rest.input with
  | nil => rfl
  | cons byte bytes => simp only [hinput, List.length_cons] at hlength; omega

/-- Both actual version schedules compose with a later Adler-32 trailer and
retain an arbitrary suffix. No successful specification decode is a premise. -/
theorem storedA_zlib (version : Version) (tail : List UInt8) :
    zlibTake ([0x78, 0x01] ++ storedAInput ++ ([0, 66, 0, 66] ++ tail)) =
      some ([65], tail) := by
  obtain ⟨rest, hnorm, correct⟩ :=
    zlib_done_feed version storedAInput storedACalls storedAState (storedA_completes version)
  have hinput := storedA_reader_empty rest hnorm
  apply correct ([0, 66, 0, 66] ++ tail)
  · rfl
  · rw [hinput]
    rfl

/-- The same raw schedule composes with a later gzip CRC-32/ISIZE trailer. -/
theorem storedA_gzip (version : Version) (tail : List UInt8) :
    gzipMember ([31, 139, 8, 0, 0, 0, 0, 0, 0, 255] ++ storedAInput ++
      ([139, 158, 217, 211, 1, 0, 0, 0] ++ tail)) = some ([65], tail) := by
  obtain ⟨rest, hnorm, correct⟩ :=
    gzip_done_feed version storedAInput storedACalls storedAState (storedA_completes version)
  have hinput := storedA_reader_empty rest hnorm
  apply correct ([139, 158, 217, 211, 1, 0, 0, 0] ++ tail)
  · rfl
  · rw [hinput]
    rfl

end Silmaril.Formats.Compression.Inflate.Stream.RawContainers
