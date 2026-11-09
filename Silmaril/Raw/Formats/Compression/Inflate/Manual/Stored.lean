module

public import Silmaril.Formats.Compression.Inflate.Manual.Stored
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
public import Silmaril.Raw.Formats.Compression.Bits.BitstreamLemmas
public import Silmaril.Raw.Formats.Compression.Bits.BitstreamFacts
public import Silmaril.Raw.Formats.Compression.Deflate.HuffmanLemmas
public import Silmaril.Raw.Formats.Compression.Deflate.StoredWriter
public import Silmaril.Raw.Formats.Compression.Deflate.RoundTrip
public import Silmaril.Raw.Formats.Compression.Checksum.Adler32Spec
public import Silmaril.Raw.Formats.Compression.Zlib.DictionaryHistory
public import Silmaril.Raw.Formats.Compression.Vectors

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Manual.Stored`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Manual

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Deflate (DecompressError)

theorem stored_complement_iff (len nlen : Nat) :
    len = nlen ^^^ 65535 ↔ len ^^^ nlen = 65535 := by
  constructor
  · intro h
    rw [h, Nat.xor_comm nlen 65535, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · intro h
    calc
      len = (len ^^^ nlen) ^^^ nlen := by
        rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      _ = 65535 ^^^ nlen := by rw [h]
      _ = nlen ^^^ 65535 := Nat.xor_comm _ _

/-- Exact agreement with the existing stored-block specification, including
malformed LEN/NLEN, truncated headers, truncated payloads and reader counters. -/
theorem decompressStored_eq (r : LSBReader) :
    decompressStored r = Deflate.decompressStored r := by
  simp only [decompressStored, decompressStoredArray, readStoredHeader,
    Deflate.decompressStored]
  cases hlen : r.alignToByte.readBits 16 with
  | none => rfl
  | some p =>
    obtain ⟨len, afterLen⟩ := p
    dsimp only
    cases hnlen : afterLen.readBits 16 with
    | none => rfl
    | some p =>
      obtain ⟨nlen, afterHeader⟩ := p
      dsimp only
      have hl := LSBReader.readBits_lt hlen
      have hnl := LSBReader.readBits_lt hnlen
      have hx : len ^^^ nlen < 65536 :=
        Nat.xor_lt_two_pow (n := 16) hl hnl
      have hcheck : (len ^^^ nlen) % 65536 = 65535 ↔ len = nlen ^^^ 65535 := by
        rw [Nat.mod_eq_of_lt hx]
        exact (stored_complement_iff len nlen).symm
      by_cases h : len = nlen ^^^ 65535
      · have hspec := hcheck.mpr h
        simp only [ite_eq_left h, ite_eq_right (show ¬((len ^^^ nlen) % 65536 ≠ 65535)
          from fun hn => hn hspec)]
        simpa only [Array.toList_empty] using Deflate.readStoredBytesArr_eq len #[] afterHeader
      · have hspec : (len ^^^ nlen) % 65536 ≠ 65535 := fun hh => h (hcheck.mp hh)
        simp only [ite_eq_right h, ite_eq_left hspec]
        rfl

/-- Satisfiable success check: one arbitrary byte, with a trailing byte left
unconsumed and an exact thirty-two-bit header advance. -/
theorem decompressStored_singleton (byte tail : UInt8) :
    decompressStored ⟨0, 0, [1, 0, 254, 255, byte, tail], 0⟩ =
      .ok ([byte], ⟨0, 0, [tail], 40⟩) := by
  rw [decompressStored_eq]
  rw [Deflate.decompressStored, Deflate.alignToByte_eq]
  dsimp only
  rw [Deflate.readBits16_aligned]
  dsimp only
  rw [Deflate.readBits16_aligned]
  dsimp only
  simp only [UInt8.toNat_ofNat, Nat.reduceAdd, ne_eq]
  exact Deflate.readStoredBytes_aligned [] [byte] [tail] 32

theorem decompressStored_bad_complement :
    decompressStored ⟨0, 0, [1, 0, 255, 255], 0⟩ = .error .badStoredLen := by rfl

theorem decompressStored_truncated_header :
    decompressStored ⟨0, 0, [1, 0, 254], 0⟩ = .error .badStoredLen := by rfl

theorem decompressStored_truncated_payload :
    decompressStored ⟨0, 0, [1, 0, 254, 255], 0⟩ = .error .decodeOverrun := by rfl

end Silmaril.Formats.Compression.Inflate.Manual
