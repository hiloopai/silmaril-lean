module

public import Silmaril.Formats.Compression.Zlib.Basic
public import Silmaril.Raw.Formats.Compression.Bits.ByteFields
public import Silmaril.Raw.Formats.Compression.Checksum.Adler32
public import Silmaril.Raw.Formats.Compression.Deflate.Stored

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Zlib.Basic`. -/

@[expose] public section

namespace Silmaril.Formats.Compression

open Deflate (storedBytes compressStored deflateTake deflateTake_storedBytes deflateTake_suffix)

/-! ### Round trip and trailer soundness -/

theorem zlibCompress_toList (data : ByteArray) :
    (zlibCompress data).data.toList =
      [0x78, 0x01] ++ (storedBytes data.data.toList ++ be32Bytes (adler32 data).toNat) := by
  simp [zlibCompress, zlibHeader, zlibTrailer, compressStored]

theorem zlibDecompress_zlibCompress (data : ByteArray) :
    zlibDecompress (zlibCompress data) = some data := by
  rw [zlibDecompress, zlibCompress_toList]
  simp only [List.cons_append, List.nil_append, zlibCheckHeader]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide : ((0x78 : UInt8) &&& 0x0F = 8 ∧
    (0x78 : UInt8).toNat / 16 ≤ 7 ∧
    ((0x78 : UInt8).toNat * 256 + (0x01 : UInt8).toNat) % 31 = 0 ∧ (0x01 : UInt8) &&& 0x20 = 0)))]
  dsimp only
  rw [deflateTake_storedBytes]
  simp only [be32Bytes]
  rw [be32Val_be32Bytes]
  have h1 : (adler32 ⟨data.data.toList.toArray⟩).toNat % 4294967296
      = (adler32 ⟨data.data.toList.toArray⟩).toNat := by
    have h := (adler32 ⟨data.data.toList.toArray⟩).toNat_lt_size
    simp only [UInt32.size] at h
    omega
  rw [h1]
  simp

/-- Trailer soundness (RFC 1950 §2.2): if `zlibDecompress` accepts a stream, the
stream really ends with the Adler-32 of the data it returned. The decoder
therefore cannot accept a stream whose trailer disagrees with its output. -/
theorem zlibDecompress_trailer_sound {c out : ByteArray} (h : zlibDecompress c = some out) :
    ∃ pre, c.data.toList = pre ++ (zlibTrailer out).data.toList := by
  rw [zlibDecompress] at h
  cases hh : zlibCheckHeader c.data.toList with
  | none => rw [hh] at h; simp at h
  | some body =>
    rw [hh] at h
    dsimp only at h
    cases hd : deflateTake body with
    | error e => rw [hd] at h; simp at h
    | ok p =>
      obtain ⟨data, afterData⟩ := p
      rw [hd] at h
      dsimp only at h
      match hm : afterData with
      | [] => simp at h
      | [a0] => simp at h
      | [a0, a1] => simp at h
      | [a0, a1, a2] => simp at h
      | (a0 :: a1 :: a2 :: a3 :: x :: xs) => simp at h
      | [a0, a1, a2, a3] =>
        dsimp only at h
        split at h
        · next hadler =>
          simp only [Option.some.injEq] at h
          subst h
          -- the header is two bytes, the remainder a suffix of the body
          obtain ⟨hpre, hbody⟩ : ∃ p, c.data.toList = p ++ body := by
            match hc : c.data.toList with
            | [] => rw [hc] at hh; simp [zlibCheckHeader] at hh
            | [x] => rw [hc] at hh; simp [zlibCheckHeader] at hh
            | (cmf :: flg :: r) =>
              rw [hc] at hh
              simp only [zlibCheckHeader] at hh
              split at hh
              · simp only [Option.some.injEq] at hh
                exact ⟨[cmf, flg], by simp [hh]⟩
              · simp at hh
          obtain ⟨q, hq⟩ := deflateTake_suffix hd
          refine ⟨hpre ++ q, ?_⟩
          rw [hbody, ← hq]
          have hz : (zlibTrailer ⟨data.toArray⟩).data.toList
              = be32Bytes (adler32 ⟨data.toArray⟩).toNat := by simp [zlibTrailer]
          rw [hz, ← hadler, be32Bytes_be32Val, List.append_assoc]
        · simp at h

theorem zlibCompresses_iff (data c : ByteArray) :
    ZlibCompresses data c ↔ zlibDecompress c = some data := Iff.rfl

theorem zlibCompress_sound (data : ByteArray) : ZlibCompresses data (zlibCompress data) :=
  zlibDecompress_zlibCompress data

/-- Every byte string has a zlib encoding, i.e. `zlibDecompress` is surjective. -/
theorem zlibDecompress_surjective (data : ByteArray) : ∃ c, zlibDecompress c = some data :=
  ⟨zlibCompress data, zlibDecompress_zlibCompress data⟩

/-- A stream that asks for a preset dictionary (FDICT = 1, RFC 1950 §2.2) is
rejected rather than mis-parsed: its DICTID is never fed to the DEFLATE decoder. -/
theorem zlibDecompress_fdict (cmf flg : UInt8) (rest : List UInt8) (h : flg &&& 0x20 ≠ 0) :
    zlibDecompress ⟨(cmf :: flg :: rest).toArray⟩ = none := by
  have hl : (⟨(cmf :: flg :: rest).toArray⟩ : ByteArray).data.toList = cmf :: flg :: rest := by
    simp
  rw [zlibDecompress, hl]
  simp only [zlibCheckHeader]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [h]))]

end Silmaril.Formats.Compression
