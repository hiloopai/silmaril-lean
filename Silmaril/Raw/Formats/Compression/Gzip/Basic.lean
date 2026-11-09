module

public import Silmaril.Formats.Compression.Gzip.Basic
public import Silmaril.Raw.Formats.Compression.Bits.ByteFields
public import Silmaril.Raw.Formats.Compression.Checksum.CRC32
public import Silmaril.Raw.Formats.Compression.Deflate.Stored

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Gzip.Basic`. -/

@[expose] public section

namespace Silmaril.Formats.Compression

open Deflate (storedBytes compressStored deflateTake deflateTake_storedBytes)

/-! ### Round trip and multi-member decoding -/

theorem gzipCompress_toList (data : ByteArray) :
    (gzipCompress data).data.toList =
      [0x1F, 0x8B, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF] ++
        (storedBytes data.data.toList ++
          (le32Bytes (crc32 data).toNat ++ le32Bytes data.size)) := by
  simp [gzipCompress, gzipHeader, gzipMagic, gzipTrailer, compressStored]

theorem gzipMember_gzipCompress_append (data : ByteArray) (tail : List UInt8) :
    gzipMember ((gzipCompress data).data.toList ++ tail) = some (data.data.toList, tail) := by
  rw [gzipCompress_toList]
  simp only [List.cons_append, List.nil_append, List.append_assoc, gzipMember,
    gzipSkipHeaderFields, gzipSkipOptional, gzipCheckTrailer, gzipFEXTRA, gzipFNAME,
    gzipFCOMMENT, gzipFHCRC, gzipFRESERVED]
  simp only [show ((0 : UInt8) &&& 224) = 0 from rfl, show ((0 : UInt8) &&& 4) = 0 from rfl,
    show ((0 : UInt8) &&& 8) = 0 from rfl, show ((0 : UInt8) &&& 16) = 0 from rfl,
    show ((0 : UInt8) &&& 2) = 0 from rfl, ne_eq, not_true_eq_false, false_or, reduceIte]
  rw [deflateTake_storedBytes]
  simp only [le32Bytes, List.cons_append, List.nil_append]
  rw [le32Val_le32Bytes, le32Val_le32Bytes]
  have h1 : (crc32 ⟨data.data.toList.toArray⟩).toNat % 4294967296
      = (crc32 ⟨data.data.toList.toArray⟩).toNat := by
    have h := (crc32 ⟨data.data.toList.toArray⟩).toNat_lt_size
    simp only [UInt32.size] at h
    omega
  have h2 : data.size % 4294967296 = data.data.toList.length % 4294967296 := by simp
  rw [h1, h2]
  simp

theorem gzipMember_gzipCompress (data : ByteArray) :
    gzipMember (gzipCompress data).data.toList = some (data.data.toList, []) := by
  simpa using gzipMember_gzipCompress_append data []

theorem gzipDecompress_gzipCompress (data : ByteArray) :
    gzipDecompress (gzipCompress data) = some data := by
  rw [gzipDecompress]
  simp only [gzipMembers, gzipMember_gzipCompress]
  simp

/-- Multi-member streams (RFC 1952 §2.2): the members' data are concatenated. -/
theorem gzipDecompress_append (a b : ByteArray) :
    gzipDecompress (gzipCompress a ++ gzipCompress b) = some (a ++ b) := by
  have hlist : (gzipCompress a ++ gzipCompress b).data.toList
      = (gzipCompress a).data.toList ++ (gzipCompress b).data.toList :=
    ByteArray.toList_data_append
  have hb : (gzipCompress b).data.toList =
      31 :: 139 :: 8 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 255 ::
        (Deflate.storedBytes b.data.toList ++
          (le32Bytes (crc32 b).toNat ++ le32Bytes b.size)) := by
    rw [gzipCompress_toList]; rfl
  have hb10 : 10 ≤ (gzipCompress b).data.toList.length := by rw [hb]; simp
  have hs : (gzipCompress a ++ gzipCompress b).size
      = (gzipCompress a).data.toList.length + (gzipCompress b).data.toList.length := by
    rw [byteArray_size_toList, hlist, List.length_append]
  obtain ⟨n, hn⟩ : ∃ n, (gzipCompress a ++ gzipCompress b).size = n + 2 :=
    ⟨(gzipCompress a ++ gzipCompress b).size - 2, by omega⟩
  rw [gzipDecompress, hn, gzipMembers, hlist,
    gzipMember_gzipCompress_append a ((gzipCompress b).data.toList), hb]
  simp only []
  rw [← hb, gzipMembers, gzipMember_gzipCompress]
  simp only [List.nil_append, Option.some.injEq]
  rw [← ByteArray.toList_data_append]

theorem gzipCompresses_iff (data c : ByteArray) :
    GzipCompresses data c ↔ gzipDecompress c = some data := Iff.rfl

theorem gzipCompress_sound (data : ByteArray) : GzipCompresses data (gzipCompress data) :=
  gzipDecompress_gzipCompress data

/-- Every byte string has a gzip encoding, i.e. `gzipDecompress` is surjective. -/
theorem gzipDecompress_surjective (data : ByteArray) : ∃ c, gzipDecompress c = some data :=
  ⟨gzipCompress data, gzipDecompress_gzipCompress data⟩

/-! ### Trailer soundness

The decoder consumes a prefix of the stream (`Deflate.deflateTake_suffix`, plus
the header-skipping lemmas below), so the bytes it compares against the CRC-32
and ISIZE really are the last eight bytes of the member. -/

theorem gzipDropZeroTerminated_suffix : ∀ {bs r : List UInt8},
    gzipDropZeroTerminated bs = some r → r <:+ bs := by
  intro bs
  induction bs with
  | nil => intro r h; simp [gzipDropZeroTerminated] at h
  | cons x xs ih =>
    intro r h
    by_cases hx : x = 0
    · subst hx
      rw [gzipDropZeroTerminated.eq_2] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨[0], rfl⟩
    · rw [gzipDropZeroTerminated.eq_3 x xs (fun he => hx he)] at h
      exact (ih h).trans ⟨[x], rfl⟩

theorem gzipDropExact_suffix {n : Nat} {bs r : List UInt8} (h : gzipDropExact n bs = some r) :
    r <:+ bs := by
  unfold gzipDropExact at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨bs.take n, by simp⟩
  · simp at h

theorem gzipSkipOptional_suffix {flg : UInt8} {bs r : List UInt8}
    (h : gzipSkipOptional flg bs = some r) : r <:+ bs := by
  unfold gzipSkipOptional at h
  dsimp only at h
  split at h
  · simp at h
  · next bs1 hbs1 =>
    have h1 : bs1 <:+ bs := by
      split at hbs1
      · split at hbs1
        · exact (gzipDropExact_suffix hbs1).trans
            ((List.suffix_cons _ _).trans (List.suffix_cons _ _))
        · simp at hbs1
      · simp only [Option.some.injEq] at hbs1
        subst hbs1
        exact List.suffix_rfl
    split at h
    · simp at h
    · next bs2 hbs2 =>
      have h2 : bs2 <:+ bs1 := by
        split at hbs2
        · exact gzipDropZeroTerminated_suffix hbs2
        · simp only [Option.some.injEq] at hbs2
          subst hbs2
          exact List.suffix_rfl
      have h3 : r <:+ bs2 := by
        split at h
        · exact gzipDropZeroTerminated_suffix h
        · simp only [Option.some.injEq] at h
          subst h
          exact List.suffix_rfl
      exact (h3.trans h2).trans h1

theorem gzipSkipHeaderFields_suffix {flg : UInt8} {member afterFixed r : List UInt8}
    (h : gzipSkipHeaderFields flg member afterFixed = some r) : r <:+ afterFixed := by
  unfold gzipSkipHeaderFields at h
  split at h
  · simp at h
  · next afterOpt hso =>
    have h1 : afterOpt <:+ afterFixed := gzipSkipOptional_suffix hso
    split at h
    · split at h
      · dsimp only at h
        split at h
        · simp only [Option.some.injEq] at h
          subst h
          exact (List.suffix_cons _ _).trans ((List.suffix_cons _ _).trans h1)
        · simp at h
      · simp at h
    · simp only [Option.some.injEq] at h
      subst h
      exact h1

theorem gzipCheckTrailer_spec {data afterData rest : List UInt8}
    (h : gzipCheckTrailer data afterData = some rest) :
    afterData = (gzipTrailer ⟨data.toArray⟩).data.toList ++ rest := by
  unfold gzipCheckTrailer at h
  split at h
  · next c0 c1 c2 c3 i0 i1 i2 i3 rest' =>
    split at h
    · next hcheck =>
      simp only [Option.some.injEq] at h
      subst h
      have ht : (gzipTrailer ⟨data.toArray⟩).data.toList
          = le32Bytes (crc32 ⟨data.toArray⟩).toNat ++ le32Bytes data.length := by
        have hsize : (⟨data.toArray⟩ : ByteArray).size = data.length := by
          simp [ByteArray.size]
        simp [gzipTrailer, hsize]
      rw [ht, ← hcheck.1, le32Bytes_le32Val, ← le32Bytes_mod data.length, ← hcheck.2,
        le32Bytes_le32Val]
      rfl
    · simp at h
  · simp at h

/-- Trailer soundness (RFC 1952 §2.3.1): a member that `gzipMember` accepts ends
with the gzip trailer — CRC-32 and ISIZE — of the data it returned, followed by
the rest of the stream. A member whose trailer disagrees with its payload cannot
be accepted. -/
theorem gzipMember_trailer {bs data rest : List UInt8} (h : gzipMember bs = some (data, rest)) :
    ∃ pre, bs = pre ++ ((gzipTrailer ⟨data.toArray⟩).data.toList ++ rest) := by
  unfold gzipMember at h
  split at h
  · next bs' cm flg mt0 mt1 mt2 mt3 xfl os rest0 =>
    split at h
    · simp at h
    · split at h
      · simp at h
      · next body hhdr =>
        have h1 : body <:+ rest0 := gzipSkipHeaderFields_suffix hhdr
        split at h
        · simp at h
        · next data' afterData hdt =>
          split at h
          · simp at h
          · next rest' hct =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have h2 : afterData <:+ body := Deflate.deflateTake_suffix hdt
            obtain ⟨p, hp⟩ := (h2.trans h1)
            refine ⟨31 :: 139 :: cm :: flg :: mt0 :: mt1 :: mt2 :: mt3 :: xfl :: os :: p, ?_⟩
            rw [← gzipCheckTrailer_spec hct, ← hp]
            rfl
  · simp at h

end Silmaril.Formats.Compression
