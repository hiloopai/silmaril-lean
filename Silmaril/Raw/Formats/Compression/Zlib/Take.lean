module

public import Silmaril.Formats.Compression.Zlib.Take
public import Silmaril.Raw.Formats.Compression.Zlib.Basic

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Zlib.Take`. -/

@[expose] public section

namespace Silmaril.Formats.Compression

open Deflate

/-- Checking a zlib header only removes a prefix of the input. -/
theorem zlibCheckHeader_suffix {bytes rest : List UInt8}
    (h : zlibCheckHeader bytes = some rest) : rest <:+ bytes := by
  match bytes with
  | [] | [_] => simp [zlibCheckHeader] at h
  | cmf :: flg :: body =>
    simp only [zlibCheckHeader] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst rest
      exact ⟨[cmf, flg], rfl⟩
    · simp at h

/-- The take-style trailer checker consumes exactly four checksum bytes, and
those bytes are the existing zlib trailer of the output it accepted. -/
theorem zlibCheckTrailer_spec {data afterData tail : List UInt8}
    (h : zlibCheckTrailer data afterData = some tail) :
    afterData = (zlibTrailer ⟨data.toArray⟩).data.toList ++ tail := by
  match afterData with
  | [] | [_] | [_, _] | [_, _, _] => simp [zlibCheckTrailer] at h
  | a0 :: a1 :: a2 :: a3 :: rest =>
    simp only [zlibCheckTrailer] at h
    split at h
    · next hcheck =>
      simp only [Option.some.injEq] at h
      subst tail
      have htrailer : (zlibTrailer ⟨data.toArray⟩).data.toList =
          be32Bytes (adler32 ⟨data.toArray⟩).toNat := by simp [zlibTrailer]
      rw [htrailer, ← hcheck, be32Bytes_be32Val]
      rfl
    · simp at h

/-- Soundness retains the exact member boundary: a successful member ends with
the checksum of its returned output, followed by the untouched input suffix. -/
theorem zlibTake_trailer {bytes data tail : List UInt8}
    (h : zlibTake bytes = some (data, tail)) :
    ∃ pre, bytes = pre ++ ((zlibTrailer ⟨data.toArray⟩).data.toList ++ tail) := by
  unfold zlibTake at h
  cases hh : zlibCheckHeader bytes with
  | none => simp [hh] at h
  | some body =>
    simp only [hh] at h
    cases hd : deflateTake body with
    | error error => simp [hd] at h
    | ok pair =>
      obtain ⟨out, afterData⟩ := pair
      simp only [hd] at h
      cases ht : zlibCheckTrailer out afterData with
      | none => simp [ht] at h
      | some rest =>
        simp only [ht, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨header, hheader⟩ := zlibCheckHeader_suffix hh
        obtain ⟨compressed, hcompressed⟩ := deflateTake_suffix hd
        refine ⟨header ++ compressed, ?_⟩
        rw [← hheader, ← hcompressed, zlibCheckTrailer_spec ht, List.append_assoc]

/-- A successful call returns an actual suffix of the offered input. -/
theorem zlibTake_suffix {bytes data tail : List UInt8}
    (h : zlibTake bytes = some (data, tail)) : tail <:+ bytes := by
  obtain ⟨pre, hpre⟩ := zlibTake_trailer h
  exact ⟨pre ++ (zlibTrailer ⟨data.toArray⟩).data.toList,
    by simpa only [List.append_assoc] using hpre.symm⟩

/-- Appending bytes after a correct Adler-32 trailer leaves them untouched. -/
theorem zlibCheckTrailer_zlibTrailer_append (data : ByteArray) (tail : List UInt8) :
    zlibCheckTrailer data.data.toList ((zlibTrailer data).data.toList ++ tail) =
      some tail := by
  simp only [zlibTrailer, List.toList_toArray, zlibCheckTrailer, be32Bytes,
    List.cons_append, List.nil_append]
  rw [be32Val_be32Bytes]
  have hmod : (adler32 data).toNat % 4294967296 = (adler32 data).toNat := by
    have h := (adler32 data).toNat_lt_size
    simp only [UInt32.size] at h
    omega
  simp [hmod]

/-- Every stored zlib encoding is accepted as one member, retaining an arbitrary
suffix. The payload can span arbitrarily many stored DEFLATE blocks. -/
theorem zlibTake_zlibCompress_append (data : ByteArray) (tail : List UInt8) :
    zlibTake ((zlibCompress data).data.toList ++ tail) =
      some (data.data.toList, tail) := by
  rw [zlibCompress_toList]
  simp only [List.cons_append, List.nil_append, List.append_assoc, zlibTake,
    zlibCheckHeader]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide : ((0x78 : UInt8) &&& 0x0F = 8 ∧
    (0x78 : UInt8).toNat / 16 ≤ 7 ∧
    ((0x78 : UInt8).toNat * 256 + (0x01 : UInt8).toNat) % 31 = 0 ∧
      (0x01 : UInt8) &&& 0x20 = 0)))]
  dsimp only
  rw [deflateTake_storedBytes]
  dsimp only
  have htrailer : be32Bytes (adler32 data).toNat = (zlibTrailer data).data.toList := by
    simp [zlibTrailer]
  rw [htrailer, zlibCheckTrailer_zlibTrailer_append]

theorem zlibTake_zlibCompress (data : ByteArray) :
    zlibTake (zlibCompress data).data.toList = some (data.data.toList, []) := by
  simpa only [List.append_nil] using zlibTake_zlibCompress_append data []

theorem exactMember_trailer (data rest : List UInt8) :
    exactMember (match zlibCheckTrailer data rest with
      | none => none
      | some tail => some (data, tail)) =
      match rest with
      | [a0, a1, a2, a3] =>
        if be32Val a0 a1 a2 a3 = (adler32 ⟨data.toArray⟩).toNat then
          some ⟨data.toArray⟩ else none
      | _ => none := by
  match rest with
  | [] | [_] | [_, _] | [_, _, _] => rfl
  | a0 :: a1 :: a2 :: a3 :: tail =>
    by_cases h : be32Val a0 a1 a2 a3 = (adler32 ⟨data.toArray⟩).toNat
    all_goals cases tail <;> simp [zlibCheckTrailer, exactMember, h]

/-- The new suffix-preserving specification agrees exactly with the existing
one-shot specification after imposing its end-of-input requirement. -/
theorem zlibDecompress_eq_exactMember (bytes : ByteArray) :
    zlibDecompress bytes = exactMember (zlibTake bytes.data.toList) := by
  unfold zlibDecompress zlibTake
  cases hh : zlibCheckHeader bytes.data.toList with
  | none => rfl
  | some body =>
    simp only []
    cases hd : deflateTake body with
    | error e => rfl
    | ok p =>
      rcases p with ⟨data, rest⟩
      simp only []
      exact (exactMember_trailer data rest).symm

end Silmaril.Formats.Compression
