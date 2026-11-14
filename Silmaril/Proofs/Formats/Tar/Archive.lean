module

public import Silmaril.Proofs.Formats.Tar.Header
public import Silmaril.Formats.Compression.Gzip.Thms

/-! Proofs for `Silmaril.Formats.Tar.Thms`: archives. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Tar

open Silmaril.Formats.Tar

theorem le_roundUp512 (n : Nat) : n ≤ roundUp512 n := by unfold roundUp512; omega

@[simp] theorem padRecord_length (bytes : List UInt8) :
    (padRecord bytes).length = roundUp512 bytes.length := by
  have := le_roundUp512 bytes.length
  simp [padRecord]; omega

theorem encode_cons {e : Entry} {es : List Entry} {bs : List UInt8}
    (h : encode (e :: es) = some bs) :
    ∃ hdr rest, encodeHeader e = some hdr ∧ encode es = some rest ∧
      bs = hdr ++ padRecord e.data ++ rest := by
  simp only [encode] at h
  cases hh : encodeHeader e with
  | none => simp [hh] at h
  | some hdr =>
    cases hr : encode es with
    | none => simp [hh, hr] at h
    | some rest =>
      simp only [hh, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      exact ⟨hdr, rest, rfl, rfl, h.symm⟩

/-- Decoding an encoded archive ignores whatever follows it. -/
theorem decode_encode_append :
    ∀ {es : List Entry} {bs : List UInt8}, encode es = some bs →
      ∀ tail, decode (bs ++ tail) = some es
  | [], bs, h, tail => by
    simp only [encode, Option.some.injEq] at h
    subst h
    rw [decode, endMarker, List.take_append_of_le_length (by rw [List.length_replicate]; omega),
      List.take_replicate, List.all_replicate]
    simp only [List.length_append, List.length_replicate]
    rw [ite_eq_right (by omega), ite_eq_left (by decide)]
  | e :: es, bs, h, tail => by
    obtain ⟨hdr, rest, hh, hr, rfl⟩ := encode_cons h
    have hlen := encodeHeader_length hh
    have hdata : (padRecord e.data).length = roundUp512 e.data.length := padRecord_length _
    have hle := le_roundUp512 e.data.length
    rw [decode]
    simp only [List.append_assoc, List.length_append, hlen, List.take_left' hlen,
      List.drop_left' hlen, encodeHeader_not_zero hh, parseHeader_encodeHeader hh]
    have htake : (padRecord e.data ++ (rest ++ tail)).take e.data.length = e.data := by
      simp [padRecord]
    simp [htake, decode_encode_append hr tail]

theorem decode_encode {es : List Entry} {bs : List UInt8} (h : encode es = some bs) :
    decode bs = some es := by
  simpa using decode_encode_append h []

/-- `encode` succeeds exactly when every entry is admissible. -/
theorem encode_isSome_iff (es : List Entry) :
    (encode es).isSome ↔ ∀ e ∈ es, e.admissible = true := by
  induction es with
  | nil => simp [encode]
  | cons e es ih =>
    constructor
    · intro h
      obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨hdr, rest, hh, hr, -⟩ := encode_cons hbs
      have hes := ih.mp (by simp [hr])
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (encodeHeader_eq_some hh).1
      · exact hes x hx
    · intro h
      obtain ⟨hdr, hh⟩ := Option.isSome_iff_exists.mp (encodeHeader_isSome (h e (by simp)))
      obtain ⟨rest, hr⟩ := Option.isSome_iff_exists.mp
        (ih.mpr fun x hx => h x (List.mem_cons_of_mem e hx))
      simp [encode, hh, hr]

theorem encode_length {es : List Entry} {bs : List UInt8} (h : encode es = some bs) :
    bs.length % 512 = 0 := by
  induction es generalizing bs with
  | nil => simp only [encode, Option.some.injEq] at h; subst h; rw [endMarker, List.length_replicate]
  | cons e es ih =>
    obtain ⟨hdr, rest, hh, hr, rfl⟩ := encode_cons h
    have := ih hr
    simp only [List.length_append, encodeHeader_length hh, padRecord_length, roundUp512]
    omega

theorem decode_blockArchive {es : List Entry} {bs : List UInt8} (h : encode es = some bs)
    (factor : Nat) : decode (blockArchive factor bs) = some es := by
  simp only [blockArchive]
  split
  · exact decode_encode h
  · exact decode_encode_append h _

theorem decodeArchive_encodeArchive {es : List Entry} {bs : ByteArray}
    (h : encodeArchive es = some bs) : decodeArchive bs = some es := by
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp h
  simpa [decodeArchive] using decode_encode hl

theorem decompressGz_compressGz {es : List Entry} {gz : ByteArray}
    (h : compressGz es = some gz) : decompressGz gz = some es := by
  obtain ⟨bs, hbs, rfl⟩ := Option.map_eq_some_iff.mp h
  simp [decompressGz, Silmaril.Formats.Compression.Gzip.decompress_compress, decodeArchive_encodeArchive hbs]

end Silmaril.Proofs.Formats.Tar
