module

public import Silmaril.Formats.Compression.Catalog.Defs
public import Silmaril.Formats.Compression.Format.Thms
public import Silmaril.Formats.Compression.Transform.Thms
public import Silmaril.Formats.Compression.DeflateSpec.Thms
public import Silmaril.Formats.Compression.Inflate.Thms
public import Silmaril.Formats.Compression.GzipHeader.Thms

/-!
# Proofs of the catalogue certificates

Stated in `Silmaril.Formats.Compression.Catalog.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.Catalog

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Catalog
open Silmaril.Formats.Compression.Inflate.Stream

/-! ## DEFLATE -/

theorem deflate_decode_eq_some {history bytes out rest : List UInt8} :
    deflate.decode history bytes = some (out, rest) ↔
      Deflate.deflateTakeWithHistory history bytes = .ok (out, rest) := by
  simp only [Format.decode, deflate, Decoder.ofExcept]
  cases Deflate.deflateTakeWithHistory history bytes <;> simp [Except.toOption]

theorem deflate_decode_nil : deflate.decode [] = Deflate.decoder := by
  show Decoder.ofExcept (Deflate.deflateTakeWithHistory []) = Decoder.ofExcept Deflate.deflateTake
  rw [funext Deflate.withHistory_empty]

theorem deflate_consumes (history : List UInt8) : (deflate.decode history).Consumes :=
  fun _ _ _ h => Deflate.withHistory_suffix (deflate_decode_eq_some.mp h)

theorem deflate_local (history : List UInt8) : (deflate.decode history).Local :=
  fun _ _ _ tail h =>
    deflate_decode_eq_some.mpr (Deflate.deflateTakeWithHistory_append (deflate_decode_eq_some.mp h) tail)

theorem deflate_outputLinear (history : List UInt8) : (deflate.decode history).OutputLinear 2064 :=
  fun _ _ _ h => Deflate.withHistory_output_le (deflate_decode_eq_some.mp h)

theorem deflate_spec : (Capability.spec (Scope.only []) deflateSpec).Holds := by
  intro p hp input out rest
  cases hp
  rw [deflate_decode_nil, Deflate.decoder_eq_some]
  exact DeflateSpec.deflateTake_iff

theorem deflate_all : Capability.All deflateClaims := by
  refine ⟨fun p _ => deflate_consumes p, fun p _ => deflate_local p, deflate_spec,
    Capability.deterministic_of_spec deflate_spec, ?_, ?_, ?_,
    fun p _ => deflate_outputLinear p,
    Inflate.raw_call_output .v131, Inflate.raw_call_output .develop, ?_, ?_, ?_, ?_, trivial⟩
  · show deflate.decode [] _ = _
    rw [deflate_decode_nil, Deflate.decoder_eq_some]
    exact DeflateSpec.deflateTake_complete DeflateSpec.kat_fixed
  · intro history data rest
    exact deflate_decode_eq_some.mpr (Deflate.history_stored history data rest)
  · intro _
    simpa [deflateFixed, deflate_decode_nil] using Deflate.roundTripFixed
  all_goals simp only [Capability.Holds, deflate_decode_nil]
  · exact Inflate.raw_sound .v131
  · exact Inflate.raw_complete .v131
  · exact Inflate.raw_sound .develop
  · exact Inflate.raw_complete .develop

/-! ## zlib -/

theorem checkHeader_suffix {bytes body : List UInt8} {h : ZlibDictionary.Header}
    (hh : ZlibDictionary.checkHeader bytes = some (h, body)) : body <:+ bytes := by
  match bytes, hh with
  | [], hh => simp [ZlibDictionary.checkHeader] at hh
  | [_], hh => simp [ZlibDictionary.checkHeader] at hh
  | cmf :: flg :: rest, hh =>
    simp only [ZlibDictionary.checkHeader] at hh
    split at hh
    · split at hh
      · simp only [Option.some.injEq, Prod.mk.injEq] at hh
        obtain ⟨-, rfl⟩ := hh
        exact ⟨[cmf, flg], rfl⟩
      · split at hh
        · rename_i d0 d1 d2 d3 b
          simp only [Option.some.injEq, Prod.mk.injEq] at hh
          obtain ⟨-, rfl⟩ := hh
          exact ⟨[cmf, flg, d0, d1, d2, d3], rfl⟩
        · simp at hh
    · simp at hh

theorem checkHeader_append {bytes body : List UInt8} {h : ZlibDictionary.Header}
    (tail : List UInt8) (hh : ZlibDictionary.checkHeader bytes = some (h, body)) :
    ZlibDictionary.checkHeader (bytes ++ tail) = some (h, body ++ tail) := by
  match bytes, hh with
  | [], hh => simp [ZlibDictionary.checkHeader] at hh
  | [_], hh => simp [ZlibDictionary.checkHeader] at hh
  | cmf :: flg :: rest, hh =>
    simp only [ZlibDictionary.checkHeader] at hh
    split at hh
    · rename_i hc
      split at hh
      · rename_i hf
        simp only [Option.some.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl⟩ := hh
        simp [ZlibDictionary.checkHeader, hc, hf]
      · rename_i hf
        split at hh
        · rename_i d0 d1 d2 d3 b
          simp only [Option.some.injEq, Prod.mk.injEq] at hh
          obtain ⟨rfl, rfl⟩ := hh
          simp [ZlibDictionary.checkHeader, hc, hf]
        · simp at hh
    · simp at hh

theorem zlibHeader_spec {dictionary : Option (List UInt8)} {bytes history body : List UInt8}
    (hh : zlibParseHeader dictionary bytes = some (history, body)) :
    ∃ header, ZlibDictionary.checkHeader bytes = some (header, body) ∧
      zlibHistory dictionary header = some history := by
  simp only [zlibParseHeader, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hh
  obtain ⟨⟨header, body'⟩, h₁, history', h₂, he⟩ := hh
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨header, h₁, h₂⟩

theorem zlibFraming_consumes (dictionary : Option (List UInt8)) :
    (zlibFraming dictionary).Consumes := by
  refine ⟨fun bytes h rest hh => ?_, fun _ out bytes rest ht => Zlib.framing_consumes.2 (h := ()) ht⟩
  obtain ⟨header, hc, -⟩ := zlibHeader_spec hh
  exact checkHeader_suffix hc

theorem zlibFraming_local (dictionary : Option (List UInt8)) : (zlibFraming dictionary).Local := by
  refine ⟨fun bytes h rest tail hh => ?_,
    fun _ out bytes rest tail ht => Zlib.framing_local.2 (h := ()) tail ht⟩
  obtain ⟨header, hc, hz⟩ := zlibHeader_spec hh
  simp [zlibFraming, zlibParseHeader, checkHeader_append tail hc, hz]

theorem zlibFraming_trailerIs (dictionary : Option (List UInt8)) :
    (zlibFraming dictionary).TrailerIs Zlib.trailer :=
  fun _ _ _ _ ht => Zlib.trailerIs (h := ()) ht

theorem zlib_decode (dictionary : Option (List UInt8)) :
    zlib.decode dictionary = (zlibFraming dictionary).wrapDep deflate.decode :=
  Format.decode_ofDecoder _ _ dictionary

theorem zlibHeader_none (bytes : List UInt8) :
    zlibParseHeader none bytes = (zlibCheckHeader bytes).map ([], ·) := by
  match bytes with
  | [] => rfl
  | [_] => rfl
  | cmf :: flg :: rest =>
    simp only [zlibParseHeader, ZlibDictionary.checkHeader, zlibCheckHeader]
    by_cases hc : cmf &&& 0x0F = 8 ∧ cmf.toNat / 16 ≤ 7 ∧ (cmf.toNat * 256 + flg.toNat) % 31 = 0
    · by_cases hf : flg &&& 0x20 = 0
      · simp [hc, hf, zlibHistory]
      · simp only [hc, hf, and_self, and_false, ↓reduceIte, Option.map_none]
        match rest with
        | _ :: _ :: _ :: _ :: _ => simp [zlibHistory]
        | [] | [_] | [_, _] | [_, _, _] => rfl
    · have : ¬ (cmf &&& 0x0F = 8 ∧ cmf.toNat / 16 ≤ 7 ∧ (cmf.toNat * 256 + flg.toNat) % 31 = 0 ∧
          flg &&& 0x20 = 0) := fun h => hc ⟨h.1, h.2.1, h.2.2.1⟩
      simp only [hc, this, ↓reduceIte, Option.bind_none, Option.map_none]

theorem zlib_decode_none : zlib.decode none = Zlib.decoder := by
  rw [zlib_decode]
  funext bytes
  simp only [Framing.wrapDep, Framing.wrap, zlibFraming, Zlib.framing, zlibHeader_none]
  cases zlibCheckHeader bytes with
  | none => rfl
  | some body => simp [deflate_decode_nil]

theorem zlib_decode_some (dictionary : List UInt8) :
    zlib.decode (some dictionary) = Zlib.takeWithDictionary dictionary := by
  rw [zlib_decode]
  funext bytes
  simp only [Framing.wrapDep, zlibFraming, zlibParseHeader, Zlib.takeWithDictionary,
    ZlibDictionary.takeWithDictionary]
  cases hc : ZlibDictionary.checkHeader bytes with
  | none => rfl
  | some p =>
    obtain ⟨header, body⟩ := p
    simp only [Option.bind_some]
    cases hid : header.dictionaryID with
    | none =>
      simp only [zlibHistory, hid, Option.map_some, deflate_decode_nil, Deflate.decoder,
        Decoder.ofExcept, ZlibDictionary.finish]
      cases Deflate.deflateTake body with
      | error => rfl
      | ok r => obtain ⟨d, a⟩ := r; simp only [Except.toOption]; cases zlibCheckTrailer d a <;> rfl
    | some expected =>
      simp only [zlibHistory, hid]
      by_cases hok : ZlibDictionary.supportedDictionaryProfile header ∧
          ZlibDictionary.dictionaryChecksum dictionary = expected
      · simp only [hok, and_self, ↓reduceIte, Option.map_some, Format.decode, deflate,
          Decoder.ofExcept, ZlibDictionary.finish]
        cases Deflate.deflateTakeWithHistory (ZlibDictionary.history dictionary) body with
        | error => rfl
        | ok r => obtain ⟨d, a⟩ := r; simp only [Except.toOption]; cases zlibCheckTrailer d a <;> rfl
      · simp only [hok, ↓reduceIte, Option.map_none]

theorem zlib_consumes (dictionary : Option (List UInt8)) : (zlib.decode dictionary).Consumes := by
  rw [zlib_decode]
  exact Framing.wrapDep_consumes (zlibFraming_consumes dictionary) deflate_consumes

theorem zlib_local (dictionary : Option (List UInt8)) : (zlib.decode dictionary).Local := by
  rw [zlib_decode]
  exact Framing.wrapDep_local (zlibFraming_local dictionary) deflate_local

theorem zlib_outputLinear (dictionary : Option (List UInt8)) :
    (zlib.decode dictionary).OutputLinear 2064 := by
  rw [zlib_decode]
  exact Framing.wrapDep_outputLinear (zlibFraming_consumes dictionary) deflate_consumes
    deflate_outputLinear

theorem adler32_ref (bytes : List UInt8) : Checksum.adler32.digest bytes = adler32Ref bytes := by
  have h₁ := Checksum.adler32_digest_byteArray ⟨bytes.toArray⟩
  have h₂ := Checksum.adler32_toNat_eq_symbolic ⟨bytes.toArray⟩
  simp only at h₁ h₂
  rw [adler32Ref, ← h₂, h₁, UInt32.ofNat_toNat]

theorem zlib_all : Capability.All zlibClaims := by
  refine ⟨fun p _ => zlib_consumes p, fun p _ => zlib_local p, ?_, adler32_ref, ?_, ?_, ?_, ?_, ?_,
    fun p _ => zlib_outputLinear p,
    Inflate.member_call_output .v131, Inflate.member_call_output .develop,
    ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · intro p _ bytes out rest h
    rw [zlib_decode p] at h
    exact Framing.wrapDep_trailer (zlibFraming_consumes p) deflate_consumes
      (zlibFraming_trailerIs p) h
  · show zlib.decode none _ = _
    rw [zlib_decode_none]; exact Zlib.decoder_sampleHello
  · show zlib.decode (some _) _ = _
    rw [zlib_decode_some]; exact Zlib.dictionary_match
  · intro _; show RoundTrip (zlib.decode none) _
    rw [zlib_decode_none]; exact Zlib.roundTrip
  · intro _; show RoundTrip (zlib.decode none) _
    rw [zlib_decode_none]; exact Zlib.roundTripFixed
  · intro dictionary data rest
    show zlib.decode (some dictionary) _ = _
    rw [zlib_decode_some dictionary]
    have h := Zlib.takeWithDictionary_stored dictionary data rest
    simp only [zlibStoredWithDictionary, zlibDictionaryHeader, List.append_assoc] at h ⊢
    exact h
  all_goals simp only [Capability.Holds, zlib_decode_none]
  · exact Inflate.zlib_sound .v131
  · exact Inflate.shared_zlib ▸ Inflate.member_rejectSound .v131 .zlib
  · exact Inflate.zlib_complete .v131
  · exact Inflate.zlib_sound .develop
  · exact Inflate.shared_zlib ▸ Inflate.member_rejectSound .develop .zlib
  · exact Inflate.zlib_complete .develop

/-! ## gzip -/

theorem gzipMember_decode (p : gzipMember.Params) : gzipMember.decode p = Gzip.decoder :=
  Format.decode_ofDecoder _ _ p

theorem gzip_all : Capability.All gzipClaims := by
  refine ⟨?_, ?_, ?_, Checksum.crc32_digest_eq_spec, ?_, ?_, ?_,
    Inflate.member_call_output .v131, Inflate.member_call_output .develop,
    ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals simp only [Capability.Holds, gzipMember_decode]
  · exact fun _ _ => Gzip.consumes
  · exact fun _ _ => Gzip.local
  · exact fun _ _ _ _ _ h => Gzip.decoder_trailer h
  · exact fun h => GzipHeader.roundTrip h.2
  · exact fun _ => Gzip.roundTripFixed
  · exact fun _ _ _ _ _ h => Gzip.output_le h
  all_goals rw [show gzipMember.decode () = Gzip.decoder from gzipMember_decode _]
  · exact Inflate.gzip_sound .v131
  · exact Inflate.shared_gzip ▸ Inflate.member_rejectSound .v131 .gzip
  · exact Inflate.gzip_complete .v131
  · exact Inflate.gzip_sound .develop
  · exact Inflate.shared_gzip ▸ Inflate.member_rejectSound .develop .gzip
  · exact Inflate.gzip_complete .develop

theorem gzipFile_run (bytes : List UInt8) : gzipFile.run () bytes = Gzip.decoder.members bytes := by
  show (gzipMember.decode ()).members bytes = _
  rw [show gzipMember.decode () = Gzip.decoder from gzipMember_decode _]

/-! ## identity -/

theorem identity_decode (p : identity.Params) (bytes : List UInt8) :
    identity.decode p bytes = some (bytes, []) := rfl

theorem identity_all : Capability.All identityClaims := by
  refine ⟨fun _ _ bytes out rest h => ?_, fun _ _ bytes out rest h => ?_, rfl, trivial⟩
  · simp only [identity_decode, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact List.nil_suffix
  · simp only [identity_decode, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp

theorem identity_not_local : ¬ (identity.decode ()).Local := by
  intro h
  have := (h [0] (identity_decode () [])).symm.trans (identity_decode () [0])
  simp at this

end Silmaril.Proofs.Formats.Compression.Catalog
