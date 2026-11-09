module

public import Silmaril.Formats.Compression.Gzip.Defs
public import Silmaril.Formats.Compression.Checksum.Thms
public import Silmaril.Formats.Compression.Deflate.Thms
public import Silmaril.Raw.Formats.Compression.Gzip.Basic

/-! Proofs for `Silmaril.Formats.Compression.Gzip.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.Gzip

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Gzip

theorem member_eq_decoder : member = decoder := by
  funext bytes
  simp only [member, gzipMember, Framing.wrap, framing]
  split
  · simp only [checkHeader]
    split
    · rfl
    · generalize gzipSkipHeaderFields _ _ _ = o
      cases o with
      | none => rfl
      | some body =>
        simp only [Option.map_some, Decoder.ofExcept]
        generalize Deflate.deflateTake body = t
        rcases t with e | ⟨d, r⟩
        · rfl
        · simp only [Except.toOption]
          generalize gzipCheckTrailer d r = q
          cases q <;> rfl
  · rename_i hne
    have hnone : checkHeader bytes = none := by
      unfold checkHeader
      split
      · exact (hne _ _ _ _ _ _ _ _ _ rfl).elim
      · rfl
    rw [hnone]

theorem gzipTrailer_toList (out : List UInt8) :
    (gzipTrailer ⟨out.toArray⟩).data.toList = trailer out := by
  have h := Checksum.crc32_digest ⟨out.toArray⟩
  simp only at h
  simp [gzipTrailer, trailer, h, ByteArray.size]

theorem trailerIs : framing.TrailerIs trailer := by
  intro _ out bytes rest h
  rw [gzipCheckTrailer_spec h, gzipTrailer_toList]

theorem framing_consumes : framing.Consumes := by
  refine ⟨fun bytes h rest hh => ?_, fun _ out _ _ ht => ⟨trailer out, (trailerIs ht).symm⟩⟩
  simp only [framing, checkHeader] at hh
  split at hh
  · split at hh
    · simp at hh
    · obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp hh
      cases he
      exact (gzipSkipHeaderFields_suffix hr).trans ⟨[31, 139, _, _, _, _, _, _, _, _], rfl⟩
  · simp at hh

theorem consumes : decoder.Consumes :=
  Framing.wrap_consumes framing_consumes Deflate.consumes

theorem decoder_trailer {bytes out rest : List UInt8} (h : decoder bytes = some (out, rest)) :
    ∃ pre, bytes = pre ++ (trailer out ++ rest) :=
  Framing.wrap_trailer framing_consumes Deflate.consumes trailerIs h

theorem compress_eq (data : ByteArray) : (compress data).data.toList = encoder data.data.toList := by
  rw [compress, gzipCompress_toList]
  have h := Checksum.crc32_digest data
  simp [Framing.encode, header, gzipMagic, trailer, h]

theorem roundTrip : RoundTrip decoder encoder := by
  intro data rest
  have h := gzipMember_gzipCompress_append ⟨data.toArray⟩ rest
  rw [compress_eq] at h
  simpa [← member_eq_decoder] using h

theorem gzipMembers_eq (fuel : Nat) (bytes acc : List UInt8) :
    gzipMembers fuel bytes acc = member.membersFuel fuel bytes acc := by
  induction fuel generalizing bytes acc with
  | zero => rfl
  | succ n ih => simp only [gzipMembers, Decoder.membersFuel, ih]; rfl

theorem decompress_eq (bytes : ByteArray) :
    decompress bytes = (decoder.members bytes.data.toList).map (fun out => ⟨out.toArray⟩) := by
  rw [decompress, gzipDecompress, gzipMembers_eq, member_eq_decoder, Decoder.members,
    byteArray_size_toList]
  cases decoder.membersFuel (bytes.data.toList.length + 1) bytes.data.toList [] <;> rfl

theorem encoder_ne_nil (data : List UInt8) : encoder data ≠ [] := by
  simp [Framing.encode, header, gzipMagic]

end Silmaril.Proofs.Formats.Compression.Gzip
