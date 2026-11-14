module

public import Silmaril.Formats.Compression.Zlib.Defs
public import Silmaril.Formats.Compression.Checksum.Thms
public import Silmaril.Formats.Compression.Deflate.Thms
public import Silmaril.Raw.Formats.Compression.Zlib.Take
public import Silmaril.Proofs.Formats.Compression.Bounds

/-! Proofs for `Silmaril.Formats.Compression.Zlib.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.Zlib

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Zlib

theorem take_eq_decoder : take = decoder := by
  funext bytes
  simp only [take, zlibTake, Framing.wrap, framing, Decoder.ofExcept]
  cases zlibCheckHeader bytes with
  | none => rfl
  | some body =>
    simp only [Option.map_some]
    cases Deflate.deflateTake body with
    | error e => rfl
    | ok p =>
      obtain ⟨d, r⟩ := p
      simp only [Except.toOption]
      cases zlibCheckTrailer d r <;> rfl

theorem zlibTrailer_toList (out : List UInt8) :
    (zlibTrailer ⟨out.toArray⟩).data.toList = trailer out := by
  have h := Checksum.adler32_digest_byteArray ⟨out.toArray⟩
  simp only at h
  simp [zlibTrailer, trailer, h]

theorem header_some {bytes : List UInt8} {h : Unit} {rest : List UInt8} :
    framing.header bytes = some (h, rest) ↔ zlibCheckHeader bytes = some rest := by
  cases h
  simp only [framing]
  cases zlibCheckHeader bytes <;> simp

theorem trailerIs : framing.TrailerIs trailer := by
  intro _ out bytes rest h
  rw [zlibCheckTrailer_spec h, zlibTrailer_toList]

theorem framing_consumes : framing.Consumes :=
  ⟨fun _ _ _ hh => zlibCheckHeader_suffix (header_some.mp hh),
   fun _ out _ _ ht => ⟨trailer out, (trailerIs ht).symm⟩⟩

theorem consumes : decoder.Consumes :=
  Framing.wrap_consumes framing_consumes Deflate.consumes

theorem decoder_trailer {bytes out rest : List UInt8} (h : decoder bytes = some (out, rest)) :
    ∃ pre, bytes = pre ++ (trailer out ++ rest) :=
  Framing.wrap_trailer framing_consumes Deflate.consumes trailerIs h

theorem writes : framing.Writes zlibHeader trailer := by
  intro rest
  refine ⟨(), header_some.mpr rfl, fun out tail => ?_⟩
  have h := zlibCheckTrailer_zlibTrailer_append ⟨out.toArray⟩ tail
  simp only [zlibTrailer_toList] at h
  exact h

theorem roundTrip : RoundTrip decoder encoder :=
  Framing.wrap_roundTrip writes Deflate.roundTrip

theorem framing_local : framing.Local := by
  refine ⟨fun bytes h rest tail hh => ?_, fun h out bytes rest tail ht => ?_⟩
  · rw [header_some] at hh ⊢
    match bytes, hh with
    | [], hh | [_], hh => simp [zlibCheckHeader] at hh
    | cmf :: flg :: body, hh =>
      simp only [zlibCheckHeader, List.cons_append] at hh ⊢
      split at hh <;> simp_all
  · simp only [framing] at ht ⊢
    match bytes, ht with
    | [], ht | [_], ht | [_, _], ht | [_, _, _], ht => simp [zlibCheckTrailer] at ht
    | a0 :: a1 :: a2 :: a3 :: r, ht =>
      simp only [zlibCheckTrailer, List.cons_append] at ht ⊢
      split at ht <;> simp_all

theorem local_of_deflate (h : Deflate.decoder.Local) : decoder.Local :=
  Framing.wrap_local framing_local h

theorem decompress_eq (bytes : ByteArray) :
    decompress bytes = (decoder.whole bytes.data.toList).map (fun out => ⟨out.toArray⟩) := by
  rw [decompress, zlibDecompress_eq_exactMember, ← take_eq_decoder]
  unfold Decoder.whole exactMember take
  generalize zlibTake bytes.data.toList = r
  rcases r with _ | ⟨out, _ | ⟨b, bs⟩⟩ <;> rfl

theorem compress_eq (data : ByteArray) : (compress data).data.toList = encoder data.data.toList := by
  rw [compress, zlibCompress_toList]
  have h := Checksum.adler32_digest_byteArray data
  simp [Framing.encode, zlibHeader, trailer, h]

/-! ### Output bounds -/

theorem outputLe : Bounds.OutputLe decoder 2064 :=
  Bounds.wrap_outputLe framing_consumes Bounds.decoder_outputLe

theorem decompress_output_le {bytes out : ByteArray} (h : decompress bytes = some out) :
    out.size ≤ 2064 * bytes.size := by
  rw [decompress_eq] at h
  unfold Decoder.whole at h
  split at h
  · next o heq =>
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have := outputLe heq
    have h1 : (⟨o.toArray⟩ : ByteArray).size = o.length := by simp [ByteArray.size]
    have h2 : bytes.data.toList.length = bytes.size := Array.length_toList
    omega
  · cases h

end Silmaril.Proofs.Formats.Compression.Zlib
