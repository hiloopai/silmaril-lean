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

/-! ### The header and trailer ignore appended bytes -/

theorem gzipDropZeroTerminated_append (tail : List UInt8) : ∀ {bs r : List UInt8},
    gzipDropZeroTerminated bs = some r → gzipDropZeroTerminated (bs ++ tail) = some (r ++ tail)
  | [], r, h => by simp [gzipDropZeroTerminated] at h
  | x :: xs, r, h => by
    by_cases hx : x = 0
    · subst hx
      rw [gzipDropZeroTerminated.eq_2] at h
      cases h
      rw [List.cons_append, gzipDropZeroTerminated.eq_2]
    · rw [gzipDropZeroTerminated.eq_3 x xs (fun he => hx he)] at h
      rw [List.cons_append, gzipDropZeroTerminated.eq_3 x _ (fun he => hx he)]
      exact gzipDropZeroTerminated_append tail h

theorem gzipDropExact_append {n : Nat} {bs r : List UInt8} (h : gzipDropExact n bs = some r)
    (tail : List UInt8) : gzipDropExact n (bs ++ tail) = some (r ++ tail) := by
  unfold gzipDropExact at h ⊢
  split at h
  · next hn =>
    cases h
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by simp only [List.length_append]; omega)),
      List.drop_append_of_le_length hn]
  · cases h

theorem gzipSkipOptional_append {flg : UInt8} {bs r : List UInt8}
    (h : gzipSkipOptional flg bs = some r) (tail : List UInt8) :
    gzipSkipOptional flg (bs ++ tail) = some (r ++ tail) := by
  unfold gzipSkipOptional at h ⊢
  dsimp only at h ⊢
  have hz : ∀ {x y : List UInt8}, some x = some y → some (x ++ tail) = some (y ++ tail) := by
    intro x y hxy; cases hxy; rfl
  by_cases hx : flg &&& gzipFEXTRA = 0 <;>
  by_cases hn : flg &&& gzipFNAME = 0 <;>
  by_cases hc : flg &&& gzipFCOMMENT = 0 <;>
  simp only [hx, hn, hc, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at h ⊢ <;>
  first
  | (match bs, h with
     | x0 :: x1 :: r', h =>
       simp only [List.cons_append]
       split at h
       · cases h
       next bs1 hbs1 =>
       rw [gzipDropExact_append hbs1 tail]
       dsimp only
       first
       | exact hz h
       | exact gzipDropZeroTerminated_append tail h
       | (split at h
          · cases h
          next bs2 hbs2 =>
          rw [gzipDropZeroTerminated_append tail hbs2]
          first
          | exact hz h
          | exact gzipDropZeroTerminated_append tail h))
  | (first
     | exact hz h
     | exact gzipDropZeroTerminated_append tail h
     | (split at h
        · cases h
        next bs2 hbs2 =>
        rw [gzipDropZeroTerminated_append tail hbs2]
        first
        | exact hz h
        | exact gzipDropZeroTerminated_append tail h))

theorem gzipSkipHeaderFields_append {flg : UInt8} {member afterFixed r : List UInt8}
    (h : gzipSkipHeaderFields flg member afterFixed = some r) (tail : List UInt8) :
    gzipSkipHeaderFields flg (member ++ tail) (afterFixed ++ tail) = some (r ++ tail) := by
  unfold gzipSkipHeaderFields at h ⊢
  split at h
  · cases h
  next afterOpt hso =>
  rw [gzipSkipOptional_append hso tail]
  dsimp only
  split at h
  · next hc =>
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    split at h
    · next c0 c1 r' =>
      dsimp only at h ⊢
      have hlen : (member ++ tail).length - (c0 :: c1 :: r' ++ tail).length =
          member.length - (c0 :: c1 :: r').length := by
        simp only [List.length_append, List.length_cons]
        omega
      rw [List.cons_append, List.cons_append, ← List.cons_append, ← List.cons_append, hlen,
        List.take_append_of_le_length (Nat.sub_le _ _)]
      split at h
      · next hcrc =>
        cases h
        simp only [List.cons_append, hcrc, ↓reduceIte]
      · cases h
    · cases h
  · next hc =>
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    cases h
    rfl

theorem gzipCheckTrailer_append {data afterData rest : List UInt8}
    (h : gzipCheckTrailer data afterData = some rest) (tail : List UInt8) :
    gzipCheckTrailer data (afterData ++ tail) = some (rest ++ tail) := by
  unfold gzipCheckTrailer at h ⊢
  split at h
  · next c0 c1 c2 c3 i0 i1 i2 i3 r =>
    simp only [List.cons_append]
    split at h
    · next hc =>
      cases h
      simp only [hc, and_self, ↓reduceIte]
    · cases h
  · cases h

theorem framing_local : framing.Local := by
  refine ⟨fun bytes h rest tail hh => ?_, fun h out bytes rest tail ht => ?_⟩
  · simp only [framing, checkHeader] at hh ⊢
    split at hh
    · next cm flg m0 m1 m2 m3 xfl os body =>
      simp only [List.cons_append]
      split at hh
      · cases hh
      next hok =>
      rw [ite_eq_right_of_eq_false _ _ (eq_false hok)]
      obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp hh
      cases he
      have := gzipSkipHeaderFields_append hr tail
      simp only [List.cons_append] at this
      rw [this]
      rfl
    · cases hh
  · exact gzipCheckTrailer_append ht tail

theorem local_of_deflate (h : Deflate.decoder.Local) : decoder.Local :=
  Framing.wrap_local framing_local h

end Silmaril.Proofs.Formats.Compression.Gzip
