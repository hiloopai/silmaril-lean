module

public import Silmaril.Formats.Compression.GzipHeader.Defs
public import Silmaril.Formats.Compression.Gzip.Thms

/-! Proofs for `Silmaril.Formats.Compression.GzipHeader.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.GzipHeader

open Silmaril.Formats.Compression Silmaril.Formats.Compression.GzipHeader

/-! ### Agreement with `Gzip.checkHeader` -/

theorem skipHeaderFields_eq (flg : UInt8) (m a : List UInt8) :
    gzipSkipHeaderFields flg m a = (gzipSkipOptional flg a).bind (checkHcrc flg m) := by
  unfold gzipSkipHeaderFields
  cases gzipSkipOptional flg a <;> rfl

theorem parseZeroTerminated_snd : ∀ bs : List UInt8,
    (parseZeroTerminated bs).map Prod.snd = gzipDropZeroTerminated bs
  | [] => rfl
  | b :: rest => by
    by_cases hb : b = 0
    · subst hb; rfl
    · rw [parseZeroTerminated.eq_3 b rest hb, gzipDropZeroTerminated.eq_3 b rest hb,
        ← parseZeroTerminated_snd rest, Option.map_map]
      rfl

theorem optField_snd (c : Prop) [Decidable c] (p : List UInt8 → Option (List UInt8 × List UInt8))
    (bs : List UInt8) :
    (optField c p bs).map Prod.snd = if c then (p bs).map Prod.snd else some bs := by
  unfold optField
  split
  · rw [Option.map_map]; rfl
  · rfl

theorem parseExtra_snd (x0 x1 : UInt8) (r : List UInt8) :
    (parseExtra (x0 :: x1 :: r)).map Prod.snd = gzipDropExact (x0.toNat + 256 * x1.toNat) r := by
  simp only [parseExtra, gzipDropExact]
  split <;> rfl

theorem skipOptional_eq (flg : UInt8) (bs : List UInt8) :
    gzipSkipOptional flg bs =
      (if flg &&& gzipFEXTRA ≠ 0 then (parseExtra bs).map Prod.snd else some bs).bind fun b1 =>
        (if flg &&& gzipFNAME ≠ 0 then gzipDropZeroTerminated b1 else some b1).bind fun b2 =>
          if flg &&& gzipFCOMMENT ≠ 0 then gzipDropZeroTerminated b2 else some b2 := by
  unfold gzipSkipOptional
  rcases bs with _ | ⟨x0, _ | ⟨x1, r⟩⟩ <;> (try rw [parseExtra_snd]) <;>
  by_cases hE : flg &&& gzipFEXTRA = 0 <;> by_cases hN : flg &&& gzipFNAME = 0 <;>
  by_cases hC : flg &&& gzipFCOMMENT = 0 <;> simp [hE, hN, hC, parseExtra] <;>
  (repeat' split) <;> simp_all

theorem parseOptional_snd (flg : UInt8) (bs : List UInt8) :
    (parseOptional flg bs).map Prod.snd = gzipSkipOptional flg bs := by
  rw [skipOptional_eq]
  simp only [← parseZeroTerminated_snd, ← optField_snd, Option.bind_map, parseOptional,
    Option.map_bind]
  congr 1
  funext p1
  simp only [Function.comp_apply, Option.map_bind]
  congr 1
  funext p2
  simp only [Function.comp_apply, Option.map_map]
  rfl

theorem parseHeader_agrees (bs : List UInt8) :
    (parseHeader bs).map (fun p => ((), p.2)) = Gzip.checkHeader bs := by
  unfold parseHeader
  split
  · simp only [Gzip.checkHeader]
    split
    · rfl
    · rw [skipHeaderFields_eq, ← parseOptional_snd]
      rcases parseOptional _ _ with _ | ⟨⟨e, n, c⟩, a⟩
      · rfl
      · simp only [Option.map_some, Option.bind_some]
        rcases checkHcrc _ _ a with _ | r <;> rfl
  · rename_i hne
    have hnone : Gzip.checkHeader bs = none := by
      unfold Gzip.checkHeader
      split
      · exact (hne _ _ _ _ _ _ _ _ _ rfl).elim
      · rfl
    rw [hnone]
    rfl

/-! ### Round trip -/

theorem flg_bits (h : Header) :
    h.flg &&& gzipFRESERVED = 0 ∧ (h.flg &&& gzipFTEXT ≠ 0 ↔ h.text = true) ∧
      (h.flg &&& gzipFHCRC ≠ 0 ↔ h.hcrc = true) ∧
      (h.flg &&& gzipFEXTRA ≠ 0 ↔ h.extra.isSome = true) ∧
      (h.flg &&& gzipFNAME ≠ 0 ↔ h.name.isSome = true) ∧
      (h.flg &&& gzipFCOMMENT ≠ 0 ↔ h.comment.isSome = true) := by
  unfold Header.flg
  generalize h.text = a
  generalize h.hcrc = b
  generalize h.extra.isSome = c
  generalize h.name.isSome = d
  generalize h.comment.isSome = e
  revert a b c d e
  decide

theorem le32Val_le32Bytes (n : Nat) :
    le32Val (UInt8.ofNat (n % 256)) (UInt8.ofNat (n / 256 % 256)) (UInt8.ofNat (n / 65536 % 256))
      (UInt8.ofNat (n / 16777216 % 256)) = n % 2 ^ 32 := by
  simp only [le32Val, UInt8.toNat_ofNat', Nat.reducePow, Nat.mod_mod]
  omega

theorem parseZeroTerminated_append (r : List UInt8) :
    ∀ s : List UInt8, 0 ∉ s → parseZeroTerminated (s ++ 0 :: r) = some (s, r)
  | [], _ => rfl
  | b :: s, hs => by
    have hb : b ≠ 0 := fun hb => hs (hb ▸ List.mem_cons_self)
    have hs' : 0 ∉ s := fun h => hs (List.mem_cons_of_mem _ h)
    rw [List.cons_append, parseZeroTerminated.eq_3 b _ hb, parseZeroTerminated_append r s hs']
    rfl

theorem parseExtra_append {x : List UInt8} (hx : x.length < 65536) (r : List UInt8) :
    parseExtra (le16Bytes x.length ++ (x ++ r)) = some (x, r) := by
  simp only [le16Bytes, List.cons_append, List.nil_append, parseExtra, UInt8.toNat_ofNat']
  have hn : x.length % 256 % 2 ^ 8 + 256 * (x.length / 256 % 256 % 2 ^ 8) = x.length := by omega
  simp only [hn, List.length_append, Nat.le_add_right, ↓reduceIte, List.take_left', List.drop_left']

theorem parseOptional_encodeOptional {h : Header} (hv : h.Valid) (r : List UInt8) :
    parseOptional h.flg (encodeOptional h ++ r) = some ((h.extra, h.name, h.comment), r) := by
  obtain ⟨_, _, _, _, hE, hN, hC⟩ := flg_bits h
  obtain ⟨_, vE, vN, vC⟩ := hv
  unfold parseOptional encodeOptional optField
  revert hE hN hC vE vN vC
  rcases h with ⟨text, mtime, xfl, os, extra, name, comment, hcrc⟩
  dsimp only
  intro hE hN hC vE vN vC
  rcases extra with _ | x <;> rcases name with _ | n <;> rcases comment with _ | c <;>
  simp_all [parseExtra_append, parseZeroTerminated_append]

theorem hcrcOf_lt (pre : List UInt8) : hcrcOf pre < 65536 := Nat.mod_lt _ (by decide)

theorem checkHcrc_encode (h : Header) (rest : List UInt8) :
    checkHcrc h.flg (encodeHeader h ++ rest)
      ((if h.hcrc then le16Bytes (hcrcOf (encodePrefix h)) else []) ++ rest) = some rest := by
  obtain ⟨_, _, hH, _⟩ := flg_bits h
  unfold checkHcrc encodeHeader
  cases hc : h.hcrc
  · simp_all
  · have hv := hcrcOf_lt (encodePrefix h)
    simp only [hc, ↓reduceIte] at hH ⊢
    simp only [hH, ↓reduceIte, le16Bytes, List.cons_append,
      List.nil_append, UInt8.toNat_ofNat', List.append_assoc, List.length_append, List.length_cons]
    have hlen : (encodePrefix h).length + (rest.length + 1 + 1) - (rest.length + 1 + 1) =
        (encodePrefix h).length := by omega
    rw [hlen, List.take_left' rfl]
    simp only [hcrcOf] at hv ⊢
    simp only [Nat.reducePow, Nat.mod_mod]
    exact ite_eq_left_of_eq_true _ _ (eq_true (by omega))

theorem encodeHeader_eq (h : Header) (rest : List UInt8) :
    encodeHeader h ++ rest =
      0x1F :: 0x8B :: 0x08 :: h.flg :: UInt8.ofNat (h.mtime % 256) ::
        UInt8.ofNat (h.mtime / 256 % 256) :: UInt8.ofNat (h.mtime / 65536 % 256) ::
        UInt8.ofNat (h.mtime / 16777216 % 256) :: h.xfl :: h.os ::
        (encodeOptional h ++
          ((if h.hcrc then le16Bytes (hcrcOf (encodePrefix h)) else []) ++ rest)) := by
  simp [encodeHeader, encodePrefix, le32Bytes]

theorem parseHeader_encodeHeader {h : Header} (hv : h.Valid) (rest : List UInt8) :
    parseHeader (encodeHeader h ++ rest) = some (h, rest) := by
  obtain ⟨hR, hT, hH, -⟩ := flg_bits h
  have hm := le32Val_le32Bytes h.mtime
  rw [Nat.mod_eq_of_lt hv.1] at hm
  have hc := checkHcrc_encode h rest
  have ho := parseOptional_encodeOptional hv
    ((if h.hcrc then le16Bytes (hcrcOf (encodePrefix h)) else []) ++ rest)
  rw [encodeHeader_eq] at hc ⊢
  simp only [parseHeader, ho, hc, hR, hm, ne_eq, not_true_eq_false, or_false, ↓reduceIte,
    Option.some.injEq, Prod.mk.injEq, and_true]
  rcases h with ⟨text, mtime, xfl, os, extra, name, comment, hcrc⟩
  simp only at hT hH ⊢
  cases text <;> cases hcrc <;> simp_all

theorem checkHeader_encodeHeader {h : Header} (hv : h.Valid) (rest : List UInt8) :
    Gzip.checkHeader (encodeHeader h ++ rest) = some ((), rest) := by
  rw [← parseHeader_agrees, parseHeader_encodeHeader hv]
  rfl

/-- The gzip trailer is accepted after its own output, from `Gzip.roundTrip`. -/
theorem checkTrailer_trailer (out tail : List UInt8) :
    gzipCheckTrailer out (Gzip.trailer out ++ tail) = some tail := by
  have h := Gzip.roundTrip out tail
  have hh : Gzip.framing.header (Gzip.header ++ (Deflate.encoder out ++ (Gzip.trailer out ++ tail))) =
      some ((), Deflate.encoder out ++ (Gzip.trailer out ++ tail)) := by
    simp only [Gzip.framing, Gzip.header, gzipMagic, List.cons_append, List.nil_append]
    rfl
  have hd := Deflate.roundTrip out (Gzip.trailer out ++ tail)
  simp only [Gzip.decoder, Gzip.encoder, Framing.encode, Framing.wrap, List.append_assoc] at h
  rw [hh] at h
  dsimp only at h
  rw [hd] at h
  dsimp only [Gzip.framing] at h
  split at h
  · cases h
  · next r hr => cases h; exact hr

theorem writes {h : Header} (hv : h.Valid) : Gzip.framing.Writes (encodeHeader h) Gzip.trailer :=
  fun rest => ⟨(), checkHeader_encodeHeader hv rest, checkTrailer_trailer⟩

theorem roundTrip {h : Header} (hv : h.Valid) : RoundTrip Gzip.decoder (encodeMember h) :=
  Framing.wrap_roundTrip (writes hv) Deflate.roundTrip

end Silmaril.Proofs.Formats.Compression.GzipHeader
