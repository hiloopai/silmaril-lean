module

public import Silmaril.Formats.Compression.ContainerSpec.Defs
public import Silmaril.Formats.Compression.Zlib.Thms
public import Silmaril.Formats.Compression.Gzip.Thms
public import Silmaril.Formats.Compression.GzipHeader.Thms
public import Silmaril.Formats.Compression.DeflateSpec.Thms
public import Silmaril.Proofs.Formats.Compression.GzipHeader

/-! Proofs for `Silmaril.Formats.Compression.ContainerSpec.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.ContainerSpec

open Silmaril.Formats.Compression Silmaril.Formats.Compression.ContainerSpec

/-! ### Bytes and numbers -/

theorem length_four {l : List UInt8} (h : l.length = 4) : ∃ a b c d, l = [a, b, c, d] := by
  match l, h with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

theorem length_two {l : List UInt8} (h : l.length = 2) : ∃ a b, l = [a, b] := by
  match l, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

theorem le32Val_eq (a b c d : UInt8) : le32Val a b c d = leValue [a, b, c, d] := by
  simp [le32Val, leValue]; omega

theorem be32Val_eq (a b c d : UInt8) : be32Val a b c d = beValue [a, b, c, d] := by
  simp [be32Val, beValue, leValue]; omega

theorem adler32_eq (out : List UInt8) :
    (adler32 ⟨out.toArray⟩).toNat = adler32Of out := by
  rw [Checksum.adler32_toNat_eq_symbolic]; rfl

theorem crc32_eq (out : List UInt8) : (crc32 ⟨out.toArray⟩).toNat = crc32Of out := by
  rw [crc32_eq_spec]; rfl

theorem crc32List_eq (pre : List UInt8) : crc32List (pre.map UInt8.toNat) = crc32Of pre :=
  crc32List_eq_spec pre

/-- A four-byte field at the front of a list. -/
theorem exists_four {after rest : List UInt8} {P : List UInt8 → Prop} :
    (∃ t, after = t ++ rest ∧ t.length = 4 ∧ P t) ↔
      ∃ a b c d, after = a :: b :: c :: d :: rest ∧ P [a, b, c, d] := by
  constructor
  · rintro ⟨t, rfl, ht, hp⟩
    obtain ⟨a, b, c, d, rfl⟩ := length_four ht
    exact ⟨a, b, c, d, rfl, hp⟩
  · rintro ⟨a, b, c, d, rfl, hp⟩
    exact ⟨[a, b, c, d], rfl, rfl, hp⟩

/-! ### Trailers -/

theorem zlibCheckTrailer_iff {out after rest : List UInt8} :
    zlibCheckTrailer out after = some rest ↔
      ∃ adler, after = adler ++ rest ∧ adler.length = 4 ∧ beValue adler = adler32Of out := by
  rw [exists_four]
  unfold zlibCheckTrailer
  split
  · rename_i a b c d r
    simp only [be32Val_eq, adler32_eq, Option.ite_none_right_eq_some, Option.some.injEq,
      List.cons.injEq]
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨a, b, c, d, ⟨rfl, rfl, rfl, rfl, rfl⟩, h⟩
    · rintro ⟨a, b, c, d, ⟨rfl, rfl, rfl, rfl, rfl⟩, h⟩; exact ⟨h, rfl⟩
  · rename_i hne
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro a b c d h
    exact (hne a b c d rest h).elim

theorem gzipCheckTrailer_iff {out after rest : List UInt8} :
    gzipCheckTrailer out after = some rest ↔
      ∃ crc isize, after = crc ++ isize ++ rest ∧ crc.length = 4 ∧ leValue crc = crc32Of out ∧
        isize.length = 4 ∧ leValue isize = out.length % 2 ^ 32 := by
  constructor
  · intro h
    unfold gzipCheckTrailer at h
    split at h
    · rename_i c0 c1 c2 c3 i0 i1 i2 i3 r
      simp only [le32Val_eq, crc32_eq, Option.ite_none_right_eq_some, Option.some.injEq] at h
      obtain ⟨⟨h1, h2⟩, rfl⟩ := h
      exact ⟨[c0, c1, c2, c3], [i0, i1, i2, i3], rfl, rfl, h1, rfl, h2⟩
    · cases h
  · rintro ⟨crc, isize, rfl, hc, h1, hi, h2⟩
    obtain ⟨c0, c1, c2, c3, rfl⟩ := length_four hc
    obtain ⟨i0, i1, i2, i3, rfl⟩ := length_four hi
    simp only [gzipCheckTrailer, List.cons_append, List.nil_append, le32Val_eq, crc32_eq, h1, h2]
    simp

/-! ### zlib -/

theorem cm_iff : ∀ b : UInt8, b &&& 0x0F = 8 ↔ b.toNat % 16 = 8 := by decide

theorem fdict_iff : ∀ b : UInt8, b &&& 0x20 = 0 ↔ fdict b = false := by decide

theorem zlibHeader_iff (cmf flg : UInt8) :
    ZlibHeader cmf flg ↔
      cmf &&& 0x0F = 8 ∧ cmf.toNat / 16 ≤ 7 ∧ (cmf.toNat * 256 + flg.toNat) % 31 = 0 := by
  rw [cm_iff]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

theorem zlibCheckHeader_iff {bs body : List UInt8} :
    zlibCheckHeader bs = some body ↔
      ∃ cmf flg, bs = cmf :: flg :: body ∧ ZlibHeader cmf flg ∧ fdict flg = false := by
  unfold zlibCheckHeader
  split
  · rename_i cmf flg r
    simp only [zlibHeader_iff, ← fdict_iff, Option.ite_none_right_eq_some, Option.some.injEq,
      List.cons.injEq]
    constructor
    · rintro ⟨⟨h1, h2, h3, h4⟩, rfl⟩; exact ⟨cmf, flg, ⟨rfl, rfl, rfl⟩, ⟨h1, h2, h3⟩, h4⟩
    · rintro ⟨_, _, ⟨rfl, rfl, rfl⟩, ⟨h1, h2, h3⟩, h4⟩; exact ⟨⟨h1, h2, h3, h4⟩, rfl⟩
  · rename_i hne
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro cmf flg h
    exact (hne cmf flg body h).elim

/-- The body and trailer of a zlib member. -/
theorem body_trailer_iff {body out rest : List UInt8} :
    (∃ after, Deflate.deflateTake body = .ok (out, after) ∧
        zlibCheckTrailer out after = some rest) ↔
      ∃ adler, DeflateSpec.Stream .strict body out (adler ++ rest) ∧ adler.length = 4 ∧
        beValue adler = adler32Of out := by
  simp only [DeflateSpec.deflateTake_iff, zlibCheckTrailer_iff]
  constructor
  · rintro ⟨_, hs, adler, rfl, h1, h2⟩; exact ⟨adler, hs, h1, h2⟩
  · rintro ⟨adler, hs, h1, h2⟩; exact ⟨_, hs, adler, rfl, h1, h2⟩

theorem take_iff {bs out rest : List UInt8} :
    Zlib.take bs = some (out, rest) ↔ ZlibMember bs out rest := by
  have key : Zlib.take bs = some (out, rest) ↔ ∃ body, zlibCheckHeader bs = some body ∧
      ∃ after, Deflate.deflateTake body = .ok (out, after) ∧
        zlibCheckTrailer out after = some rest := by
    simp only [Zlib.take, zlibTake]
    split
    · simp_all
    · rename_i body hb
      simp only [hb, Option.some.injEq, exists_eq_left']
      split
      · simp_all
      · rename_i data after hd
        simp only [hd, Except.ok.injEq, Prod.mk.injEq]
        split
        · rename_i ht; simp only [reduceCtorEq, false_iff, not_exists, not_and]
          rintro _ ⟨rfl, rfl⟩; simp [ht]
        · rename_i tail ht
          constructor
          · rintro ⟨rfl, rfl⟩; exact ⟨after, ⟨rfl, rfl⟩, ht⟩
          · rintro ⟨_, ⟨rfl, rfl⟩, h⟩; rw [ht] at h; cases h; simp
  rw [key]
  simp only [zlibCheckHeader_iff, body_trailer_iff, ZlibMember]
  constructor
  · rintro ⟨body, ⟨cmf, flg, rfl, hh, hf⟩, adler, hs, h1, h2⟩
    exact ⟨cmf, flg, body, adler, rfl, hh, hf, hs, h1, h2⟩
  · rintro ⟨cmf, flg, body, adler, rfl, hh, hf, hs, h1, h2⟩
    exact ⟨body, ⟨cmf, flg, rfl, hh, hf⟩, adler, hs, h1, h2⟩

/-! ### zlib with a preset dictionary -/

section Dictionary

open ZlibDictionary

theorem finish_iff {raw : Except Deflate.DecompressError (List UInt8 × List UInt8)}
    {out rest : List UInt8} :
    finish raw = some (out, rest) ↔
      ∃ after, raw = .ok (out, after) ∧ zlibCheckTrailer out after = some rest := by
  unfold finish
  split
  · simp
  · rename_i data after
    simp only [Option.map_eq_some_iff, Prod.mk.injEq, Except.ok.injEq]
    constructor
    · rintro ⟨t, ht, rfl, rfl⟩; exact ⟨after, ⟨rfl, rfl⟩, ht⟩
    · rintro ⟨_, ⟨rfl, rfl⟩, ht⟩; exact ⟨rest, ht, rfl, rfl⟩

theorem checkHeader_sound {input body : List UInt8} {h : Header}
    (hc : checkHeader input = some (h, body)) :
    ∃ cmf flg r, input = cmf :: flg :: r ∧ ZlibHeader cmf flg ∧
      h.windowBits = cmf.toNat / 16 + 8 ∧
      ((fdict flg = false ∧ h.dictionaryID = none ∧ body = r) ∨
       (fdict flg = true ∧ ∃ dictid, dictid.length = 4 ∧ r = dictid ++ body ∧
          h.dictionaryID = some (beValue dictid))) := by
  unfold checkHeader at hc
  split at hc
  · rename_i cmf flg r
    split at hc
    · rename_i hh
      have hh' := (zlibHeader_iff cmf flg).2 hh
      split at hc
      · rename_i hd
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact ⟨cmf, flg, r, rfl, hh', rfl, .inl ⟨(fdict_iff flg).1 hd, rfl, rfl⟩⟩
      · rename_i hd
        split at hc
        · rename_i d0 d1 d2 d3 b
          simp only [Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          refine ⟨cmf, flg, _, rfl, hh', rfl, .inr ⟨?_, [d0, d1, d2, d3], rfl, rfl, ?_⟩⟩
          · cases h : fdict flg
            · exact absurd ((fdict_iff flg).2 h) hd
            · rfl
          · simp [be32Val_eq]
        · cases hc
    · cases hc
  · cases hc

theorem checkHeader_free {cmf flg : UInt8} {body : List UInt8} (hh : ZlibHeader cmf flg)
    (hf : fdict flg = false) :
    checkHeader (cmf :: flg :: body) = some (⟨cmf.toNat / 16 + 8, none⟩, body) := by
  have := (zlibHeader_iff cmf flg).1 hh
  simp [checkHeader, this, (fdict_iff flg).2 hf]

theorem checkHeader_dict {cmf flg : UInt8} {d0 d1 d2 d3 : UInt8} {body : List UInt8}
    (hh : ZlibHeader cmf flg) (hf : fdict flg = true) :
    checkHeader (cmf :: flg :: d0 :: d1 :: d2 :: d3 :: body) =
      some (⟨cmf.toNat / 16 + 8, some (beValue [d0, d1, d2, d3])⟩, body) := by
  have := (zlibHeader_iff cmf flg).1 hh
  have hd : ¬ flg &&& 0x20 = 0 := by rw [fdict_iff, hf]; simp
  simp [checkHeader, this, hd, be32Val_eq]

theorem dictionaryChecksum_eq (dictionary : List UInt8) :
    dictionaryChecksum dictionary = adler32Of dictionary := adler32_eq dictionary

theorem takeWithDictionary_iff {dictionary input out rest : List UInt8} :
    Zlib.takeWithDictionary dictionary input = some (out, rest) ↔
      ZlibMember input out rest ∨ ZlibDictMember dictionary input out rest := by
  constructor
  · intro h
    obtain ⟨⟨hd, body⟩, hc, hf⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨cmf, flg, r, rfl, hh, hw, ⟨hfd, hid, rfl⟩ | ⟨hfd, dictid, hl, rfl, hid⟩⟩ :=
      checkHeader_sound hc
    · simp only [hid] at hf
      obtain ⟨adler, hs, h1, h2⟩ := body_trailer_iff.1 (finish_iff.1 hf)
      exact .inl ⟨cmf, flg, _, adler, rfl, hh, hfd, hs, h1, h2⟩
    · simp only [hid] at hf
      split at hf
      · rename_i hcond
        obtain ⟨hprof, hsum⟩ := hcond
        obtain ⟨after, hdec, htr⟩ := finish_iff.1 hf
        obtain ⟨adler, rfl, h1, h2⟩ := zlibCheckTrailer_iff.1 htr
        unfold history at hdec
        have hs := DeflateSpec.StreamWithHistory.window.1
          (DeflateSpec.deflateTakeWithHistory_iff.1 hdec)
        refine .inr ⟨cmf, flg, dictid, body, adler, rfl, hh, hfd, ?_, hl,
          ?_, hs, h1, h2⟩
        · unfold supportedDictionaryProfile at hprof; omega
        · rw [← hsum, dictionaryChecksum_eq]
      · cases hf
  · rintro (⟨cmf, flg, body, adler, rfl, hh, hf, hs, h1, h2⟩ |
      ⟨cmf, flg, dictid, body, adler, rfl, hh, hf, h7, hl, hv, hs, h1, h2⟩)
    · simp only [Zlib.takeWithDictionary, takeWithDictionary, checkHeader_free hh hf,
        Option.bind_some]
      exact finish_iff.2 (body_trailer_iff.2 ⟨adler, hs, h1, h2⟩)
    · obtain ⟨d0, d1, d2, d3, rfl⟩ := length_four hl
      simp only [Zlib.takeWithDictionary, takeWithDictionary, List.cons_append, List.nil_append,
        checkHeader_dict hh hf, Option.bind_some]
      have hcond : supportedDictionaryProfile ⟨cmf.toNat / 16 + 8, some (beValue [d0, d1, d2, d3])⟩ ∧
          dictionaryChecksum dictionary = beValue [d0, d1, d2, d3] := by
        refine ⟨?_, by rw [dictionaryChecksum_eq, hv]⟩
        show cmf.toNat / 16 + 8 = 15
        omega
      simp only [hcond, and_self, ↓reduceIte]
      unfold history
      exact finish_iff.2 ⟨_, DeflateSpec.deflateTakeWithHistory_iff.2
        (DeflateSpec.StreamWithHistory.window.2 hs), zlibCheckTrailer_iff.2 ⟨adler, rfl, h1, h2⟩⟩

end Dictionary

/-! ### gzip member headers -/

section Header

open GzipHeader

theorem bit_text : ∀ b : UInt8, decide (b &&& gzipFTEXT ≠ 0) = b.toNat.testBit 0 := by decide
theorem bit_hcrc : ∀ b : UInt8, decide (b &&& gzipFHCRC ≠ 0) = b.toNat.testBit 1 := by decide
theorem bit_extra : ∀ b : UInt8, decide (b &&& gzipFEXTRA ≠ 0) = b.toNat.testBit 2 := by decide
theorem bit_name : ∀ b : UInt8, decide (b &&& gzipFNAME ≠ 0) = b.toNat.testBit 3 := by decide
theorem bit_comment : ∀ b : UInt8, decide (b &&& gzipFCOMMENT ≠ 0) = b.toNat.testBit 4 := by
  decide
theorem bit_reserved : ∀ b : UInt8, b &&& gzipFRESERVED = 0 ↔ b.toNat < 32 := by decide

theorem parseExtra_iff {bs x r : List UInt8} :
    parseExtra bs = some (x, r) ↔ ∃ xb, ExtraField x xb ∧ bs = xb ++ r := by
  constructor
  · intro h
    unfold parseExtra at h
    split at h
    · rename_i x0 x1 r0
      simp only at h
      split at h
      · rename_i hn
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[x0, x1] ++ r0.take (x0.toNat + 256 * x1.toNat), ⟨[x0, x1], rfl, ?_, rfl⟩, ?_⟩
        · simp [leValue]; omega
        · simp
      · cases h
    · cases h
  · rintro ⟨_, ⟨xlen, hl, hv, rfl⟩, rfl⟩
    obtain ⟨a, b, rfl⟩ := length_two hl
    simp only [leValue, Nat.mul_zero, Nat.add_zero] at hv
    simp [parseExtra, hv]

theorem parseZeroTerminated_iff : ∀ {bs s r : List UInt8},
    parseZeroTerminated bs = some (s, r) ↔ ∃ zb, ZeroTerminated s zb ∧ bs = zb ++ r
  | [], s, r => by simp [parseZeroTerminated, ZeroTerminated]
  | b :: bs, s, r => by
    simp only [ZeroTerminated]
    constructor
    · intro h
      by_cases hb : b = 0
      · subst hb
        simp only [parseZeroTerminated, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[0], ⟨by simp, rfl⟩, rfl⟩
      · rw [parseZeroTerminated.eq_3 b bs hb, Option.map_eq_some_iff] at h
        obtain ⟨⟨s', r'⟩, h1, h2⟩ := h
        simp only [Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        obtain ⟨_, ⟨hz, rfl⟩, rfl⟩ := parseZeroTerminated_iff.1 h1
        refine ⟨b :: s' ++ [0], ⟨?_, rfl⟩, by simp⟩
        simp only [List.mem_cons, not_or]
        exact ⟨Ne.symm hb, hz⟩
    · rintro ⟨_, ⟨hz, rfl⟩, h⟩
      rw [h, List.append_assoc]
      exact Proofs.Formats.Compression.GzipHeader.parseZeroTerminated_append r s hz

theorem optField_iff {c : Prop} [Decidable c] {p : List UInt8 → Option (List UInt8 × List UInt8)}
    {field : List UInt8 → List UInt8 → Prop}
    (hp : ∀ {bs x r}, p bs = some (x, r) ↔ ∃ b, field x b ∧ bs = b ++ r)
    {bs : List UInt8} {o : Option (List UInt8)} {r : List UInt8} :
    optField c p bs = some (o, r) ↔ o.isSome = decide c ∧ ∃ b, Optional field o b ∧ bs = b ++ r := by
  unfold optField
  by_cases hc : c
  · simp only [hc, ↓reduceIte, Option.map_eq_some_iff, decide_true]
    constructor
    · rintro ⟨⟨x, r'⟩, h, h'⟩
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      obtain ⟨b, hb, rfl⟩ := hp.1 h
      exact ⟨rfl, b, hb, rfl⟩
    · rintro ⟨ho, b, hb, rfl⟩
      cases o with
      | none => simp at ho
      | some x => exact ⟨(x, r), hp.2 ⟨b, hb, rfl⟩, rfl⟩
  · simp only [hc, ↓reduceIte, decide_false, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, [], rfl, rfl⟩
    · rintro ⟨ho, b, hb, rfl⟩
      cases o with
      | some => simp at ho
      | none => simp only [Optional] at hb; subst hb; simp

theorem parseOptional_iff {flg : UInt8} {bs : List UInt8} {e n c : Option (List UInt8)}
    {a : List UInt8} :
    parseOptional flg bs = some ((e, n, c), a) ↔
      e.isSome = flg.toNat.testBit 2 ∧ n.isSome = flg.toNat.testBit 3 ∧
      c.isSome = flg.toNat.testBit 4 ∧
      ∃ xb nb cb, Optional ExtraField e xb ∧ Optional ZeroTerminated n nb ∧
        Optional ZeroTerminated c cb ∧ bs = xb ++ nb ++ cb ++ a := by
  rw [← bit_extra, ← bit_name, ← bit_comment]
  unfold parseOptional
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨e', b1⟩, h1, ⟨n', b2⟩, h2, ⟨c', b3⟩, h3, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := heq
    obtain ⟨he, xb, hx, rfl⟩ := (optField_iff parseExtra_iff).1 h1
    obtain ⟨hn, nb, hn', rfl⟩ := (optField_iff parseZeroTerminated_iff).1 h2
    obtain ⟨hc, cb, hc', rfl⟩ := (optField_iff parseZeroTerminated_iff).1 h3
    exact ⟨he, hn, hc, xb, nb, cb, hx, hn', hc', by simp⟩
  · rintro ⟨he, hn, hc, xb, nb, cb, hx, hn', hc', rfl⟩
    refine ⟨⟨e, nb ++ cb ++ a⟩, (optField_iff parseExtra_iff).2 ⟨he, xb, hx, by simp⟩,
      ⟨n, cb ++ a⟩, (optField_iff parseZeroTerminated_iff).2 ⟨hn, nb, hn', by simp⟩,
      ⟨c, a⟩, (optField_iff parseZeroTerminated_iff).2 ⟨hc, cb, hc', rfl⟩, rfl⟩

theorem checkHcrc_iff {flg : UInt8} {pre after r : List UInt8} :
    checkHcrc flg (pre ++ after) after = some r ↔
      ∃ crc, HeaderCrc (flg.toNat.testBit 1) pre crc ∧ after = crc ++ r := by
  rw [← bit_hcrc]
  unfold checkHcrc HeaderCrc
  split
  · rename_i hc
    simp only [show decide (flg &&& gzipFHCRC ≠ 0) = true from decide_eq_true hc, ↓reduceIte]
    rcases after with _ | ⟨c0, _ | ⟨c1, r'⟩⟩
    · simp only [reduceCtorEq, false_iff, not_exists, not_and]
      intro crc ⟨hl, _⟩ h
      have := congrArg List.length h; simp at this; omega
    · simp only [reduceCtorEq, false_iff, not_exists, not_and]
      intro crc ⟨hl, _⟩ h
      have := congrArg List.length h; simp at this; omega
    · have htake : (pre ++ c0 :: c1 :: r').take
          ((pre ++ c0 :: c1 :: r').length - (c0 :: c1 :: r').length) = pre := by simp
      simp only [htake, crc32List_eq, Option.ite_none_right_eq_some, Option.some.injEq]
      constructor
      · rintro ⟨hv, rfl⟩
        exact ⟨[c0, c1], ⟨rfl, by simp [leValue]; omega⟩, rfl⟩
      · rintro ⟨crc, ⟨hl, hv⟩, h⟩
        obtain ⟨a, b, rfl⟩ := length_two hl
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp [leValue] at hv
        exact ⟨by omega, rfl⟩
  · rename_i hc
    simp only [show decide (flg &&& gzipFHCRC ≠ 0) = false from decide_eq_false hc,
      Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
    simp

theorem parseHeader_sound {bs r : List UInt8} {hdr : Header}
    (h : parseHeader bs = some (hdr, r)) : GzipMemberHeader bs hdr r := by
  unfold parseHeader at h
  split at h
  · rename_i cm flg m0 m1 m2 m3 xfl os rest
    split at h
    · cases h
    rename_i hcm
    split at h
    · cases h
    rename_i e n c afterOpt hopt
    split at h
    · cases h
    rename_i r' hh
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨he, hn, hc, xb, nb, cb, hxb, hnb, hcb, rfl⟩ := parseOptional_iff.1 hopt
    simp only [not_or, Decidable.not_not] at hcm
    obtain ⟨rfl, hres⟩ := hcm
    rw [show (0x1F :: 0x8B :: 8 :: flg :: m0 :: m1 :: m2 :: m3 :: xfl :: os ::
        (xb ++ nb ++ cb ++ afterOpt) : List UInt8) =
        ([0x1f, 0x8b, 8, flg] ++ [m0, m1, m2, m3] ++ [xfl, os] ++ xb ++ nb ++ cb) ++ afterOpt
        by simp] at hh ⊢
    obtain ⟨crc, hcrc, rfl⟩ := checkHcrc_iff.1 hh
    have := GzipMemberHeader.mk (rest := r')
      (hdr := ⟨decide (flg &&& gzipFTEXT ≠ 0), le32Val m0 m1 m2 m3, xfl, os, e, n, c,
        decide (flg &&& gzipFHCRC ≠ 0)⟩)
      (mtime := [m0, m1, m2, m3])
      ⟨by rw [bit_text], by rw [bit_hcrc], he.symm, hn.symm, hc.symm, (bit_reserved flg).1 hres⟩
      rfl (le32Val_eq _ _ _ _).symm hxb hnb hcb (by rw [bit_hcrc]; exact hcrc)
    simpa using this
  · cases h

theorem parseHeader_complete {bs r : List UInt8} {hdr : Header}
    (h : GzipMemberHeader bs hdr r) : parseHeader bs = some (hdr, r) := by
  obtain ⟨⟨ft, fh, fe, fn, fc, fr⟩, hml, hmv, hx, hn, hc, hcrc⟩ := h
  rename_i flg mtime xb nb cb crc
  obtain ⟨m0, m1, m2, m3, rfl⟩ := length_four hml
  have hopt : parseOptional flg (xb ++ nb ++ cb ++ (crc ++ r)) =
      some ((hdr.extra, hdr.name, hdr.comment), crc ++ r) :=
    parseOptional_iff.2 ⟨fe.symm, fn.symm, fc.symm, xb, nb, cb, hx, hn, hc, rfl⟩
  have hh := checkHcrc_iff (flg := flg)
    (pre := [0x1f, 0x8b, 8, flg] ++ [m0, m1, m2, m3] ++ [hdr.xfl, hdr.os] ++ xb ++ nb ++ cb)
    (after := crc ++ r) (r := r) |>.2 ⟨crc, by rw [fh]; exact hcrc, rfl⟩
  have hres : ¬ (flg &&& gzipFRESERVED ≠ 0) := by rw [Decidable.not_not, bit_reserved]; exact fr
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hopt hh ⊢
  simp only [parseHeader, ne_eq, not_true_eq_false, false_or, hres, ↓reduceIte, hopt, hh,
    Option.some.injEq, Prod.mk.injEq, and_true]
  rcases hdr with ⟨text, mtime, xfl, os, extra, name, comment, hcrc'⟩
  simp only at ft fh hmv ⊢
  rw [bit_text, bit_hcrc, le32Val_eq, ft, fh, hmv]

theorem parseHeader_iff {bs r : List UInt8} {hdr : Header} :
    parseHeader bs = some (hdr, r) ↔ GzipMemberHeader bs hdr r :=
  ⟨parseHeader_sound, parseHeader_complete⟩

end Header

/-! ### gzip members and files -/

theorem wrap_eq_some {H : Type} {f : Framing H} {body : Decoder} {bs out rest : List UInt8} :
    f.wrap body bs = some (out, rest) ↔
      ∃ h a b, f.header bs = some (h, a) ∧ body a = some (out, b) ∧
        f.trailer h out b = some rest := by
  unfold Framing.wrap
  split
  · rename_i hh; simp [hh]
  · rename_i h a hh
    split
    · rename_i hb; simp [hh, hb]
    · rename_i o b hb
      split
      · rename_i ht
        simp only [reduceCtorEq, false_iff, not_exists, not_and]
        intro h' a' b' e1 e2 e3
        rw [hh] at e1; cases e1; rw [hb] at e2; cases e2; rw [ht] at e3; cases e3
      · rename_i r ht
        simp only [Option.some.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, rfl⟩; exact ⟨h, a, b, hh, hb, ht⟩
        · rintro ⟨h', a', b', e1, e2, e3⟩
          rw [hh] at e1; cases e1; rw [hb] at e2; cases e2; rw [ht] at e3; cases e3
          exact ⟨rfl, rfl⟩

theorem deflate_decoder_eq_some {a out b : List UInt8} :
    Deflate.decoder a = some (out, b) ↔ DeflateSpec.Stream .strict a out b := by
  rw [← DeflateSpec.deflateTake_iff]
  simp only [Deflate.decoder, Decoder.ofExcept]
  cases Deflate.deflateTake a <;> simp [Except.toOption]

theorem checkHeader_eq_some {bs a : List UInt8} :
    Gzip.checkHeader bs = some ((), a) ↔ ∃ hdr, GzipMemberHeader bs hdr a := by
  rw [← GzipHeader.parseHeader_agrees]
  simp only [Option.map_eq_some_iff, Prod.mk.injEq, true_and, ← parseHeader_iff]
  constructor
  · rintro ⟨⟨hdr, a'⟩, h, rfl⟩; exact ⟨hdr, h⟩
  · rintro ⟨hdr, h⟩; exact ⟨(hdr, a), h, rfl⟩

theorem gzipMember_iff {bs out rest : List UInt8} :
    gzipMember bs = some (out, rest) ↔ ∃ hdr, GzipMember bs hdr out rest := by
  rw [show gzipMember = Gzip.decoder from Gzip.member_eq_decoder, Gzip.decoder, wrap_eq_some]
  constructor
  · rintro ⟨⟨⟩, a, b, h1, h2, h3⟩
    obtain ⟨hdr, hh⟩ := checkHeader_eq_some.1 h1
    obtain ⟨crc, isize, rfl, h4⟩ := gzipCheckTrailer_iff.1 h3
    exact ⟨hdr, a, crc, isize, hh, deflate_decoder_eq_some.1 h2, h4⟩
  · rintro ⟨hdr, a, crc, isize, hh, hs, h4⟩
    exact ⟨(), a, _, checkHeader_eq_some.2 ⟨hdr, hh⟩, deflate_decoder_eq_some.2 hs,
      gzipCheckTrailer_iff.2 ⟨crc, isize, rfl, h4⟩⟩

theorem gzipMember_progress {bs out rest : List UInt8} (h : gzipMember bs = some (out, rest)) :
    rest.length < bs.length := by
  rw [show gzipMember = Gzip.decoder from Gzip.member_eq_decoder] at h
  obtain ⟨pre, rfl⟩ := Gzip.decoder_trailer h
  simp [Gzip.trailer, le32, le32Bytes]; omega

theorem gzipFile_nil {out : List UInt8} : ¬ GzipFile [] out := by
  have hm : ∀ {hdr o r}, ¬ GzipMember [] hdr o r := by
    rintro hdr o r ⟨_, _, _, hh, _⟩
    cases hh
  intro h
  cases h with
  | last hm' => exact hm hm'
  | cons hm' _ => exact hm hm'

theorem membersFuel_iff : ∀ (fuel : Nat) {bs acc out : List UInt8}, bs.length < fuel →
    (Decoder.membersFuel gzipMember fuel bs acc = some out ↔
      ∃ o, out = acc ++ o ∧ GzipFile bs o)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, bs, acc, out, hf => by
    have hfile : ∀ {o}, GzipFile bs o ↔ ∃ o1 r, gzipMember bs = some (o1, r) ∧
        ((r = [] ∧ o = o1) ∨ (r ≠ [] ∧ ∃ o2, o = o1 ++ o2 ∧ GzipFile r o2)) := by
      intro o
      constructor
      · intro h
        cases h with
        | last hm => exact ⟨o, [], gzipMember_iff.2 ⟨_, hm⟩, .inl ⟨rfl, rfl⟩⟩
        | @cons _ _ o1 r o2 hm hr =>
          refine ⟨o1, r, gzipMember_iff.2 ⟨_, hm⟩, .inr ⟨?_, o2, rfl, hr⟩⟩
          rintro rfl; exact gzipFile_nil hr
      · rintro ⟨o1, r, hm, ⟨rfl, rfl⟩ | ⟨_, o2, rfl, hr⟩⟩
        · obtain ⟨hdr, hm⟩ := gzipMember_iff.1 hm; exact .last hm
        · obtain ⟨hdr, hm⟩ := gzipMember_iff.1 hm; exact .cons hm hr
    simp only [hfile]
    unfold Decoder.membersFuel
    split
    · rename_i hn
      simp [hn]
    · rename_i o1 hm
      simp only [Option.some.injEq, hm, Prod.mk.injEq]
      constructor
      · rintro rfl; exact ⟨o1, rfl, o1, [], ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩⟩
      · rintro ⟨o, rfl, o1', r, ⟨rfl, rfl⟩, ⟨_, rfl⟩ | ⟨hne, _⟩⟩
        · rfl
        · exact absurd rfl hne
    · rename_i o1 r hne hm
      have hp := gzipMember_progress hm
      rw [membersFuel_iff fuel (by omega)]
      simp only [hm, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨o2, rfl, hr⟩
        exact ⟨o1 ++ o2, by simp, o1, r, ⟨rfl, rfl⟩, .inr ⟨hne, o2, rfl, hr⟩⟩
      · rintro ⟨o, rfl, o1', r', ⟨rfl, rfl⟩, ⟨rfl, _⟩ | ⟨_, o2, rfl, hr⟩⟩
        · exact absurd rfl hne
        · exact ⟨o2, by simp, hr⟩

theorem gzipDecompress_iff {bs out : List UInt8} :
    gzipDecompress ⟨bs.toArray⟩ = some ⟨out.toArray⟩ ↔ GzipFile bs out := by
  have h := Gzip.decompress_eq ⟨bs.toArray⟩
  simp only [Gzip.decompress] at h
  rw [h, ← Gzip.member_eq_decoder]
  simp only [Decoder.members, Option.map_eq_some_iff]
  constructor
  · rintro ⟨o, ho, he⟩
    have : o = out := by
      have := congrArg (fun b : ByteArray => b.data.toList) he
      simpa using this
    subst this
    obtain ⟨o', ho', hf⟩ := (membersFuel_iff _ (Nat.lt_succ_self _)).1 ho
    simp at ho'
    exact ho' ▸ hf
  · intro hf
    exact ⟨out, (membersFuel_iff _ (Nat.lt_succ_self _)).2 ⟨out, by simp, hf⟩, rfl⟩

theorem zlibDecompress_iff {bs out : List UInt8} :
    zlibDecompress ⟨bs.toArray⟩ = some ⟨out.toArray⟩ ↔ ZlibMember bs out [] := by
  have h := Zlib.decompress_eq ⟨bs.toArray⟩
  simp only [Zlib.decompress] at h
  rw [h, Option.map_eq_some_iff]
  rw [← take_iff, Zlib.take_eq_decoder, ← Decoder.whole_eq_some_iff]
  constructor
  · rintro ⟨o, ho, he⟩
    have : o = out := by
      have := congrArg (fun b : ByteArray => b.data.toList) he
      simpa using this
    exact this ▸ ho
  · intro h; exact ⟨out, h, rfl⟩

end Silmaril.Proofs.Formats.Compression.ContainerSpec
