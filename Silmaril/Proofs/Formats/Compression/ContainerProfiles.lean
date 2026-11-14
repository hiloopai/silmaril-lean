module

public import Silmaril.Proofs.Formats.Compression.ContainerSpec
public import Silmaril.Formats.Compression.Gzip.Prefix

/-! Proofs for the zlib window/dictionary profiles and the suffix-lenient gzip
file profile of `Silmaril.Formats.Compression.ContainerSpec.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.ContainerSpec

open Silmaril.Formats.Compression Silmaril.Formats.Compression.ContainerSpec

/-! ### zlib within the `CINFO` window -/

theorem takeWindowed_iff {bs out rest : List UInt8} :
    Zlib.takeWindowed bs = some (out, rest) ↔ ZlibMemberWindowed bs out rest := by
  constructor
  · intro h
    unfold Zlib.takeWindowed at h
    split at h
    · cases h
    rename_i cmf tl
    split at h
    · cases h
    rename_i body hb
    obtain ⟨cmf', flg, e, hh, hf⟩ := zlibCheckHeader_iff.1 hb
    simp only [List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨after, hd, ht⟩ := finish_iff.1 h
    obtain ⟨adler, rfl, h1, h2⟩ := zlibCheckTrailer_iff.1 ht
    exact ⟨cmf, flg, body, adler, rfl, hh, hf, DeflateSpec.deflateTakeWindowed_iff.1 hd, h1, h2⟩
  · rintro ⟨cmf, flg, body, adler, rfl, hh, hf, hs, h1, h2⟩
    have hc : zlibCheckHeader (cmf :: flg :: body) = some body :=
      zlibCheckHeader_iff.2 ⟨cmf, flg, rfl, hh, hf⟩
    simp only [Zlib.takeWindowed, hc]
    exact finish_iff.2 ⟨_, DeflateSpec.deflateTakeWindowed_iff.2 hs,
      zlibCheckTrailer_iff.2 ⟨adler, rfl, h1, h2⟩⟩

theorem zlibMemberWindowed_member {bs out rest : List UInt8} (h : ZlibMemberWindowed bs out rest) :
    ZlibMember bs out rest := by
  obtain ⟨cmf, flg, body, adler, rfl, hh, hf, hs, h1, h2⟩ := h
  exact ⟨cmf, flg, body, adler, rfl, hh, hf, (DeflateSpec.StreamWithHistoryWithin.unwindowed hs), h1, h2⟩

theorem zlibWindow_seven {cmf : UInt8} (h : cmf.toNat / 16 = 7) : zlibWindow cmf = 32768 := by
  simp [zlibWindow, h]

theorem zlibMemberWindowed_iff_seven {cmf : UInt8} {tl out rest : List UInt8}
    (h7 : cmf.toNat / 16 = 7) :
    ZlibMemberWindowed (cmf :: tl) out rest ↔ ZlibMember (cmf :: tl) out rest := by
  refine ⟨zlibMemberWindowed_member, ?_⟩
  rintro ⟨cmf', flg, body, adler, e, hh, hf, hs, h1, h2⟩
  simp only [List.cons.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨_, flg, body, adler, rfl, hh, hf,
    (DeflateSpec.streamWithHistoryWithin_large (by rw [zlibWindow_seven h7]; exact Nat.le_refl _)).2 hs, h1, h2⟩

/-! ### zlib with a preset dictionary, every window -/

section Dictionary

open ZlibDictionary

theorem takeWithDictionaryAnyWindow_iff {dictionary input out rest : List UInt8} :
    Zlib.takeWithDictionaryAnyWindow dictionary input = some (out, rest) ↔
      ZlibMember input out rest ∨ ZlibDictMemberAnyWindow dictionary input out rest := by
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
      · rename_i hsum
        obtain ⟨after, hdec, htr⟩ := finish_iff.1 hf
        obtain ⟨adler, rfl, h1, h2⟩ := zlibCheckTrailer_iff.1 htr
        unfold history at hdec
        have hs := DeflateSpec.StreamWithHistory.window.1
          (DeflateSpec.deflateTakeWithHistory_iff.1 hdec)
        exact .inr ⟨cmf, flg, dictid, body, adler, rfl, hh, hfd, hl,
          by rw [← hsum, dictionaryChecksum_eq], hs, h1, h2⟩
      · cases hf
  · rintro (⟨cmf, flg, body, adler, rfl, hh, hf, hs, h1, h2⟩ |
      ⟨cmf, flg, dictid, body, adler, rfl, hh, hf, hl, hv, hs, h1, h2⟩)
    · simp only [Zlib.takeWithDictionaryAnyWindow, checkHeader_free hh hf, Option.bind_some]
      exact finish_iff.2 (body_trailer_iff.2 ⟨adler, hs, h1, h2⟩)
    · obtain ⟨d0, d1, d2, d3, rfl⟩ := length_four hl
      simp only [Zlib.takeWithDictionaryAnyWindow, List.cons_append, List.nil_append,
        checkHeader_dict hh hf, Option.bind_some]
      have hcond : dictionaryChecksum dictionary = beValue [d0, d1, d2, d3] := by
        rw [dictionaryChecksum_eq, hv]
      simp only [hcond, ↓reduceIte]
      unfold history
      exact finish_iff.2 ⟨_, DeflateSpec.deflateTakeWithHistory_iff.2
        (DeflateSpec.StreamWithHistory.window.2 hs), zlibCheckTrailer_iff.2 ⟨adler, rfl, h1, h2⟩⟩

theorem zlibDictMember_iff_anyWindow {dictionary input out rest : List UInt8} :
    ZlibDictMember dictionary input out rest ↔
      ZlibDictMemberAnyWindow dictionary input out rest ∧
        ∃ cmf tl, input = cmf :: tl ∧ cmf.toNat / 16 = 7 := by
  constructor
  · rintro ⟨cmf, flg, dictid, body, adler, rfl, hh, hf, h7, hl, hv, hs, h1, h2⟩
    exact ⟨⟨cmf, flg, dictid, body, adler, rfl, hh, hf, hl, hv, hs, h1, h2⟩, cmf, _, rfl, h7⟩
  · rintro ⟨⟨cmf, flg, dictid, body, adler, rfl, hh, hf, hl, hv, hs, h1, h2⟩, cmf', tl, e, h7⟩
    simp only [List.cons.injEq] at e
    obtain ⟨rfl, -⟩ := e
    exact ⟨cmf, flg, dictid, body, adler, rfl, hh, hf, h7, hl, hv, hs, h1, h2⟩

/-- On `CINFO = 7` headers (and on every input that is not a dictionary member),
`takeWithDictionary` is `takeWithDictionaryAnyWindow`. -/
theorem takeWithDictionary_eq_anyWindow {dictionary input : List UInt8}
    (h7 : ∀ cmf tl, input = cmf :: tl → cmf.toNat / 16 = 7) :
    Zlib.takeWithDictionary dictionary input = Zlib.takeWithDictionaryAnyWindow dictionary input := by
  apply Option.ext
  rintro ⟨out, rest⟩
  rw [takeWithDictionary_iff, takeWithDictionaryAnyWindow_iff, zlibDictMember_iff_anyWindow]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact .inl h
    · exact .inr h
  · rintro (h | h)
    · exact .inl h
    · have h' := h
      obtain ⟨cmf, flg, dictid, body, adler, rfl, -⟩ := h'
      exact .inr ⟨h, cmf, _, rfl, h7 _ _ rfl⟩

theorem takeWithDictionary_anyWindow {dictionary input out rest : List UInt8}
    (h : Zlib.takeWithDictionary dictionary input = some (out, rest)) :
    Zlib.takeWithDictionaryAnyWindow dictionary input = some (out, rest) := by
  rw [takeWithDictionaryAnyWindow_iff]
  rcases takeWithDictionary_iff.1 h with h | h
  · exact .inl h
  · exact .inr (zlibDictMember_iff_anyWindow.1 h).1

theorem takeWithDictionaryWindowed_iff {dictionary input out rest : List UInt8} :
    Zlib.takeWithDictionaryWindowed dictionary input = some (out, rest) ↔
      ZlibMemberWindowed input out rest ∨ ZlibDictMemberWindowed dictionary input out rest := by
  constructor
  · intro h
    obtain ⟨⟨hd, body⟩, hc, hf⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨cmf, flg, r, rfl, hh, hw, ⟨hfd, hid, rfl⟩ | ⟨hfd, dictid, hl, rfl, hid⟩⟩ :=
      checkHeader_sound hc
    · simp only [hid, hw] at hf
      obtain ⟨after, hdec, htr⟩ := finish_iff.1 hf
      obtain ⟨adler, rfl, h1, h2⟩ := zlibCheckTrailer_iff.1 htr
      exact .inl ⟨cmf, flg, _, adler, rfl, hh, hfd,
        DeflateSpec.deflateTakeWindowed_iff.1 hdec, h1, h2⟩
    · simp only [hid, hw] at hf
      split at hf
      · rename_i hsum
        obtain ⟨after, hdec, htr⟩ := finish_iff.1 hf
        obtain ⟨adler, rfl, h1, h2⟩ := zlibCheckTrailer_iff.1 htr
        have hs := DeflateSpec.StreamWithHistoryWithin.window.1
          (DeflateSpec.deflateTakeWithHistoryWindowed_iff.1 hdec)
        exact .inr ⟨cmf, flg, dictid, body, adler, rfl, hh, hfd, hl,
          by rw [← hsum, dictionaryChecksum_eq], hs, h1, h2⟩
      · cases hf
  · rintro (⟨cmf, flg, body, adler, rfl, hh, hf, hs, h1, h2⟩ |
      ⟨cmf, flg, dictid, body, adler, rfl, hh, hf, hl, hv, hs, h1, h2⟩)
    · simp only [Zlib.takeWithDictionaryWindowed, checkHeader_free hh hf, Option.bind_some]
      exact finish_iff.2 ⟨_, DeflateSpec.deflateTakeWindowed_iff.2 hs,
        zlibCheckTrailer_iff.2 ⟨adler, rfl, h1, h2⟩⟩
    · obtain ⟨d0, d1, d2, d3, rfl⟩ := length_four hl
      simp only [Zlib.takeWithDictionaryWindowed, List.cons_append, List.nil_append,
        checkHeader_dict hh hf, Option.bind_some]
      have hcond : dictionaryChecksum dictionary = beValue [d0, d1, d2, d3] := by
        rw [dictionaryChecksum_eq, hv]
      simp only [hcond, ↓reduceIte]
      exact finish_iff.2 ⟨_, DeflateSpec.deflateTakeWithHistoryWindowed_iff.2
        (DeflateSpec.StreamWithHistoryWithin.window.2 hs),
        zlibCheckTrailer_iff.2 ⟨adler, rfl, h1, h2⟩⟩

end Dictionary

/-! ### gzip files with a suffix -/

theorem gzipMember_functional {bs out out' rest rest' : List UInt8} {hdr hdr'}
    (h : GzipMember bs hdr out rest) (h' : GzipMember bs hdr' out' rest') :
    out = out' ∧ rest = rest' := by
  have := (gzipMember_iff.2 ⟨_, h⟩).symm.trans (gzipMember_iff.2 ⟨_, h'⟩)
  simp_all

theorem noMember_iff {bs : List UInt8} :
    gzipMember bs = none ↔ ∀ hdr out rest, ¬ GzipMember bs hdr out rest := by
  constructor
  · intro h hdr out rest hm
    rw [gzipMember_iff.2 ⟨hdr, hm⟩] at h
    cases h
  · intro h
    cases e : gzipMember bs with
    | none => rfl
    | some p =>
      obtain ⟨hdr, hm⟩ := gzipMember_iff.1 e
      exact (h hdr _ _ hm).elim

/-- After the first member: no member and nothing more, or a lenient file. -/
def PTail (bs o rest : List UInt8) : Prop :=
  (gzipMember bs = none ∧ o = [] ∧ rest = bs) ∨ GzipFilePrefix bs o rest

theorem filePrefix_member {bs out rest : List UInt8} (h : GzipFilePrefix bs out rest) :
    ∃ p, gzipMember bs = some p := by
  cases h with
  | last hm _ => exact ⟨_, gzipMember_iff.2 ⟨_, hm⟩⟩
  | cons hm _ => exact ⟨_, gzipMember_iff.2 ⟨_, hm⟩⟩

theorem filePrefix_iff {bs d r out rest : List UInt8} (hm : gzipMember bs = some (d, r)) :
    GzipFilePrefix bs out rest ↔ ∃ o, out = d ++ o ∧ PTail r o rest := by
  obtain ⟨hdr, hm'⟩ := gzipMember_iff.1 hm
  constructor
  · intro h
    cases h with
    | last hm2 hno =>
      obtain ⟨rfl, rfl⟩ := gzipMember_functional hm' hm2
      exact ⟨[], by simp, .inl ⟨noMember_iff.2 hno, rfl, rfl⟩⟩
    | cons hm2 hp =>
      obtain ⟨rfl, rfl⟩ := gzipMember_functional hm' hm2
      exact ⟨_, rfl, .inr hp⟩
  · rintro ⟨o, rfl, ⟨hno, rfl, rfl⟩ | hp⟩
    · rw [List.append_nil]; exact .last hm' (noMember_iff.1 hno)
    · exact .cons hm' hp

theorem membersPrefix_iff : ∀ (fuel : Nat) {bs acc out rest : List UInt8}, bs.length < fuel →
    (Gzip.membersPrefix fuel bs acc = (out, rest) ↔ ∃ o, out = acc ++ o ∧ PTail bs o rest)
  | 0, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, bs, acc, out, rest, hf => by
    simp only [Gzip.membersPrefix]
    cases hm : gzipMember bs with
    | none =>
      simp only [Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨[], by simp, .inl ⟨hm, rfl, rfl⟩⟩
      · rintro ⟨o, rfl, ⟨_, rfl, rfl⟩ | hp⟩
        · simp
        · obtain ⟨p, hp'⟩ := filePrefix_member hp; rw [hm] at hp'; cases hp'
    | some p =>
      obtain ⟨d, r⟩ := p
      have hp := gzipMember_progress hm
      simp only
      rw [membersPrefix_iff fuel (by omega)]
      have hpt : ∀ o, PTail bs o rest ↔ GzipFilePrefix bs o rest := by
        intro o
        refine ⟨fun h => ?_, .inr⟩
        rcases h with ⟨h, -⟩ | h
        · rw [hm] at h; cases h
        · exact h
      simp only [hpt, filePrefix_iff hm]
      constructor
      · rintro ⟨o, rfl, h⟩; exact ⟨d ++ o, by simp, o, rfl, h⟩
      · rintro ⟨_, rfl, o, rfl, h⟩; exact ⟨o, by simp, h⟩

theorem decompressPrefix_iff {bs out rest : List UInt8} :
    Gzip.decompressPrefix bs = some (out, rest) ↔ GzipFilePrefix bs out rest := by
  unfold Gzip.decompressPrefix
  cases hm : gzipMember bs with
  | none =>
    simp only [reduceCtorEq, false_iff]
    intro h
    obtain ⟨p, hp⟩ := filePrefix_member h
    rw [hm] at hp; cases hp
  | some p =>
    obtain ⟨d, r⟩ := p
    simp only [Option.some.injEq]
    rw [membersPrefix_iff _ (Nat.lt_succ_self _), filePrefix_iff hm]

theorem gzipFile_iff_prefix {bs out : List UInt8} :
    GzipFile bs out ↔ GzipFilePrefix bs out [] := by
  have hnil : ∀ hdr' out' rest', ¬ GzipMember [] hdr' out' rest' :=
    noMember_iff.1 rfl
  constructor
  · intro h
    induction h with
    | last hm => exact .last hm hnil
    | cons hm _ ih => exact .cons hm ih
  · intro h
    have key : ∀ {bs out rest}, GzipFilePrefix bs out rest → rest = [] → GzipFile bs out := by
      intro bs out rest h
      induction h with
      | last hm _ => intro e; subst e; exact .last hm
      | cons hm _ ih => intro e; exact .cons hm (ih e)
    exact key h rfl

theorem gzipDecompress_iff_prefix {bs out : List UInt8} :
    gzipDecompress ⟨bs.toArray⟩ = some ⟨out.toArray⟩ ↔ Gzip.decompressPrefix bs = some (out, []) := by
  rw [gzipDecompress_iff, decompressPrefix_iff, gzipFile_iff_prefix]

/-! ### Witnesses -/

set_option maxRecDepth 100000 in
theorem zlibFar_take : Zlib.take [0x08, 0x1d, 0x63, 0x18, 0x05, 0xc0, 0x00, 0x00, 0x00, 0x01,
    0x06, 0x00, 0x01] = some (List.replicate 262 0, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem zlibFar_takeWindowed : Zlib.takeWindowed [0x08, 0x1d, 0x63, 0x18, 0x05, 0xc0, 0x00, 0x00,
    0x00, 0x01, 0x06, 0x00, 0x01] = none := by
  decide +kernel

theorem zlib_window_witness :
    ZlibMember [0x08, 0x1d, 0x63, 0x18, 0x05, 0xc0, 0x00, 0x00, 0x00, 0x01, 0x06, 0x00, 0x01]
      (List.replicate 262 0) [] ∧
    ∀ out rest, ¬ ZlibMemberWindowed [0x08, 0x1d, 0x63, 0x18, 0x05, 0xc0, 0x00, 0x00, 0x00, 0x01,
      0x06, 0x00, 0x01] out rest := by
  refine ⟨take_iff.1 zlibFar_take, fun out rest h => ?_⟩
  have := takeWindowed_iff.2 h
  rw [zlibFar_takeWindowed] at this
  cases this

set_option maxRecDepth 100000 in
theorem gzipTrailing_prefix : Gzip.decompressPrefix [0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x03, 0xcb, 0x48, 0xcd, 0xc9, 0xc9, 0x07, 0x00, 0x86, 0xa6, 0x10, 0x36, 0x05,
    0x00, 0x00, 0x00, 0x58, 0x59, 0x5a] = some ([0x68, 0x65, 0x6c, 0x6c, 0x6f], [0x58, 0x59, 0x5a])
    := by
  decide +kernel

theorem gzip_trailing_witness :
    GzipFilePrefix [0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0xcb, 0x48, 0xcd,
      0xc9, 0xc9, 0x07, 0x00, 0x86, 0xa6, 0x10, 0x36, 0x05, 0x00, 0x00, 0x00, 0x58, 0x59, 0x5a]
      [0x68, 0x65, 0x6c, 0x6c, 0x6f] [0x58, 0x59, 0x5a] ∧
    ∀ out, ¬ GzipFile [0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0xcb, 0x48,
      0xcd, 0xc9, 0xc9, 0x07, 0x00, 0x86, 0xa6, 0x10, 0x36, 0x05, 0x00, 0x00, 0x00, 0x58, 0x59,
      0x5a] out := by
  refine ⟨decompressPrefix_iff.1 gzipTrailing_prefix, fun out h => ?_⟩
  have := decompressPrefix_iff.2 (gzipFile_iff_prefix.1 h)
  rw [gzipTrailing_prefix] at this
  simp at this

end Silmaril.Proofs.Formats.Compression.ContainerSpec
