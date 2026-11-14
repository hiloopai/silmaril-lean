module

public import Silmaril.Formats.Compression.Registry.Defs
public import Silmaril.Formats.Compression.Thms
public import Silmaril.Formats.Compression.Gzip.Thms
public import Silmaril.Formats.Compression.Zlib.Thms

/-! Proofs for `Silmaril.Formats.Compression.Registry.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.Registry

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Registry

/-! ## Chains -/

section Chain

variable {α ε : Type}

theorem decodeChain_append (dec : α → List UInt8 → Except ε (List UInt8)) (cs ds : List α)
    (bytes : List UInt8) :
    decodeChain dec (cs ++ ds) bytes = (decodeChain dec ds bytes).bind (decodeChain dec cs) := by
  induction cs with
  | nil => simp only [List.nil_append]; cases decodeChain dec ds bytes <;> rfl
  | cons c cs ih =>
    simp only [List.cons_append, decodeChain, ih]
    cases decodeChain dec ds bytes with
    | error e => rfl
    | ok mid => simp only [Except.bind]

theorem encodeChain_append (enc : α → List UInt8 → Option (List UInt8)) (cs ds : List α)
    (data : List UInt8) :
    encodeChain enc (cs ++ ds) data = (encodeChain enc cs data).bind (encodeChain enc ds) := by
  induction cs generalizing data with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.cons_append, encodeChain]
    cases enc c data with
    | none => rfl
    | some coded => exact ih coded

theorem decodeChain_encodeChain {dec : α → List UInt8 → Except ε (List UInt8)}
    {enc : α → List UInt8 → Option (List UInt8)}
    (h : ∀ c data coded, enc c data = some coded → dec c coded = .ok data) :
    ∀ (cs : List α) (data coded : List UInt8),
      encodeChain enc cs data = some coded → decodeChain dec cs coded = .ok data := by
  intro cs
  induction cs with
  | nil => intro data coded hc; cases hc; rfl
  | cons c cs ih =>
    intro data coded hc
    simp only [encodeChain] at hc
    cases he : enc c data with
    | none => rw [he] at hc; cases hc
    | some mid =>
      rw [he] at hc
      simp only [decodeChain, ih mid coded hc]
      exact h c data mid he

theorem decodeChain_congr {f g : α → List UInt8 → Except ε (List UInt8)} :
    ∀ {cs : List α}, (∀ c ∈ cs, ∀ b, f c b = g c b) → ∀ b, decodeChain f cs b = decodeChain g cs b
  | [], _, _ => rfl
  | c :: cs, h, b => by
    simp only [decodeChain]
    rw [decodeChain_congr (fun c hc => h c (List.mem_cons_of_mem _ hc)) b]
    cases decodeChain g cs b with
    | error e => rfl
    | ok mid => exact h c (List.mem_cons_self ..) mid

theorem decodeChain_neutral {dec : α → List UInt8 → Except ε (List UInt8)} {i : α}
    (hi : ∀ b, dec i b = .ok b) (cs ds : List α) (bytes : List UInt8) :
    decodeChain dec (cs ++ i :: ds) bytes = decodeChain dec (cs ++ ds) bytes := by
  rw [decodeChain_append, decodeChain_append]
  simp only [decodeChain]
  cases decodeChain dec ds bytes with
  | error e => rfl
  | ok mid => simp only [Except.bind, hi]

theorem encodeChain_neutral {enc : α → List UInt8 → Option (List UInt8)} {i : α}
    (hi : ∀ d, enc i d = some d) (cs ds : List α) (data : List UInt8) :
    encodeChain enc (cs ++ i :: ds) data = encodeChain enc (cs ++ ds) data := by
  rw [encodeChain_append, encodeChain_append]
  cases encodeChain enc cs data with
  | none => rfl
  | some mid => simp only [Option.bind_some, encodeChain, hi]

end Chain

/-! ## Guarded stages -/

section Guarded

variable {α : Type} {within : List UInt8 → List UInt8 → Bool}
  {dec : α → List UInt8 → Except (DecodeError α) (List UInt8)}

theorem guarded_eq_ok_iff {c : α} {bytes out : List UInt8} :
    guarded within dec c bytes = .ok out ↔ dec c bytes = .ok out ∧ within bytes out = true := by
  unfold guarded
  cases h : dec c bytes with
  | error e => simp
  | ok o =>
    by_cases hw : within bytes o = true
    · simp only [hw, ↓reduceIte, Except.ok.injEq]
      constructor
      · rintro rfl; exact ⟨rfl, hw⟩
      · rintro ⟨rfl, _⟩; rfl
    · simp only [hw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, Except.ok.injEq, false_iff,
        not_and]
      intro ho; subst ho; exact hw

theorem guardedChain_sound :
    ∀ {cs : List α} {bytes out : List UInt8},
      guardedChain within dec cs bytes = .ok out → decodeChain dec cs bytes = .ok out
  | [], _, _, h => h
  | c :: cs, bytes, out, h => by
    simp only [guardedChain, decodeChain] at h ⊢
    cases hg : decodeChain (guarded within dec) cs bytes with
    | error e => rw [hg] at h; cases h
    | ok mid =>
      rw [hg] at h
      rw [guardedChain_sound (cs := cs) hg]
      exact (guarded_eq_ok_iff.mp h).1

theorem guardedChain_complete :
    ∀ {cs : List α} {bytes out : List UInt8}, decodeChain dec cs bytes = .ok out →
      StagesWithin within dec cs bytes → guardedChain within dec cs bytes = .ok out
  | [], _, _, h, _ => h
  | c :: cs, bytes, out, h, ⟨hs, hc⟩ => by
    simp only [guardedChain, decodeChain] at h ⊢
    cases hd : decodeChain dec cs bytes with
    | error e => rw [hd] at h; cases h
    | ok mid =>
      rw [hd] at h
      have hg : guardedChain within dec cs bytes = .ok mid := guardedChain_complete hd hs
      simp only [guardedChain] at hg
      rw [hg]
      exact guarded_eq_ok_iff.mpr ⟨h, hc mid out hd h⟩

theorem guardedChain_within {c : α} {cs : List α} {bytes out : List UInt8}
    (h : guardedChain within dec (c :: cs) bytes = .ok out) :
    ∃ mid, guardedChain within dec cs bytes = .ok mid ∧ within mid out = true := by
  simp only [guardedChain, decodeChain] at h ⊢
  cases hg : decodeChain (guarded within dec) cs bytes with
  | error e => rw [hg] at h; cases h
  | ok mid => rw [hg] at h; exact ⟨mid, rfl, (guarded_eq_ok_iff.mp h).2⟩

/-- When the unguarded chain succeeds, the guarded one returns the same output or
reports `tooLarge` at some coding. -/
theorem guardedChain_agree :
    ∀ {cs : List α} {bytes out : List UInt8}, decodeChain dec cs bytes = .ok out →
      guardedChain within dec cs bytes = .ok out ∨
        ∃ c, guardedChain within dec cs bytes = .error (.tooLarge c)
  | [], _, _, h => .inl h
  | c :: cs, bytes, out, h => by
    simp only [guardedChain, decodeChain] at h ⊢
    cases hd : decodeChain dec cs bytes with
    | error e => rw [hd] at h; cases h
    | ok mid =>
      rw [hd] at h
      rcases guardedChain_agree (cs := cs) hd with hg | ⟨c', hg⟩
      · simp only [guardedChain] at hg
        rw [hg]
        simp only [guarded, h]
        by_cases hw : within mid out = true
        · exact .inl (by simp only [hw, ↓reduceIte])
        · exact .inr ⟨c, by simp only [hw, Bool.false_eq_true, ↓reduceIte]⟩
      · simp only [guardedChain] at hg
        rw [hg]
        exact .inr ⟨c', rfl⟩

end Guarded

/-! ## Profiles -/

theorem profile_stage_ok {p : Profile} {ext : Externals} {c : Coding} {bytes out : List UInt8}
    (h : p.stage ext c bytes = .ok out) :
    p.supports ext c = true ∧ stage ext c bytes = .ok out ∧ out.length ≤ p.limit bytes.length := by
  unfold Profile.stage at h
  by_cases hs : p.supports ext c = true
  · simp only [hs, ↓reduceIte] at h
    have ⟨h1, h2⟩ := guarded_eq_ok_iff.mp h
    exact ⟨hs, h1, of_decide_eq_true h2⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

theorem profile_decode_eq {p : Profile} {ext : Externals} {cs : List Coding}
    (hs : ∀ c ∈ cs, p.supports ext c = true) (bytes : List UInt8) :
    p.decode ext cs bytes = guardedChain p.within (stage ext) cs bytes :=
  decodeChain_congr (fun c hc b => by simp only [Profile.stage, hs c hc, ↓reduceIte]) bytes

theorem profile_decode_sound :
    ∀ {p : Profile} {ext : Externals} {cs : List Coding} {bytes out : List UInt8},
      p.decode ext cs bytes = .ok out → decodeAll ext cs bytes = .ok out
  | _, _, [], _, _, h => h
  | p, ext, c :: cs, bytes, out, h => by
    simp only [Profile.decode, decodeAll, decodeChain] at h ⊢
    cases hd : decodeChain (p.stage ext) cs bytes with
    | error e => rw [hd] at h; cases h
    | ok mid =>
      rw [hd] at h
      have hm : decodeAll ext cs bytes = .ok mid := profile_decode_sound hd
      simp only [decodeAll] at hm
      rw [hm]
      exact (profile_stage_ok h).2.1

theorem limit_le (p : Profile) (n : Nat) : p.limit n ≤ p.maxDecoded := by
  unfold Profile.limit
  cases p.maxRatio with
  | none => exact Nat.le_refl _
  | some r => exact Nat.min_le_left _ _

theorem profile_decode_le {p : Profile} {ext : Externals} {c : Coding} {cs : List Coding}
    {bytes out : List UInt8} (h : p.decode ext (c :: cs) bytes = .ok out) :
    out.length ≤ p.maxDecoded := by
  simp only [Profile.decode, decodeChain] at h
  cases hd : decodeChain (p.stage ext) cs bytes with
  | error e => rw [hd] at h; cases h
  | ok mid =>
    rw [hd] at h
    exact Nat.le_trans (profile_stage_ok h).2.2 (limit_le p _)

theorem profile_decode_complete {p : Profile} {ext : Externals} {cs : List Coding}
    {bytes out : List UInt8} (hs : ∀ c ∈ cs, p.supports ext c = true)
    (hd : decodeAll ext cs bytes = .ok out) (hw : StagesWithin p.within (stage ext) cs bytes) :
    p.decode ext cs bytes = .ok out := by
  rw [profile_decode_eq hs]
  exact guardedChain_complete hd hw

/-! ## Bounded member decoders -/

theorem bounded_eq_ok_iff {d : Decoder} {limit : Nat} {bytes out rest : List UInt8} :
    d.bounded limit bytes = .ok (out, rest) ↔
      d bytes = some (out, rest) ∧ out.length ≤ limit := by
  unfold Decoder.bounded
  cases h : d bytes with
  | none => simp
  | some r =>
    obtain ⟨o, re⟩ := r
    by_cases hl : o.length ≤ limit
    · simp only [hl, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨⟨rfl, rfl⟩, hl⟩
      · rintro ⟨⟨rfl, rfl⟩, _⟩; exact ⟨rfl, rfl⟩
    · simp only [hl, ↓reduceIte, reduceCtorEq, Option.some.injEq, Prod.mk.injEq, false_iff,
        not_and]
      rintro ⟨rfl, rfl⟩; exact hl

theorem bounded_tooLarge_iff {d : Decoder} {limit : Nat} {bytes : List UInt8} :
    d.bounded limit bytes = .error .tooLarge ↔
      ∃ out rest, d bytes = some (out, rest) ∧ limit < out.length := by
  unfold Decoder.bounded
  cases h : d bytes with
  | none => simp
  | some r =>
    obtain ⟨o, re⟩ := r
    by_cases hl : o.length ≤ limit
    · simp only [hl, ↓reduceIte, reduceCtorEq, Option.some.injEq, Prod.mk.injEq, false_iff,
        not_exists, not_and]
      rintro a b ⟨rfl, rfl⟩; exact Nat.not_lt_of_le hl
    · simp only [hl, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, true_iff]
      exact ⟨o, re, ⟨rfl, rfl⟩, Nat.lt_of_not_le hl⟩

theorem bounded_malformed_iff {d : Decoder} {limit : Nat} {bytes : List UInt8} :
    d.bounded limit bytes = .error .malformed ↔ d bytes = none := by
  unfold Decoder.bounded
  cases h : d bytes with
  | none => simp
  | some r =>
    obtain ⟨o, re⟩ := r
    by_cases hl : o.length ≤ limit
    · simp [hl]
    · simp [hl]

theorem sound_bounded {i : Incremental} {d : Decoder} (hs : i.Sound d) {initial : List UInt8}
    {calls : List i.Call} {out : List UInt8} {limit : Nat}
    (hdone : i.status (i.run (i.start initial) calls) = .done out) (hl : out.length ≤ limit) :
    ∃ rest, d.bounded limit (initial ++ i.delivered calls) = .ok (out, rest) := by
  obtain ⟨rest, h⟩ := Incremental.sound_decode hs hdone
  exact ⟨rest, bounded_eq_ok_iff.mpr ⟨h, hl⟩⟩

/-! ## The registry's codecs -/

theorem gzip_members_encoder (data : List UInt8) :
    Gzip.decoder.members (Gzip.encoder data) = some data := by
  have h := Gzip.members_encoder (xs := [data]) (List.cons_ne_nil _ _)
  simpa using h

theorem gzip_trailing_zero (data : List UInt8) :
    Gzip.decoder.members (Gzip.encoder data ++ [0]) = none := by
  have h := Gzip.roundTrip data [0]
  have h0 : Gzip.decoder [0] = none := by decide
  unfold Decoder.members
  generalize (Gzip.encoder data ++ [0]).length = n
  simp only [Decoder.membersFuel, h]
  cases n <;> simp [Decoder.membersFuel, h0]

theorem encoder_roundTrip (ext : Externals) {c : Coding} {e : Encoder} (he : c.encoder? = some e)
    (data : List UInt8) : stage ext c (e data) = .ok data := by
  cases c <;> simp only [Coding.encoder?, reduceCtorEq, Option.some.injEq] at he <;> subst he
  · rfl
  · simp only [stage, Coding.decoder?, gzip_members_encoder]
  · simp only [stage, Coding.decoder?, Zlib.roundTrip.whole]

theorem decodeAll_encodeAll (ext : Externals) {cs : List Coding} {data coded : List UInt8}
    (h : encodeAll cs data = some coded) : decodeAll ext cs coded = .ok data := by
  refine decodeChain_encodeChain (fun c d b hb => ?_) cs data coded h
  cases he : c.encoder? with
  | none => rw [he] at hb; cases hb
  | some e =>
    rw [he] at hb
    cases hb
    exact encoder_roundTrip ext he d

theorem profile_decode_single {p : Profile} {ext : Externals} {c : Coding} {e : Encoder}
    (hs : p.supports ext c = true) (he : c.encoder? = some e) {data : List UInt8}
    (hl : data.length ≤ p.limit (e data).length) : p.decode ext [c] (e data) = .ok data := by
  simp only [Profile.decode, decodeChain, Profile.stage, hs, ↓reduceIte]
  exact guarded_eq_ok_iff.mpr ⟨encoder_roundTrip ext he data, decide_eq_true hl⟩

end Silmaril.Proofs.Formats.Compression.Registry
