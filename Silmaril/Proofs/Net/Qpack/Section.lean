module

public import Silmaril.Net.Qpack.Section.Defs
public import Silmaril.Proofs.Net.Qpack.Instruction

/-!
# QPACK encoded field sections: proofs

For `Silmaril.Net.Qpack.Section.Thms` (RFC 9204 §4.5, §2.2).
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Qpack

open Silmaril.Net.Qpack
open Silmaril.Net.Hpack (Entry encodeInt decodeInt decodeInt_encodeInt)

/-! ## Required Insert Count and Base -/

/-- §4.5.1.1 round trip: a non-zero Required Insert Count in the window
`(TotalNumberOfInserts - MaxEntries, TotalNumberOfInserts + MaxEntries]` is reconstructed. -/
theorem decodeRic_encodeRic {M T ric : Nat}
    (h : ric = 0 ∨ (0 < M ∧ ric ≤ T + M ∧ T < ric + M)) :
    decodeRic M T (encodeRic M ric) = some ric := by
  by_cases hric : ric = 0
  · subst hric; simp [encodeRic, decodeRic]
  obtain ⟨hM, h1, h2⟩ := h.resolve_left hric
  have hdm := Nat.mod_add_div ric (2 * M)
  have hlt := Nat.mod_lt ric (show 0 < 2 * M by omega)
  have hA1 := Nat.div_mul_le_self (T + M) (2 * M)
  have hA2 := Nat.lt_div_mul_add (a := T + M) (show 0 < 2 * M by omega)
  simp only [encodeRic, hric, ↓reduceIte, decodeRic, Nat.add_one_ne_zero]
  generalize ric % (2 * M) = m at hdm hlt ⊢
  generalize ric / (2 * M) = k at hdm
  generalize (T + M) / (2 * M) = q at hA1 hA2 ⊢
  generalize hF : 2 * M = F at hdm hlt hA1 hA2 ⊢
  rw [Nat.mul_comm F k] at hdm
  -- `ric` lies in the wrapping block of `MaxValue` or the one before
  have hk1 : k < q + 1 := by
    have : k * F < (q + 1) * F := by rw [Nat.add_mul, Nat.one_mul]; omega
    exact Nat.lt_of_mul_lt_mul_right this
  have hk2 : q < k + 2 := by
    have : q * F < (k + 2) * F := by rw [Nat.add_mul]; omega
    exact Nat.lt_of_mul_lt_mul_right this
  simp only [show ¬ F < m + 1 by omega, ↓reduceIte,
    show q * F + (m + 1) - 1 = q * F + m by omega]
  rcases (show k = q ∨ q = k + 1 by omega) with rfl | rfl
  · simp only [show ¬ T + M < k * F + m by omega, ↓reduceIte,
      show ¬ k * F + m = 0 by omega]
    congr 1; omega
  · rw [Nat.add_mul, Nat.one_mul] at hA1 hA2 ⊢
    simp only [show T + M < k * F + F + m by omega, ↓reduceIte,
      show ¬ k * F + F + m ≤ F by omega]
    congr 1; omega

theorem decodeBase_encodeBase (ric base : Nat) :
    decodeBase ric (encodeBase ric base).1 (encodeBase ric base).2 = some base := by
  unfold encodeBase decodeBase
  by_cases h : ric ≤ base
  · simp only [h, ↓reduceIte, Bool.false_eq_true, Option.some.injEq]; omega
  · simp only [h, ↓reduceIte, show ric - base - 1 < ric by omega, Option.some.injEq]; omega

/-! ## Wire format -/

theorem decodePrefix_encode (p : SectionPrefix) (rest : List UInt8) :
    decodePrefix (p.encode ++ rest) = some (p, rest) := by
  have hs : (if p.sign then 0x80 else 0) % 2 ^ 7 = 0 ∧ (if p.sign then 0x80 else 0) < 256 := by
    cases p.sign <;> decide
  obtain ⟨b, tl, he, h1, h2, hd⟩ := encodeInt_split (n := 7) (by decide) hs.1 hs.2 p.deltaBase rest
  have hsign : decide (128 ≤ b.toNat) = p.sign := by
    cases hp : p.sign <;> simp only [hp, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq,
      decide_eq_false_iff_not] at h1 h2 ⊢ <;> omega
  unfold SectionPrefix.encode decodePrefix
  rw [List.append_assoc, decodeInt_encodeInt (by decide) (by decide) (by decide), he]
  simp only [hd, hsign]

theorem decodeValueAfter_encode (mk : List UInt8 → FieldLine) (v rest : List UInt8) :
    decodeValueAfter mk (encodeStringN 8 0 v ++ rest) = some (mk v, rest) := by
  unfold decodeValueAfter
  rw [decodeStringN_encodeStringN (by decide) (by decide) (by decide) (by decide)]

theorem flagIf_lt (b : Bool) (w : Nat) : flagIf b w = 0 ∨ flagIf b w = w := by
  cases b <;> simp [flagIf]

theorem decodeFieldLine_encode (l : FieldLine) (rest : List UInt8) :
    decodeFieldLine (l.encode ++ rest) = some (l, rest) := by
  cases l with
  | indexed r =>
    cases r with
    | static i =>
      obtain ⟨b, tl, he, h1, h2, hd⟩ :=
        encodeInt_split (n := 6) (hi := 0xc0) (by decide) (by decide) (by decide) i rest
      simp only [FieldLine.encode, he, decodeFieldLine, show 128 ≤ b.toNat by omega,
        show 192 ≤ b.toNat by omega, ↓reduceIte, hd, Option.map_some]
    | dynamic i =>
      obtain ⟨b, tl, he, h1, h2, hd⟩ :=
        encodeInt_split (n := 6) (hi := 0x80) (by decide) (by decide) (by decide) i rest
      simp only [FieldLine.encode, he, decodeFieldLine, show 128 ≤ b.toNat by omega,
        show ¬ 192 ≤ b.toNat by omega, ↓reduceIte, hd, Option.map_some]
    | postBase i =>
      obtain ⟨b, tl, he, h1, h2, hd⟩ :=
        encodeInt_split (n := 4) (hi := 0x10) (by decide) (by decide) (by decide) i rest
      simp only [FieldLine.encode, he, decodeFieldLine, show ¬ 128 ≤ b.toNat by omega,
        show ¬ 64 ≤ b.toNat by omega, show ¬ 32 ≤ b.toNat by omega,
        show 16 ≤ b.toNat by omega, ↓reduceIte, hd, Option.map_some]
  | literalRef n r v =>
    have hn : (decide (96 ≤ 0x40 + flagIf n 0x20 + 0)) = n := by cases n <;> decide
    cases r with
    | static i =>
      have hs : (0x50 + flagIf n 0x20) % 2 ^ 4 = 0 ∧ 0x50 + flagIf n 0x20 < 256 := by
        cases n <;> decide
      obtain ⟨b, tl, he, h1, h2, hd⟩ :=
        encodeInt_split (n := 4) (by decide) hs.1 hs.2 i (encodeStringN 8 0 v ++ rest)
      have hb : decide (96 ≤ b.toNat) = n := by
        cases n <;> simp only [flagIf, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq,
          decide_eq_false_iff_not] at h1 h2 ⊢ <;> omega
      have hf := flagIf_lt n 0x20
      simp only [FieldLine.encode, List.append_assoc, he, decodeFieldLine,
        show ¬ 128 ≤ b.toNat by omega, show 64 ≤ b.toNat by omega,
        show 16 ≤ b.toNat % 32 by omega, ↓reduceIte, hd, decodeValueAfter_encode, hb]
    | dynamic i =>
      have hs : (0x40 + flagIf n 0x20) % 2 ^ 4 = 0 ∧ 0x40 + flagIf n 0x20 < 256 := by
        cases n <;> decide
      obtain ⟨b, tl, he, h1, h2, hd⟩ :=
        encodeInt_split (n := 4) (by decide) hs.1 hs.2 i (encodeStringN 8 0 v ++ rest)
      have hb : decide (96 ≤ b.toNat) = n := by
        cases n <;> simp only [flagIf, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq,
          decide_eq_false_iff_not] at h1 h2 ⊢ <;> omega
      have hf := flagIf_lt n 0x20
      simp only [FieldLine.encode, List.append_assoc, he, decodeFieldLine,
        show ¬ 128 ≤ b.toNat by omega, show 64 ≤ b.toNat by omega,
        show ¬ 16 ≤ b.toNat % 32 by omega, ↓reduceIte, hd, decodeValueAfter_encode, hb]
    | postBase i =>
      have hs : (flagIf n 0x08) % 2 ^ 3 = 0 ∧ flagIf n 0x08 < 256 := by
        cases n <;> decide
      obtain ⟨b, tl, he, h1, h2, hd⟩ :=
        encodeInt_split (n := 3) (by decide) hs.1 hs.2 i (encodeStringN 8 0 v ++ rest)
      have hb : decide (8 ≤ b.toNat) = n := by
        cases n <;> simp only [flagIf, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq,
          decide_eq_false_iff_not] at h1 h2 ⊢ <;> omega
      have hf := flagIf_lt n 0x08
      simp only [FieldLine.encode, List.append_assoc, he, decodeFieldLine,
        show ¬ 128 ≤ b.toNat by omega, show ¬ 64 ≤ b.toNat by omega,
        show ¬ 32 ≤ b.toNat by omega, show ¬ 16 ≤ b.toNat by omega, ↓reduceIte, hd,
        decodeValueAfter_encode, hb]
  | literal n name v =>
    have hs : (0x20 + flagIf n 0x10) % 2 ^ 4 = 0 ∧ 0x20 + flagIf n 0x10 < 256 := by
      cases n <;> decide
    obtain ⟨b, tl, he, h1, h2, hd⟩ := encodeStringN_split (n := 4) (by decide) (by decide)
      hs.1 hs.2 name (encodeStringN 8 0 v ++ rest)
    have hb : decide (48 ≤ b.toNat) = n := by
      cases n <;> simp only [flagIf, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq,
        decide_eq_false_iff_not, Nat.reduceSub, Nat.reducePow] at h1 h2 ⊢ <;> omega
    have hf := flagIf_lt n 0x10
    simp only [Nat.reduceSub, Nat.reducePow] at h2
    simp only [FieldLine.encode, List.append_assoc, he, decodeFieldLine,
      show ¬ 128 ≤ b.toNat by omega, show ¬ 64 ≤ b.toNat by omega,
      show 32 ≤ b.toNat by omega, ↓reduceIte, hd, decodeValueAfter_encode, hb]

theorem FieldLine.encode_ne_nil (l : FieldLine) : l.encode ≠ [] := by
  cases l with
  | indexed r => cases r <;> simp [FieldLine.encode, encodeInt_ne_nil]
  | literalRef n r v => cases r <;> simp [FieldLine.encode, encodeInt_ne_nil]
  | literal n name v => simp [FieldLine.encode, encodeStringN_ne_nil]

theorem decodeEncodedSection_encode (s : EncodedSection) :
    decodeEncodedSection s.encode = some s := by
  unfold EncodedSection.encode decodeEncodedSection
  rw [decodePrefix_encode]
  simp only [decodeMany_flatMap _ _ decodeFieldLine_encode FieldLine.encode_ne_nil,
    Option.map_some]

/-! ## Decoding against the table -/

theorem lookupDyn_ok {t : DynTable} {ric a : Nat} {e : Entry} (h : lookupDyn t ric a = .ok e) :
    a < ric ∧ t.lookupAbs a = some e := by
  unfold lookupDyn at h
  split at h
  · next ha =>
    split at h
    · next he => cases h; exact ⟨ha, he⟩
    · cases h
  · cases h

theorem resolveRef_ok_abs {t : DynTable} {ric base : Nat} {r : Ref} {e : Entry}
    (h : resolveRef t ric base r = .ok e) {a : Nat} (ha : r.abs base = some a) :
    a < ric ∧ t.lookupAbs a = some e := by
  cases r with
  | static i => cases ha
  | dynamic i =>
    simp only [Ref.abs] at ha
    simp only [resolveRef, ha] at h
    exact lookupDyn_ok h
  | postBase p =>
    simp only [Ref.abs, Option.some.injEq] at ha
    simp only [resolveRef, ha] at h
    exact lookupDyn_ok h

theorem resolveRef_ok_static {t : DynTable} {base : Nat} {r : Ref} {e : Entry}
    (h : resolveRef t 0 base r = .ok e) : r.isStatic = true := by
  cases r with
  | static i => rfl
  | dynamic i =>
    simp only [resolveRef] at h
    split at h
    · have := (lookupDyn_ok h).1; omega
    · cases h
  | postBase p => have := (lookupDyn_ok h).1; omega

theorem FieldLine.resolve_ok_ref {t : DynTable} {ric base : Nat} {l : FieldLine} {e : Entry}
    (h : l.resolve t ric base = .ok e) {r : Ref} (hr : l.ref? = some r) :
    ∃ e', resolveRef t ric base r = .ok e' := by
  cases l with
  | indexed r' =>
    simp only [FieldLine.ref?, Option.some.injEq] at hr
    subst hr; exact ⟨e, h⟩
  | literalRef n r' v =>
    simp only [FieldLine.ref?, Option.some.injEq] at hr
    subst hr
    simp only [FieldLine.resolve] at h
    split at h
    · next e' he' => exact ⟨e', he'⟩
    · cases h
  | literal n name v => cases hr

theorem FieldLine.resolve_ok_absRef {t : DynTable} {ric base : Nat} {l : FieldLine} {e : Entry}
    (h : l.resolve t ric base = .ok e) {a : Nat} (ha : l.absRef base = some a) :
    a < ric ∧ (t.lookupAbs a).isSome := by
  simp only [FieldLine.absRef, Option.bind_eq_some_iff] at ha
  obtain ⟨r, hr, ha⟩ := ha
  obtain ⟨e', he'⟩ := FieldLine.resolve_ok_ref h hr
  obtain ⟨h1, h2⟩ := resolveRef_ok_abs he' ha
  exact ⟨h1, by simp [h2]⟩

theorem FieldLine.resolve_ok_staticOnly {t : DynTable} {base : Nat} {l : FieldLine} {e : Entry}
    (h : l.resolve t 0 base = .ok e) : l.staticOnly = true := by
  unfold FieldLine.staticOnly
  split
  · next r hr =>
    obtain ⟨e', he'⟩ := FieldLine.resolve_ok_ref h hr
    exact resolveRef_ok_static he'
  · rfl

theorem resolveLines_ok {t : DynTable} {ric base : Nat} {ls : List FieldLine} {fs : List Entry}
    (h : resolveLines t ric base ls = .ok fs) :
    fs.length = ls.length ∧ ∀ l ∈ ls, ∃ e, l.resolve t ric base = .ok e := by
  induction ls generalizing fs with
  | nil => simp only [resolveLines, Except.ok.injEq] at h; subst h; simp
  | cons l ls ih =>
    simp only [resolveLines] at h
    split at h
    · cases h
    · next e he =>
      split at h
      · cases h
      · next es hes =>
        cases h
        obtain ⟨h1, h2⟩ := ih hes
        refine ⟨by simp [h1], ?_⟩
        intro l' hl'
        rcases List.mem_cons.mp hl' with rfl | hl'
        · exact ⟨e, he⟩
        · exact h2 l' hl'

theorem decodeFieldSection_blocked_iff (t : DynTable) (s : EncodedSection) (ric : Nat) :
    decodeFieldSection t s = .ok (.blocked ric) ↔
      decodeRic t.maxEntries t.insertCount s.pre.encRic = some ric ∧ t.insertCount < ric := by
  unfold decodeFieldSection
  split
  · next hn => simp only [reduceCtorEq, hn, false_and]
  · next r hr =>
    simp only [hr, Option.some.injEq]
    by_cases hlt : t.insertCount < r
    · simp only [hlt, ↓reduceIte, Except.ok.injEq, SectionResult.blocked.injEq]
      constructor
      · rintro rfl; exact ⟨rfl, hlt⟩
      · rintro ⟨rfl, -⟩; rfl
    · simp only [hlt, ↓reduceIte]
      constructor
      · intro h
        split at h
        · cases h
        · split at h <;> cases h
      · rintro ⟨rfl, h⟩; exact absurd h hlt

theorem decodeFieldSection_decoded {t : DynTable} {s : EncodedSection} {ric : Nat}
    {fs : List Entry} (h : decodeFieldSection t s = .ok (.decoded ric fs)) :
    decodeRic t.maxEntries t.insertCount s.pre.encRic = some ric ∧ ric ≤ t.insertCount ∧
      ∃ base, decodeBase ric s.pre.sign s.pre.deltaBase = some base ∧
        resolveLines t ric base s.lines = .ok fs := by
  unfold decodeFieldSection at h
  split at h
  · cases h
  · next r hr =>
    split at h
    · cases h
    · next hlt =>
      split at h
      · cases h
      · next base hb =>
        split at h
        · next fs' hfs =>
          simp only [Except.ok.injEq, SectionResult.decoded.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hr, by omega, base, hb, hfs⟩
        · cases h

theorem decodeFieldSection_refs {t : DynTable} {s : EncodedSection} {ric : Nat}
    {fs : List Entry} (h : decodeFieldSection t s = .ok (.decoded ric fs)) :
    ∃ base, decodeBase ric s.pre.sign s.pre.deltaBase = some base ∧
      ∀ l ∈ s.lines, ∀ a, l.absRef base = some a → a < ric ∧ (t.lookupAbs a).isSome := by
  obtain ⟨-, -, base, hb, hl⟩ := decodeFieldSection_decoded h
  refine ⟨base, hb, fun l hl' a ha => ?_⟩
  obtain ⟨e, he⟩ := (resolveLines_ok hl).2 l hl'
  exact FieldLine.resolve_ok_absRef he ha

theorem decodeFieldSection_length {t : DynTable} {s : EncodedSection} {ric : Nat}
    {fs : List Entry} (h : decodeFieldSection t s = .ok (.decoded ric fs)) :
    fs.length = s.lines.length := by
  obtain ⟨-, -, base, -, hl⟩ := decodeFieldSection_decoded h
  exact (resolveLines_ok hl).1

theorem decodeFieldSection_ric_zero {t : DynTable} {s : EncodedSection} (h0 : s.pre.encRic = 0)
    {r : SectionResult} (h : decodeFieldSection t s = .ok r) :
    ∃ fs, r = .decoded 0 fs ∧ ∀ l ∈ s.lines, l.staticOnly = true := by
  have hric : decodeRic t.maxEntries t.insertCount s.pre.encRic = some 0 := by
    simp [h0, decodeRic]
  cases r with
  | blocked ric =>
    have := (decodeFieldSection_blocked_iff t s ric).mp h
    rw [hric, Option.some.injEq] at this
    omega
  | decoded ric fs =>
    obtain ⟨hr, -, base, -, hl⟩ := decodeFieldSection_decoded h
    rw [hric, Option.some.injEq] at hr
    subst hr
    refine ⟨fs, rfl, fun l hl' => ?_⟩
    obtain ⟨e, he⟩ := (resolveLines_ok hl).2 l hl'
    exact FieldLine.resolve_ok_staticOnly he

theorem lookupDyn_error_of_le {t : DynTable} {ric a : Nat} (h : ric ≤ a) :
    lookupDyn t ric a = .error .decompressionFailed := by
  simp only [lookupDyn, show ¬ a < ric by omega, ↓reduceIte]

theorem lookupDyn_error_of_evicted {t : DynTable} {ric a : Nat} (h : t.lookupAbs a = none) :
    lookupDyn t ric a = .error .decompressionFailed := by
  unfold lookupDyn
  split
  · simp only [h]
  · rfl

end Silmaril.Proofs.Net.Qpack
