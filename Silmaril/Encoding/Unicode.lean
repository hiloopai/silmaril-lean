module

public import Silmaril.Encoding.Carriers

/-!
# Unicode carrier maps

`String` (a sequence of Unicode scalar values) relates to bytes through text
encodings, each a pair of carrier maps:

| encoding | `String ⇒ bytes` | `bytes ⇒ String` |
|----------|------------------|------------------|
| UTF-8 (the default) | total, injective (`utf8`) | partial inverse (`utf8?`) |
| UTF-16LE / BE | total, injective | partial inverse (unpaired surrogates rejected) |
| Latin-1 (ISO-8859-1) | partial (code points ≤ U+00FF) | total, injective |

UTF-8 reuses Lean's `String.toUTF8` / `String.fromUTF8?`; `Utf8Chars` is an
independent transcription of the well-formed byte sequences of Unicode §3.9
Table 3-7 (RFC 3629: no overlongs, no surrogates, at most U+10FFFF), and
`utf8_spec` relates it to Lean's encoder.

Text encodings become carrier functors (`utf8Functor`, `utf8DecodeFunctor`,
…) and compose: `transcodeUtf8ToUtf16LE` is "decode UTF-8, encode UTF-16LE".
-/

@[expose] public section

open CategoryTheory

namespace Silmaril

namespace Unicode

/-! ## UTF-8 -/

/-- UTF-8 encoding of a string, as a byte list. -/
def utf8 (s : String) : List UInt8 := s.toUTF8.data.toList

/-- UTF-8 decoding: defined exactly on well-formed UTF-8. -/
def utf8? (b : List UInt8) : Option String := String.fromUTF8? b.toByteArray

theorem utf8_injective : Function.Injective utf8 := by
  intro s t h
  apply String.toByteArray_inj.mp
  have h' := congrArg List.toByteArray h
  simp only [utf8, String.toUTF8_eq_toByteArray] at h'
  have e : ∀ b : ByteArray, b.data.toList.toByteArray = b :=
    Carrier.byteArrayEquiv.left_inv
  rwa [e, e] at h'

theorem utf8?_eq_some_iff {b : List UInt8} {s : String} : utf8? b = some s ↔ utf8 s = b := by
  have e : ∀ b : ByteArray, b.data.toList.toByteArray = b := Carrier.byteArrayEquiv.left_inv
  unfold utf8? utf8 String.fromUTF8?
  constructor
  · intro h
    split at h
    · cases h
      simp [String.fromUTF8]
    · cases h
  · rintro rfl
    rw [String.toUTF8_eq_toByteArray, e, dite_eq_left_of_eq_true (eq_true s.isValidUTF8)]
    rfl

@[simp] theorem utf8?_utf8 (s : String) : utf8? (utf8 s) = some s :=
  utf8?_eq_some_iff.mpr rfl

/-- UTF-8 continuation byte `10xxxxxx`. -/
def Cont (b : UInt8) : Prop := 0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF

/-- One scalar value and its well-formed UTF-8 spelling (Unicode §3.9,
Table 3-7). -/
inductive Utf8Char : List UInt8 → Char → Prop where
  | one (b : UInt8) (c : Char) (hb : b.toNat ≤ 0x7F) (hc : c.toNat = b.toNat) :
      Utf8Char [b] c
  | two (b₁ b₂ : UInt8) (c : Char) (h₁ : 0xC2 ≤ b₁.toNat ∧ b₁.toNat ≤ 0xDF) (h₂ : Cont b₂)
      (hc : c.toNat = (b₁.toNat % 32) * 64 + b₂.toNat % 64) : Utf8Char [b₁, b₂] c
  | three (b₁ b₂ b₃ : UInt8) (c : Char)
      (h₁₂ : (b₁.toNat = 0xE0 ∧ 0xA0 ≤ b₂.toNat ∧ b₂.toNat ≤ 0xBF) ∨
        (((0xE1 ≤ b₁.toNat ∧ b₁.toNat ≤ 0xEC) ∨ b₁.toNat = 0xEE ∨ b₁.toNat = 0xEF) ∧
          Cont b₂) ∨
        (b₁.toNat = 0xED ∧ 0x80 ≤ b₂.toNat ∧ b₂.toNat ≤ 0x9F))
      (h₃ : Cont b₃)
      (hc : c.toNat = (b₁.toNat % 16) * 4096 + (b₂.toNat % 64) * 64 + b₃.toNat % 64) :
      Utf8Char [b₁, b₂, b₃] c
  | four (b₁ b₂ b₃ b₄ : UInt8) (c : Char)
      (h₁₂ : (b₁.toNat = 0xF0 ∧ 0x90 ≤ b₂.toNat ∧ b₂.toNat ≤ 0xBF) ∨
        ((0xF1 ≤ b₁.toNat ∧ b₁.toNat ≤ 0xF3) ∧ Cont b₂) ∨
        (b₁.toNat = 0xF4 ∧ 0x80 ≤ b₂.toNat ∧ b₂.toNat ≤ 0x8F))
      (h₃ : Cont b₃) (h₄ : Cont b₄)
      (hc : c.toNat = (b₁.toNat % 8) * 262144 + (b₂.toNat % 64) * 4096 +
        (b₃.toNat % 64) * 64 + b₄.toNat % 64) :
      Utf8Char [b₁, b₂, b₃, b₄] c

/-- Well-formed UTF-8 byte sequences and the scalar values they spell. -/
inductive Utf8Chars : List UInt8 → List Char → Prop where
  | nil : Utf8Chars [] []
  | cons {t ts : List UInt8} {c : Char} {cs : List Char} :
      Utf8Char t c → Utf8Chars ts cs → Utf8Chars (t ++ ts) (c :: cs)

/-- The RFC 3629 encoding relation on strings. -/
def utf8Rel : EncRel (List UInt8) String := fun b s => Utf8Chars b s.toList

/-- Valid scalar values: below the surrogates, or above them up to U+10FFFF. -/
theorem charToNat_valid (c : Char) :
    c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := by
  have h := c.valid
  simp only [UInt32.isValidChar] at h
  exact h

theorem charToNat_ofNat {n : Nat} (h : n < 0xD800 ∨ (0xDFFF < n ∧ n < 0x110000)) :
    (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := h
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]

/-- Every table spelling is Lean's encoding of its scalar value. -/
theorem utf8Char_eq {t : List UInt8} {c : Char} (h : Utf8Char t c) :
    t = String.utf8EncodeChar c := by
  have hv := charToNat_valid c
  unfold String.utf8EncodeChar
  simp only [Char.toNat_val]
  cases h with
  | one b c hb hc =>
    have := UInt8.toNat_lt b
    (repeat' split) <;> first | (exfalso; omega) | (simp only [List.cons.injEq, ← UInt8.toNat_inj, UInt8.toNat_ofNat', Nat.reducePow, and_true]; omega)
  | two b₁ b₂ c h₁ h₂ hc =>
    have := UInt8.toNat_lt b₁; have := UInt8.toNat_lt b₂
    unfold Cont at *
    (repeat' split) <;> first | (exfalso; omega) | (simp only [List.cons.injEq, ← UInt8.toNat_inj, UInt8.toNat_ofNat', Nat.reducePow, and_true]; omega)
  | three b₁ b₂ b₃ c h₁₂ h₃ hc =>
    have := UInt8.toNat_lt b₁; have := UInt8.toNat_lt b₂; have := UInt8.toNat_lt b₃
    unfold Cont at *
    (repeat' split) <;> first | (exfalso; omega) | (simp only [List.cons.injEq, ← UInt8.toNat_inj, UInt8.toNat_ofNat', Nat.reducePow, and_true]; omega)
  | four b₁ b₂ b₃ b₄ c h₁₂ h₃ h₄ hc =>
    have := UInt8.toNat_lt b₁; have := UInt8.toNat_lt b₂; have := UInt8.toNat_lt b₃
    have := UInt8.toNat_lt b₄
    unfold Cont at *
    (repeat' split) <;> first | (exfalso; omega) | (simp only [List.cons.injEq, ← UInt8.toNat_inj, UInt8.toNat_ofNat', Nat.reducePow, and_true]; omega)

/-- Lean's encoding of a scalar value is a table spelling. -/
theorem utf8Char_utf8EncodeChar (c : Char) : Utf8Char (String.utf8EncodeChar c) c := by
  have hv := charToNat_valid c
  unfold String.utf8EncodeChar
  simp only [Char.toNat_val]
  repeat' split
  · exact .one _ _ (by simp; omega) (by simp; omega)
  · exact .two _ _ _ (by simp; omega) (by simp [Cont]; omega) (by simp; omega)
  · exact .three _ _ _ _ (by simp [Cont]; omega) (by simp [Cont]; omega) (by simp; omega)
  · exact .four _ _ _ _ _ (by simp [Cont]; omega) (by simp [Cont]; omega) (by simp [Cont]; omega)
      (by simp; omega)
theorem utf8_eq_flatMap (s : String) : utf8 s = s.toList.flatMap String.utf8EncodeChar := by
  rw [utf8, String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList, List.utf8Encode,
    List.toList_data_toByteArray]

theorem utf8Chars_iff {b : List UInt8} {cs : List Char} :
    Utf8Chars b cs ↔ cs.flatMap String.utf8EncodeChar = b := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons hc _ ih => rw [List.flatMap_cons, ih, utf8Char_eq hc]
  · rintro rfl
    induction cs with
    | nil => exact .nil
    | cons c cs ih => exact .cons (utf8Char_utf8EncodeChar c) ih

/-- The transcribed table agrees with Lean's UTF-8 encoder. -/
theorem utf8_spec : utf8Rel = EncRel.ofFun utf8 := by
  funext b s
  apply propext
  change Utf8Chars b s.toList ↔ utf8 s = b
  rw [utf8Chars_iff, utf8_eq_flatMap]


/-- `utf8?` is a sound and complete decoder for the table. -/
theorem utf8?_sound : utf8Rel.DecoderSound utf8? := by
  intro b s h
  rw [utf8_spec]
  exact utf8?_eq_some_iff.mp h

theorem utf8?_complete : utf8Rel.DecoderComplete utf8? := by
  intro b s h
  rw [utf8_spec] at h
  exact utf8?_eq_some_iff.mpr h

/-! ## UTF-16 -/

/-- UTF-16 code units of a scalar value (one unit, or a surrogate pair). -/
def utf16Units (c : Char) : List Nat :=
  if c.toNat < 0x10000 then [c.toNat]
  else [0xD800 + (c.toNat - 0x10000) / 0x400, 0xDC00 + (c.toNat - 0x10000) % 0x400]

/-- Serialize a code unit, little- or big-endian. -/
def unitBytes (bigEndian : Bool) (u : Nat) : List UInt8 :=
  if bigEndian then [UInt8.ofNat (u / 256), UInt8.ofNat (u % 256)]
  else [UInt8.ofNat (u % 256), UInt8.ofNat (u / 256)]

/-- UTF-16 encoding. -/
def utf16 (bigEndian : Bool) (s : String) : List UInt8 :=
  s.toList.flatMap fun c => (utf16Units c).flatMap (unitBytes bigEndian)

/-- Read a code unit from two bytes in stream order. -/
def readUnit (bigEndian : Bool) (x y : UInt8) : Nat :=
  if bigEndian then x.toNat * 256 + y.toNat else y.toNat * 256 + x.toNat

/-- UTF-16 decoding to scalar values; unpaired surrogates and odd lengths are
rejected. -/
def utf16Chars (bigEndian : Bool) : List UInt8 → Option (List Char)
  | [] => some []
  | [_] => none
  | x :: y :: rest =>
      let u := readUnit bigEndian x y
      if u < 0xD800 ∨ 0xDFFF < u then (Char.ofNat u :: ·) <$> utf16Chars bigEndian rest
      else if u ≤ 0xDBFF then
        match rest with
        | x' :: y' :: rest' =>
            let v := readUnit bigEndian x' y'
            if 0xDC00 ≤ v ∧ v ≤ 0xDFFF then
              (Char.ofNat (0x10000 + (u - 0xD800) * 0x400 + (v - 0xDC00)) :: ·) <$>
                utf16Chars bigEndian rest'
            else none
        | _ => none
      else none

/-- UTF-16 decoding. -/
def utf16? (bigEndian : Bool) (b : List UInt8) : Option String :=
  String.ofList <$> utf16Chars bigEndian b

theorem readUnit_unitBytes (bigEndian : Bool) {u : Nat} (hu : u < 65536) (rest : List UInt8) :
    ∃ x y, unitBytes bigEndian u ++ rest = x :: y :: rest ∧ readUnit bigEndian x y = u := by
  cases bigEndian
  · refine ⟨_, _, rfl, ?_⟩
    simp [readUnit]; omega
  · refine ⟨_, _, rfl, ?_⟩
    simp [readUnit]; omega

theorem unitBytes_readUnit (bigEndian : Bool) (x y : UInt8) :
    unitBytes bigEndian (readUnit bigEndian x y) = [x, y] := by
  have := UInt8.toNat_lt x; have := UInt8.toNat_lt y
  cases bigEndian <;>
    simp only [unitBytes, readUnit, Bool.false_eq_true, ite_true, ite_false, List.cons.injEq,
      ← UInt8.toNat_inj, UInt8.toNat_ofNat', Nat.reducePow, and_true] <;> omega

/-- UTF-16 bytes of one scalar value. -/
abbrev utf16CharBytes (bigEndian : Bool) (c : Char) : List UInt8 :=
  (utf16Units c).flatMap (unitBytes bigEndian)

theorem utf16Chars_bmp (bigEndian : Bool) (x y : UInt8) (rest : List UInt8)
    (h : readUnit bigEndian x y < 0xD800 ∨ 0xDFFF < readUnit bigEndian x y) :
    utf16Chars bigEndian (x :: y :: rest) =
      (Char.ofNat (readUnit bigEndian x y) :: ·) <$> utf16Chars bigEndian rest := by
  rcases rest with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp only [utf16Chars, h, ite_true]

theorem utf16Chars_high_short (bigEndian : Bool) (x y : UInt8) (rest : List UInt8)
    (h : ¬(readUnit bigEndian x y < 0xD800 ∨ 0xDFFF < readUnit bigEndian x y))
    (hr : ∀ x' y' rest', rest ≠ x' :: y' :: rest') :
    utf16Chars bigEndian (x :: y :: rest) = none := by
  rcases rest with _ | ⟨a, _ | ⟨b, t⟩⟩
  · simp only [utf16Chars, h, ite_false]; split <;> rfl
  · simp only [utf16Chars, h, ite_false]; split <;> rfl
  · exact absurd rfl (hr a b t)

theorem utf16Chars_enc (bigEndian : Bool) (c : Char) (rest : List UInt8) :
    utf16Chars bigEndian (utf16CharBytes bigEndian c ++ rest) = (c :: ·) <$> utf16Chars bigEndian rest := by
  have hv := charToNat_valid c
  by_cases hc : c.toNat < 0x10000
  · obtain ⟨x, y, hxy, hu⟩ := readUnit_unitBytes bigEndian hc rest
    have e : utf16CharBytes bigEndian c ++ rest = x :: y :: rest := by
      simp only [utf16CharBytes, utf16Units, hc, ite_true, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      exact hxy
    have hc1 : c.toNat < 0xD800 ∨ 0xDFFF < c.toNat := by omega
    rw [e, utf16Chars_bmp _ _ _ _ (by rw [hu]; exact hc1), hu, Char.ofNat_toNat]
  · have h1 : 0xD800 + (c.toNat - 0x10000) / 0x400 < 65536 := by omega
    have h2 : 0xDC00 + (c.toNat - 0x10000) % 0x400 < 65536 := by omega
    obtain ⟨x', y', hxy', hv'⟩ := readUnit_unitBytes bigEndian h2 rest
    obtain ⟨x, y, hxy, hu⟩ := readUnit_unitBytes bigEndian h1 (x' :: y' :: rest)
    have e : utf16CharBytes bigEndian c ++ rest = x :: y :: x' :: y' :: rest := by
      simp only [utf16CharBytes, utf16Units, hc, ite_false, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc]
      rw [hxy', hxy]
    have c1 : ¬(0xD800 + (c.toNat - 0x10000) / 0x400 < 0xD800 ∨
        0xDFFF < 0xD800 + (c.toNat - 0x10000) / 0x400) := by omega
    have c2 : 0xD800 + (c.toNat - 0x10000) / 0x400 ≤ 0xDBFF := by omega
    have c3 : 0xDC00 ≤ 0xDC00 + (c.toNat - 0x10000) % 0x400 ∧
        0xDC00 + (c.toNat - 0x10000) % 0x400 ≤ 0xDFFF := by omega
    rw [e]
    simp only [utf16Chars, hu, hv', c1, c2, c3, ite_true, ite_false, and_self]
    have : 0x10000 + (0xD800 + (c.toNat - 0x10000) / 0x400 - 0xD800) * 0x400 +
        (0xDC00 + (c.toNat - 0x10000) % 0x400 - 0xDC00) = c.toNat := by omega
    rw [this, Char.ofNat_toNat]

theorem utf16Chars_sound (bigEndian : Bool) :
    ∀ (n : Nat) (b : List UInt8), b.length ≤ n → ∀ cs : List Char,
      utf16Chars bigEndian b = some cs → cs.flatMap (utf16CharBytes bigEndian) = b := by
  intro n
  induction n with
  | zero =>
    intro b hb cs h
    rcases b with _ | ⟨x, b⟩
    · simp only [utf16Chars, Option.some.injEq] at h; subst h; rfl
    · simp at hb
  | succ n ih =>
    intro b hb cs h
    rcases b with _ | ⟨x, _ | ⟨y, rest⟩⟩
    · simp only [utf16Chars, Option.some.injEq] at h; subst h; rfl
    · simp [utf16Chars] at h
    · have hx := UInt8.toNat_lt x; have hy := UInt8.toNat_lt y
      have hlt : readUnit bigEndian x y < 65536 := by
        cases bigEndian <;> simp only [readUnit, Bool.false_eq_true, ite_true, ite_false] <;> omega
      simp only [List.length_cons] at hb
      by_cases hu : readUnit bigEndian x y < 0xD800 ∨ 0xDFFF < readUnit bigEndian x y
      · rw [utf16Chars_bmp _ _ _ _ hu] at h
        obtain ⟨cs', hcs', rfl⟩ := Option.map_eq_some_iff.mp h
        have e := ih rest (by omega) cs' hcs'
        have hn := charToNat_ofNat (n := readUnit bigEndian x y) (by omega)
        simp only [List.flatMap_cons, e, utf16CharBytes, utf16Units, hn, hlt, ite_true,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, unitBytes_readUnit,
          List.cons_append, List.nil_append]
      · rcases rest with _ | ⟨x', _ | ⟨y', rest'⟩⟩
        · rw [utf16Chars_high_short _ _ _ _ hu (by simp)] at h; cases h
        · rw [utf16Chars_high_short _ _ _ _ hu (by simp)] at h; cases h
        · have hx' := UInt8.toNat_lt x'; have hy' := UInt8.toNat_lt y'
          have hlt' : readUnit bigEndian x' y' < 65536 := by
            cases bigEndian <;> simp only [readUnit, Bool.false_eq_true, ite_true, ite_false] <;>
              omega
          simp only [List.length_cons] at hb
          by_cases hhi : readUnit bigEndian x y ≤ 0xDBFF
          · by_cases hv : 0xDC00 ≤ readUnit bigEndian x' y' ∧ readUnit bigEndian x' y' ≤ 0xDFFF
            · simp only [utf16Chars, hu, hhi, hv, ite_true, ite_false] at h
              obtain ⟨cs', hcs', rfl⟩ := Option.map_eq_some_iff.mp h
              have e := ih rest' (by omega) cs' hcs'
              have hn := charToNat_ofNat (n := 0x10000 + (readUnit bigEndian x y - 0xD800) * 0x400 +
                (readUnit bigEndian x' y' - 0xDC00)) (by omega)
              have h1 : ¬ (0x10000 + (readUnit bigEndian x y - 0xD800) * 0x400 +
                (readUnit bigEndian x' y' - 0xDC00) < 0x10000) := by omega
              have h2 : 0xD800 + (0x10000 + (readUnit bigEndian x y - 0xD800) * 0x400 +
                (readUnit bigEndian x' y' - 0xDC00) - 0x10000) / 0x400 =
                  readUnit bigEndian x y := by omega
              have h3 : 0xDC00 + (0x10000 + (readUnit bigEndian x y - 0xD800) * 0x400 +
                (readUnit bigEndian x' y' - 0xDC00) - 0x10000) % 0x400 =
                  readUnit bigEndian x' y' := by omega
              simp only [List.flatMap_cons, e, utf16CharBytes, utf16Units, hn, h1, h2, h3, ite_false,
                List.flatMap_cons, List.flatMap_nil, List.append_nil, unitBytes_readUnit,
                List.cons_append, List.nil_append]
            · simp [utf16Chars, hu, hhi, hv] at h
          · simp [utf16Chars, hu, hhi] at h

theorem utf16Chars_eq_some_iff (bigEndian : Bool) {b : List UInt8} {cs : List Char} :
    utf16Chars bigEndian b = some cs ↔ cs.flatMap (utf16CharBytes bigEndian) = b := by
  constructor
  · exact utf16Chars_sound bigEndian _ b (Nat.le_refl _) cs
  · rintro rfl
    induction cs with
    | nil => rfl
    | cons c cs ih => rw [List.flatMap_cons, utf16Chars_enc, ih]; rfl

theorem utf16?_eq_some_iff (bigEndian : Bool) {b : List UInt8} {s : String} :
    utf16? bigEndian b = some s ↔ utf16 bigEndian s = b := by
  constructor
  · intro h
    obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [utf16, String.toList_ofList]
    exact (utf16Chars_eq_some_iff bigEndian).mp hcs
  · rintro rfl
    have h : utf16Chars bigEndian (utf16 bigEndian s) = some s.toList :=
      (utf16Chars_eq_some_iff bigEndian).mpr rfl
    rw [utf16?, h]
    exact congrArg some (String.ofList_toList)


@[simp] theorem utf16?_utf16 (bigEndian : Bool) (s : String) :
    utf16? bigEndian (utf16 bigEndian s) = some s :=
  (utf16?_eq_some_iff bigEndian).mpr rfl

theorem utf16_injective (bigEndian : Bool) : Function.Injective (utf16 bigEndian) := by
  intro s t h
  have hs := utf16?_utf16 bigEndian s
  rw [h, utf16?_utf16] at hs
  exact (Option.some.inj hs).symm

/-- An unpaired high surrogate is rejected. -/
example : utf16? false [0x00, 0xD8] = none := by decide

/-- A lone low surrogate is rejected. -/
example : utf16? false [0x00, 0xDC, 0x41, 0x00] = none := by decide

/-! ## Latin-1 -/

/-- Latin-1 decoding: every byte is the code point of the same value. -/
def latin1 (b : List UInt8) : String := String.ofList (b.map fun x => Char.ofNat x.toNat)

/-- Latin-1 encoding: defined only on code points `≤ U+00FF`. -/
def latin1? (s : String) : Option (List UInt8) :=
  s.toList.mapM fun c => if c.toNat < 256 then some (UInt8.ofNat c.toNat) else none

theorem latin1_mapM_iff : ∀ (cs : List Char) (b : List UInt8),
    cs.mapM (fun c => if c.toNat < 256 then some (UInt8.ofNat c.toNat) else none) = some b ↔
      b.map (fun x => Char.ofNat x.toNat) = cs
  | [], b => by cases b <;> simp
  | c :: cs, b => by
    rw [List.mapM_cons]
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq, latin1_mapM_iff cs]
    constructor
    · rintro ⟨x, hx, a, rfl, rfl⟩
      split at hx
      · cases hx
        rw [List.map_cons]
        congr 1
        rw [← Char.toNat_inj, charToNat_ofNat (by have := UInt8.toNat_lt (UInt8.ofNat c.toNat); omega)]
        simp; omega
      · cases hx
    · intro h
      rcases b with _ | ⟨x, b⟩
      · cases h
      · simp only [List.map_cons, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hx := UInt8.toNat_lt x
        have hn := charToNat_ofNat (n := x.toNat) (by omega)
        refine ⟨x, ?_, _, rfl, rfl⟩
        simp only [hn, hx, ite_true, UInt8.ofNat_toNat]

theorem latin1?_eq_some_iff {s : String} {b : List UInt8} :
    latin1? s = some b ↔ latin1 b = s := by
  rw [latin1?, latin1_mapM_iff, latin1]
  constructor
  · rintro h; rw [h, String.ofList_toList]
  · rintro rfl; rw [String.toList_ofList]

@[simp] theorem latin1?_latin1 (b : List UInt8) : latin1? (latin1 b) = some b :=
  latin1?_eq_some_iff.mpr rfl

theorem latin1_injective : Function.Injective latin1 := by
  intro b b' h
  have hb := latin1?_latin1 b
  rw [h, latin1?_latin1] at hb
  exact (Option.some.inj hb).symm

/-- Latin-1 encoding really is partial. -/
example : latin1? "€" = none := by decide

/-! ## Carrier functors -/

/-- Text encodings to UTF-8 byte encodings (the default). -/
abbrev utf8Functor : EncCat String ⥤ EncCat (List UInt8) := EncCat.pushFunctor utf8

/-- Byte encodings to text encodings, by partial UTF-8 decoding. -/
abbrev utf8DecodeFunctor : EncCat (List UInt8) ⥤ EncCat String :=
  EncCat.pushPartialFunctor utf8?

/-- Text encodings to UTF-16 byte encodings. -/
abbrev utf16Functor (bigEndian : Bool) : EncCat String ⥤ EncCat (List UInt8) :=
  EncCat.pushFunctor (utf16 bigEndian)

/-- Text encodings to Latin-1 byte encodings (partial: drops texts with code
points above U+00FF). -/
abbrev latin1Functor : EncCat String ⥤ EncCat (List UInt8) :=
  EncCat.pushPartialFunctor latin1?

/-- Latin-1 byte encodings to text encodings (total). -/
abbrev latin1DecodeFunctor : EncCat (List UInt8) ⥤ EncCat String :=
  EncCat.pushFunctor latin1

/-- Transcoding of byte encodings: decode UTF-8, encode UTF-16LE. -/
abbrev transcodeUtf8ToUtf16LE : EncCat (List UInt8) ⥤ EncCat (List UInt8) :=
  utf8DecodeFunctor ⋙ utf16Functor false

/-- Decoding after encoding UTF-8 is the identity on encodings. -/
theorem utf8Decode_utf8 (X : EncCat String) :
    utf8DecodeFunctor.obj (utf8Functor.obj X) = X :=
  EncCat.pushPartialFunctor_obj_pushFunctor_obj utf8?_utf8 X

/-- Transcoding a UTF-8 encoding of a text format yields its UTF-16LE encoding. -/
theorem transcode_utf8 (X : EncCat String) :
    transcodeUtf8ToUtf16LE.obj (utf8Functor.obj X) = (utf16Functor false).obj X := by
  change (utf16Functor false).obj (utf8DecodeFunctor.obj (utf8Functor.obj X)) = _
  rw [utf8Decode_utf8]

/-- The UTF-8 byte spellings of a text format are the well-formed UTF-8 byte
strings whose decoding is a text spelling. -/
theorem push_utf8_eq {α : Type} (E : EncRel String α) :
    E.push utf8 = E.pullPartial utf8? :=
  EncRel.push_eq_pullPartial (fun _ _ => utf8?_eq_some_iff) E

/-- UTF-8 preserves functionality of text encodings. -/
theorem functional_push_utf8 {α : Type} {E : EncRel String α} (hE : E.Functional) :
    (E.push utf8).Functional :=
  hE.push utf8_injective

end Unicode

end Silmaril
