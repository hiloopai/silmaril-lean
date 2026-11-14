module

public import Silmaril.Encoding.Unicode

/-!
# ASCII

ASCII (RFC 20, ANSI X3.4-1968) is the 7-bit code: the code points `0 … 127`,
one per byte.  This module is the canonical ASCII vocabulary of the library:

* the character classes of RFC 20 §4 on code points (`isControl`, `isPrintable`,
  `isGraphic`, `isUpper`, `isLower`, `isAlpha`, `isDigit`, `isAlnum`), each a
  `Bool` on `Char`; control (`0x00–0x1F`, `0x7F`) and printable (`0x20–0x7E`)
  partition ASCII (`isAscii_iff_isControl_or_isPrintable`);
* case mapping `toLower` / `toUpper` and ASCII case-insensitive equality
  `ciEq`, with their laws (idempotence, absorption, `ciEq` an equivalence),
  and the identification with core's (ASCII-only) `Char.toLower` / `Char.toUpper`;
* the byte carrier maps `encode?` (strings ⇒ bytes, defined exactly on ASCII
  strings) and `decode?` (bytes ⇒ strings, defined exactly on bytes `< 0x80`),
  exact partial inverses of each other;
* the bridge to UTF-8 (`Silmaril.Encoding.Unicode`): an ASCII string encodes
  in UTF-8 as itself, one byte per character (`utf8_of_isAsciiStr`), and UTF-8
  decoding of ASCII bytes is ASCII decoding (`utf8?_of_ascii`).

RFC 20 lists DEL (`0x7F`) among the control characters while noting it is "not
a control character in the strict sense"; `isControl` follows the table and
includes it.  RFC 20 §4.2 lists SP (`0x20`) among the graphic characters
("normally non-printing"); `isPrintable` includes it (C `isprint`) and
`isGraphic` excludes it (C `isgraph`).

The library contains ad hoc ASCII helpers that predate this module, e.g.
`Silmaril.Net.Hpack.ascii s = s.toList.map (·.toNat.toUInt8)`, which is
`s.toList.map Ascii.toByte` by definition; on ASCII strings it is therefore
`Unicode.utf8 s` (`utf8_of_isAsciiStr`).  (The `Encoding` tree does not import
`Net`, so this relationship is documented rather than stated here.)
-/

@[expose] public section

namespace Silmaril

namespace Ascii

/-! ## Code points and character classes -/

/-- An ASCII character: code point below `0x80`. -/
def isAscii (c : Char) : Bool := c.toNat < 0x80

/-- RFC 20 §4.1 control characters: `0x00–0x1F` and DEL `0x7F`. -/
def isControl (c : Char) : Bool := c.toNat < 0x20 || c.toNat == 0x7F

/-- RFC 20 §4.2 graphic characters including SP: `0x20–0x7E` (C `isprint`). -/
def isPrintable (c : Char) : Bool := 0x20 ≤ c.toNat && c.toNat ≤ 0x7E

/-- Visible graphic characters, excluding SP: `0x21–0x7E` (C `isgraph`). -/
def isGraphic (c : Char) : Bool := 0x21 ≤ c.toNat && c.toNat ≤ 0x7E

/-- Upper-case letters `A–Z` (`0x41–0x5A`). -/
def isUpper (c : Char) : Bool := 0x41 ≤ c.toNat && c.toNat ≤ 0x5A

/-- Lower-case letters `a–z` (`0x61–0x7A`). -/
def isLower (c : Char) : Bool := 0x61 ≤ c.toNat && c.toNat ≤ 0x7A

/-- Letters. -/
def isAlpha (c : Char) : Bool := isUpper c || isLower c

/-- Decimal digits `0–9` (`0x30–0x39`). -/
def isDigit (c : Char) : Bool := 0x30 ≤ c.toNat && c.toNat ≤ 0x39

/-- Letters and digits. -/
def isAlnum (c : Char) : Bool := isAlpha c || isDigit c

/-- An ASCII string. -/
def isAsciiStr (s : String) : Bool := s.toList.all isAscii

theorem isAscii_iff_isControl_or_isPrintable (c : Char) :
    isAscii c = true ↔ isControl c = true ∨ isPrintable c = true := by
  simp only [isAscii, isControl, isPrintable, decide_eq_true_eq, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq]
  omega

theorem not_isControl_and_isPrintable (c : Char) :
    ¬ (isControl c = true ∧ isPrintable c = true) := by
  simp only [isControl, isPrintable, decide_eq_true_eq, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq]
  omega

theorem isPrintable_iff (c : Char) :
    isPrintable c = true ↔ c = ' ' ∨ isGraphic c = true := by
  simp only [isPrintable, isGraphic, decide_eq_true_eq, Bool.and_eq_true,
    ← Char.toNat_inj]
  show _ ↔ c.toNat = 32 ∨ _
  omega

theorem isAscii_of_isPrintable {c : Char} (h : isPrintable c = true) : isAscii c = true := by
  simp only [isPrintable, isAscii, decide_eq_true_eq, Bool.and_eq_true] at *
  omega

theorem isGraphic_of_isAlnum {c : Char} (h : isAlnum c = true) : isGraphic c = true := by
  simp only [isAlnum, isAlpha, isUpper, isLower, isDigit, isGraphic, decide_eq_true_eq,
    Bool.or_eq_true, Bool.and_eq_true] at *
  omega

theorem toNat_ofNat_of_lt {n : Nat} (h : n < 0xD800) : (Char.ofNat n).toNat = n :=
  Unicode.charToNat_ofNat (.inl h)

/-! ## Case mapping -/

/-- Lower-case an ASCII letter; every other character is unchanged. -/
def toLower (c : Char) : Char := if isUpper c then Char.ofNat (c.toNat + 0x20) else c

/-- Upper-case an ASCII letter; every other character is unchanged. -/
def toUpper (c : Char) : Char := if isLower c then Char.ofNat (c.toNat - 0x20) else c

/-- ASCII case-insensitive equality of characters. -/
def ciEq (a b : Char) : Bool := toLower a == toLower b

theorem toNat_toLower (c : Char) :
    (toLower c).toNat = if isUpper c then c.toNat + 0x20 else c.toNat := by
  unfold toLower
  split
  · next h =>
    simp only [isUpper, decide_eq_true_eq, Bool.and_eq_true] at h
    exact toNat_ofNat_of_lt (by omega)
  · rfl

theorem toNat_toUpper (c : Char) :
    (toUpper c).toNat = if isLower c then c.toNat - 0x20 else c.toNat := by
  unfold toUpper
  split
  · next h =>
    simp only [isLower, decide_eq_true_eq, Bool.and_eq_true] at h
    exact toNat_ofNat_of_lt (by omega)
  · rfl

/-- Case laws reduce to code-point arithmetic. -/
private theorem ext_toNat {a b : Char} (h : a.toNat = b.toNat) : a = b := Char.toNat_inj.mp h

private theorem cases_toLower (c : Char) :
    ((0x41 ≤ c.toNat ∧ c.toNat ≤ 0x5A) ∧ (toLower c).toNat = c.toNat + 0x20) ∨
      (¬ (0x41 ≤ c.toNat ∧ c.toNat ≤ 0x5A) ∧ (toLower c).toNat = c.toNat) := by
  rw [toNat_toLower]
  simp only [isUpper, decide_eq_true_eq, Bool.and_eq_true]
  split <;> simp_all

private theorem cases_toUpper (c : Char) :
    ((0x61 ≤ c.toNat ∧ c.toNat ≤ 0x7A) ∧ (toUpper c).toNat = c.toNat - 0x20) ∨
      (¬ (0x61 ≤ c.toNat ∧ c.toNat ≤ 0x7A) ∧ (toUpper c).toNat = c.toNat) := by
  rw [toNat_toUpper]
  simp only [isLower, decide_eq_true_eq, Bool.and_eq_true]
  split <;> simp_all

@[simp] theorem toLower_toLower (c : Char) : toLower (toLower c) = toLower c := by
  apply ext_toNat
  rcases cases_toLower c with h | h <;> rcases cases_toLower (toLower c) with h' | h' <;> omega

@[simp] theorem toUpper_toUpper (c : Char) : toUpper (toUpper c) = toUpper c := by
  apply ext_toNat
  rcases cases_toUpper c with h | h <;> rcases cases_toUpper (toUpper c) with h' | h' <;> omega

@[simp] theorem toLower_toUpper (c : Char) : toLower (toUpper c) = toLower c := by
  apply ext_toNat
  rcases cases_toUpper c with h | h <;> rcases cases_toLower (toUpper c) with h' | h' <;>
    rcases cases_toLower c with h'' | h'' <;> omega

@[simp] theorem toUpper_toLower (c : Char) : toUpper (toLower c) = toUpper c := by
  apply ext_toNat
  rcases cases_toLower c with h | h <;> rcases cases_toUpper (toLower c) with h' | h' <;>
    rcases cases_toUpper c with h'' | h'' <;> omega

theorem toLower_eq_self_iff (c : Char) : toLower c = c ↔ isUpper c = false := by
  rw [← Char.toNat_inj, toNat_toLower]
  cases isUpper c <;> simp

theorem toUpper_eq_self_iff (c : Char) : toUpper c = c ↔ isLower c = false := by
  rw [← Char.toNat_inj, toNat_toUpper]
  simp only [isLower, decide_eq_true_eq, Bool.and_eq_true]
  split
  · simp only [Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not]; omega
  · simp_all

theorem isAscii_toLower (c : Char) : isAscii (toLower c) = isAscii c := by
  simp only [isAscii]
  rcases cases_toLower c with h | h
  · rw [h.2]; exact decide_eq_decide.mpr (by omega)
  · rw [h.2]

theorem isAscii_toUpper (c : Char) : isAscii (toUpper c) = isAscii c := by
  simp only [isAscii]
  rcases cases_toUpper c with h | h
  · rw [h.2]; exact decide_eq_decide.mpr (by omega)
  · rw [h.2]

/-- `toLower` is core's ASCII-only `Char.toLower`. -/
theorem toLower_eq_char_toLower (c : Char) : toLower c = c.toLower := by
  apply ext_toNat
  rcases cases_toLower c with h | h <;> rw [h.2]
  · simp [Char.toLower, UInt32.le_iff_toNat_le, h.1]; omega
  · have : c.toLower = c := by
      simp only [Char.toLower, ge_iff_le, UInt32.le_iff_toNat_le, Char.toNat_val, dite_eq_right_iff]
      exact fun a => absurd (by simpa using a) h.1
    rw [this]

/-- `toUpper` is core's ASCII-only `Char.toUpper`. -/
theorem toUpper_eq_char_toUpper (c : Char) : toUpper c = c.toUpper := by
  apply ext_toNat
  rcases cases_toUpper c with h | h <;> rw [h.2]
  · simp [Char.toUpper, UInt32.le_iff_toNat_le, h.1]; omega
  · have : c.toUpper = c := by
      simp only [Char.toUpper, UInt32.le_iff_toNat_le, Char.toNat_val, dite_eq_right_iff]
      exact fun a => absurd (by simpa using a) h.1
    rw [this]

/-- `ciEq` is an equivalence relation. -/
theorem ciEq_equivalence : Equivalence (fun a b => ciEq a b = true) where
  refl a := beq_self_eq_true _
  symm h := by simp only [ciEq, beq_iff_eq] at *; exact h.symm
  trans h₁ h₂ := by simp only [ciEq, beq_iff_eq] at *; exact h₁.trans h₂

theorem ciEq_iff (a b : Char) : ciEq a b = true ↔ toLower a = toLower b := by simp [ciEq]

theorem ciEq_toUpper_left (a b : Char) : ciEq (toUpper a) b = ciEq a b := by simp [ciEq]


/-! ## Strings -/

/-- Lower-case the ASCII letters of a string. -/
def lowerStr (s : String) : String := String.ofList (s.toList.map toLower)

/-- Upper-case the ASCII letters of a string. -/
def upperStr (s : String) : String := String.ofList (s.toList.map toUpper)

/-- ASCII case-insensitive equality of strings (characterwise `ciEq`). -/
def ciEqStr (s t : String) : Bool := s.toList.map toLower == t.toList.map toLower

@[simp] theorem lowerStr_lowerStr (s : String) : lowerStr (lowerStr s) = lowerStr s := by
  simp [lowerStr, Function.comp_def]

@[simp] theorem upperStr_upperStr (s : String) : upperStr (upperStr s) = upperStr s := by
  simp [upperStr, Function.comp_def]

@[simp] theorem lowerStr_upperStr (s : String) : lowerStr (upperStr s) = lowerStr s := by
  simp [lowerStr, upperStr, Function.comp_def]

@[simp] theorem upperStr_lowerStr (s : String) : upperStr (lowerStr s) = upperStr s := by
  simp [lowerStr, upperStr, Function.comp_def]

theorem ciEqStr_iff (s t : String) : ciEqStr s t = true ↔ lowerStr s = lowerStr t := by
  simp [ciEqStr, lowerStr, String.ofList_inj]

private theorem map_eq_map_iff_forall₂ {α β : Type} (f : α → β) :
    ∀ (l l' : List α), l.map f = l'.map f ↔ List.Forall₂ (fun a b => f a = f b) l l'
  | [], [] => by simp
  | [], _ :: _ => ⟨fun h => by simp at h, fun h => by cases h⟩
  | _ :: _, [] => ⟨fun h => by simp at h, fun h => by cases h⟩
  | a :: l, b :: l' => by simp [map_eq_map_iff_forall₂ f l l']

theorem ciEqStr_iff_forall₂ (s t : String) :
    ciEqStr s t = true ↔ List.Forall₂ (fun a b => ciEq a b = true) s.toList t.toList := by
  simp only [ciEqStr, beq_iff_eq, ciEq_iff]
  exact map_eq_map_iff_forall₂ _ _ _



/-- `ciEqStr` is an equivalence relation. -/
theorem ciEqStr_equivalence : Equivalence (fun s t => ciEqStr s t = true) where
  refl s := by simp [ciEqStr_iff]
  symm h := by simp only [ciEqStr_iff] at *; exact h.symm
  trans h₁ h₂ := by simp only [ciEqStr_iff] at *; exact h₁.trans h₂

/-! ## Bytes -/

/-- The byte of a character (meaningful on ASCII characters). -/
def toByte (c : Char) : UInt8 := c.toNat.toUInt8

/-- The character of a byte (meaningful on bytes `< 0x80`). -/
def ofByte (b : UInt8) : Char := Char.ofNat b.toNat

/-- ASCII encoding: defined exactly on ASCII strings, one byte per character. -/
def encode? (s : String) : Option (List UInt8) :=
  if isAsciiStr s then some (s.toList.map toByte) else none

/-- ASCII decoding: defined exactly on byte strings with every byte `< 0x80`. -/
def decode? (b : List UInt8) : Option String :=
  if b.all (·.toNat < 0x80) then some (String.ofList (b.map ofByte)) else none

theorem toNat_toByte {c : Char} (h : isAscii c = true) : (toByte c).toNat = c.toNat := by
  simp only [isAscii, decide_eq_true_eq] at h
  simp only [toByte]
  simp; omega

theorem toNat_ofByte {b : UInt8} (h : b.toNat < 0x80) : (ofByte b).toNat = b.toNat :=
  toNat_ofNat_of_lt (by omega)

theorem ofByte_toByte {c : Char} (h : isAscii c = true) : ofByte (toByte c) = c := by
  apply ext_toNat
  have := toNat_toByte h
  simp only [isAscii, decide_eq_true_eq] at h
  rw [toNat_ofByte (by omega), this]

theorem toByte_ofByte {b : UInt8} (h : b.toNat < 0x80) : toByte (ofByte b) = b := by
  apply UInt8.toNat_inj.mp
  rw [toNat_toByte (by simp [isAscii, toNat_ofByte h]; omega), toNat_ofByte h]

theorem isAscii_ofByte {b : UInt8} (h : b.toNat < 0x80) : isAscii (ofByte b) = true := by
  simp [isAscii, toNat_ofByte h, h]

theorem decode?_encode? {s : String} (h : isAsciiStr s = true) :
    decode? (s.toList.map toByte) = some s := by
  simp only [isAsciiStr, List.all_eq_true] at h
  have hb : (s.toList.map toByte).all (·.toNat < 0x80) = true := by
    simp only [List.all_map, List.all_eq_true, Function.comp_apply, decide_eq_true_eq]
    intro c hc
    have := h c hc
    rw [toNat_toByte this]
    simpa [isAscii] using this
  rw [decode?, ite_eq_left hb]
  congr
  conv => rhs; rw [← String.ofList_toList (s := s)]
  congr 1
  rw [List.map_map]
  conv => rhs; rw [← List.map_id s.toList]
  exact List.map_congr_left fun c hc => ofByte_toByte (h c hc)

/-- `encode?` and `decode?` are exact partial inverses. -/
theorem encode?_eq_some_iff {s : String} {b : List UInt8} :
    encode? s = some b ↔ decode? b = some s := by
  constructor
  · intro h
    unfold encode? at h
    split at h
    · cases h; exact decode?_encode? (by assumption)
    · cases h
  · intro h
    unfold decode? at h
    split at h
    · next hb =>
      cases h
      simp only [List.all_eq_true, decide_eq_true_eq] at hb
      have ha : isAsciiStr (String.ofList (b.map ofByte)) = true := by
        simp only [isAsciiStr, String.toList_ofList, List.all_map, List.all_eq_true,
          Function.comp_apply]
        exact fun x hx => isAscii_ofByte (hb x hx)
      rw [encode?, ite_eq_left ha, String.toList_ofList, List.map_map]
      congr
      conv => rhs; rw [← List.map_id b]
      exact List.map_congr_left fun x hx => toByte_ofByte (hb x hx)
    · cases h

theorem length_of_encode? {s : String} {b : List UInt8} (h : encode? s = some b) :
    b.length = s.length := by
  unfold encode? at h
  split at h
  · cases h; simp [String.length_toList]
  · cases h

/-! ## UTF-8 -/

/-- An ASCII character is its own one-byte UTF-8 encoding. -/
theorem utf8EncodeChar_of_isAscii {c : Char} (h : isAscii c = true) :
    String.utf8EncodeChar c = [toByte c] := by
  simp only [isAscii, decide_eq_true_eq] at h
  simp [String.utf8EncodeChar, toByte, Char.toNat_val, show c.toNat ≤ 0x7f by omega]

/-- An ASCII string encodes in UTF-8 as itself, one byte per character. -/
theorem utf8_of_isAsciiStr {s : String} (h : isAsciiStr s = true) :
    Unicode.utf8 s = s.toList.map toByte := by
  simp only [isAsciiStr, List.all_eq_true] at h
  rw [Unicode.utf8_eq_flatMap]
  generalize s.toList = l at h
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp [utf8EncodeChar_of_isAscii h.1, ih h.2]

theorem length_utf8_of_isAsciiStr {s : String} (h : isAsciiStr s = true) :
    (Unicode.utf8 s).length = s.length := by
  simp [utf8_of_isAsciiStr h, String.length_toList]

/-- ASCII encoding is UTF-8 encoding restricted to ASCII strings. -/
theorem encode?_eq_some_iff_utf8 {s : String} {b : List UInt8} :
    encode? s = some b ↔ isAsciiStr s = true ∧ Unicode.utf8 s = b := by
  unfold encode?
  split
  · next h => simp [h, utf8_of_isAsciiStr h]
  · next h => simp [h]

/-- UTF-8 decoding of ASCII bytes is ASCII decoding. -/
theorem utf8?_of_ascii {b : List UInt8} (hb : b.all (·.toNat < 0x80) = true) :
    Unicode.utf8? b = decode? b := by
  have hd : decode? b = some (String.ofList (b.map ofByte)) := by rw [decode?, ite_eq_left hb]
  rw [hd, Unicode.utf8?_eq_some_iff]
  exact (encode?_eq_some_iff_utf8.mp (encode?_eq_some_iff.mpr hd)).2

end Ascii

end Silmaril
