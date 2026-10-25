module

public import Silmaril.Formats.SExp.EncodingWatExec

@[expose] public section

/-! # Checked WAT byte escapes

An additive fallback handles plain UTF-8 characters and exactly two hexadecimal
digits after a backslash. The original lexer and bracketer remain available,
and their successful results take priority. Unicode and mnemonic escapes remain
outside this executable extension.
-/

namespace Silmaril.Formats.SExpEncoding.Wat

open Silmaril

/-- Original string spelling, decoded bytes, and suffix after its closing quote. -/
def byteStrBody? : Chars → Option (Chars × List UInt8 × Chars)
  | [] => none
  | c :: r =>
      if c = '"' then some ([], [], r)
      else if c = '\\' then
        match r with
        | h₁ :: h₂ :: rest =>
            if IsHexDigit h₁ ∧ IsHexDigit h₂ then
              (byteStrBody? rest).map fun br =>
                ('\\' :: h₁ :: h₂ :: br.1,
                  UInt8.ofNat (16 * hexVal h₁ + hexVal h₂) :: br.2.1, br.2.2)
            else none
        | _ => none
      else if PlainStrChar c then
        (byteStrBody? r).map fun br =>
          (c :: br.1, String.utf8EncodeChar c ++ br.2.1, br.2.2)
      else none

theorem byteStrBody?_sound (cs b : Chars) (bytes : List UInt8) (rest : Chars)
    (h : byteStrBody? cs = some (b, bytes, rest)) :
    cs = b ++ '"' :: rest ∧ StringBody b bytes := by
  cases cs with
  | nil => simp [byteStrBody?] at h
  | cons c r =>
    unfold byteStrBody? at h
    by_cases hq : c = '"'
    · simp only [hq, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨by simp [hq], .nil⟩
    · simp only [hq, ↓reduceIte] at h
      by_cases hb : c = '\\'
      · subst c
        simp only [↓reduceIte] at h
        cases r with
        | nil => cases h
        | cons h₁ r =>
          cases r with
          | nil => cases h
          | cons h₂ r =>
            simp only at h
            by_cases hd : IsHexDigit h₁ ∧ IsHexDigit h₂
            · simp only [hd] at h
              cases hr : byteStrBody? r with
              | none => simp [hr] at h
              | some br =>
                obtain ⟨b', bytes', rest'⟩ := br
                simp only [hr, Option.map_some] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                obtain ⟨he, hs⟩ := byteStrBody?_sound r b' bytes' _ hr
                exact ⟨by simp [he], by simpa using StringBody.cons (StringElem.byte hd.1 hd.2) hs⟩
            · simp [hd] at h
      · simp only [hb, ↓reduceIte] at h
        split at h
        · rename_i hp
          cases hr : byteStrBody? r with
          | none => simp [hr] at h
          | some br =>
            obtain ⟨b', bytes', rest'⟩ := br
            simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            obtain ⟨he, hs⟩ := byteStrBody?_sound r b' bytes' _ hr
            obtain ⟨h₁, h₂, h₃, h₄⟩ := hp
            exact ⟨by simp [he], by
              simpa [charUtf8_eq] using
                (StringBody.cons (StringElem.char h₁ h₂ h₃ h₄) hs)⟩
        · cases h
termination_by cs.length

end Silmaril.Formats.SExpEncoding.Wat
