module

public import Silmaril.Wasm.Wit.Name.Defs

/-!
# WIT identifiers: the characters they contain

A valid identifier (`ValidId`) is made of ASCII letters, digits and `-`
(`plain_of_validId`), and starts with a letter (`validId_head`). Later modules use
this to show that identifiers survive the binary encoding (no `: / @ . [`) and the
text printer (`idOk`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit

/-- A character of an identifier: an ASCII letter, a digit or `-`. -/
def plainChar (c : Char) : Bool := c.isLower || c.isUpper || c.isDigit || c == '-'

/-- Every character is `plainChar`. -/
def Plain (s : String) : Prop := ∀ c ∈ s.toList, plainChar c = true

theorem splitDash_ne_nil : ∀ l : List Char, splitDash l ≠ []
  | [] => by simp [splitDash]
  | d :: ds => by
    unfold splitDash
    split
    · simp
    · split <;> simp

theorem splitDash_cons_ne {d : Char} (hd : d ≠ '-') (ds : List Char) :
    ∃ w ws, splitDash ds = w :: ws ∧ splitDash (d :: ds) = (d :: w) :: ws := by
  cases hs : splitDash ds with
  | nil => exact absurd hs (splitDash_ne_nil ds)
  | cons w ws => exact ⟨w, ws, rfl, by simp [splitDash, hd, hs]⟩

/-- A character other than `-` lies in a word of `splitDash`. -/
theorem mem_splitDash {c : Char} (hd : c ≠ '-') :
    ∀ {l : List Char}, c ∈ l → ∃ w ∈ splitDash l, c ∈ w
  | [], h => absurd h List.not_mem_nil
  | d :: ds, h => by
    by_cases hdd : d = '-'
    · have hc : c ∈ ds := (List.mem_cons.mp h).resolve_left fun e => hd (e.trans hdd)
      obtain ⟨w, hw, hcw⟩ := mem_splitDash hd hc
      have hs : splitDash (d :: ds) = [] :: splitDash ds := by simp [splitDash, hdd]
      exact ⟨w, hs ▸ List.mem_cons_of_mem _ hw, hcw⟩
    · obtain ⟨w, ws, hs, hs'⟩ := splitDash_cons_ne hdd ds
      rcases List.mem_cons.mp h with rfl | hc
      · exact ⟨c :: w, hs' ▸ List.mem_cons_self, List.mem_cons_self⟩
      · obtain ⟨w', hw', hcw'⟩ := mem_splitDash hd hc
        rcases List.mem_cons.mp (hs ▸ hw') with rfl | hw''
        · exact ⟨d :: w', hs' ▸ List.mem_cons_self, List.mem_cons_of_mem _ hcw'⟩
        · exact ⟨w', hs' ▸ List.mem_cons_of_mem _ hw'', hcw'⟩

/-- The characters of a word are letters or digits. -/
theorem word_chars : ∀ {w : List Char}, Word w → ∀ c ∈ w, c.isLower ∨ c.isUpper ∨ c.isDigit
  | [], h, _, _ => h.elim
  | d :: ds, h, c, hc => by
    rcases List.mem_cons.mp hc with rfl | hc
    · rcases h with ⟨hl, _⟩ | ⟨hu, _⟩
      · exact .inl hl
      · exact .inr (.inl hu)
    · rcases h with ⟨_, hl⟩ | ⟨_, hu⟩
      · rcases hl c hc with h | h
        · exact .inl h
        · exact .inr (.inr h)
      · rcases hu c hc with h | h
        · exact .inr (.inl h)
        · exact .inr (.inr h)

/-- **A valid identifier is made of letters, digits and `-`.** -/
theorem plain_of_validId {s : Name} (h : ValidId s) : Plain s := by
  intro c hc
  by_cases hd : c = '-'
  · simp [plainChar, hd]
  · obtain ⟨w, hw, hcw⟩ := mem_splitDash hd hc
    rcases word_chars (h w hw) c hcw with h | h | h <;> simp [plainChar, h]

/-- A plain string does not contain a non-plain character. -/
theorem not_mem_of_plain {s : String} (h : Plain s) {c : Char} (hc : plainChar c = false) :
    c ∉ s.toList := fun hm => absurd (h c hm) (by simp [hc])

/-- **A valid identifier starts with a letter.** -/
theorem validId_head {s : Name} (h : ValidId s) : ∃ c cs, s.toList = c :: cs ∧ (c.isLower ∨ c.isUpper) := by
  unfold ValidId at h
  generalize s.toList = l at h ⊢
  cases l with
  | nil => exact (h [] (by simp [splitDash])).elim
  | cons c cs =>
    refine ⟨c, cs, rfl, ?_⟩
    by_cases hd : c = '-'
    · exact (h [] (by simp [splitDash, hd])).elim
    · cases hs : splitDash cs with
      | nil =>
        have hw := h [c] (by simp [splitDash, hd, hs])
        rcases hw with ⟨hl, _⟩ | ⟨hu, _⟩
        · exact .inl hl
        · exact .inr hu
      | cons w ws =>
        have hw := h (c :: w) (by simp [splitDash, hd, hs])
        rcases hw with ⟨hl, _⟩ | ⟨hu, _⟩
        · exact .inl hl
        · exact .inr hu

/-- The characters of a valid SemVer identifier are `semverChar`. -/
theorem ValidBuildId.chars {s : String} (h : ValidBuildId s) : ∀ c ∈ s.toList, semverChar c = true := h.2

theorem ValidPreId.build {s : String} (h : ValidPreId s) : ValidBuildId s := h.1

/-! ## Characters that never occur in identifiers -/

theorem plainChar_colon : plainChar ':' = false := by decide
theorem plainChar_slash : plainChar '/' = false := by decide
theorem plainChar_at : plainChar '@' = false := by decide
theorem plainChar_dot : plainChar '.' = false := by decide
theorem plainChar_lbrack : plainChar '[' = false := by decide

theorem Plain.head_ne {s : String} (h : Plain s) : s.toList.head? ≠ some '[' := by
  intro hh
  cases hs : s.toList with
  | nil => rw [hs] at hh; cases hh
  | cons c cs =>
    rw [hs] at hh
    have : c = '[' := by simpa using hh
    exact not_mem_of_plain h plainChar_lbrack (by rw [hs, this]; exact List.mem_cons_self)

end Silmaril.Wasm.Wit
