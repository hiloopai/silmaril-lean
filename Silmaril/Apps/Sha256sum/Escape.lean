module

public import Silmaril.Apps.Sha256sum.Basic

/-! # File-name escaping (compute output) and unescaping (`--check` input)

spec.md §5. A name is *problematic* when it contains a backslash, LF or CR. Without `-z`
such a name is printed escaped (`\` ↦ `\\`, LF ↦ `\n`, CR ↦ `\r`) on a line that starts
with one extra backslash. `--check` undoes this with `filename_unescape`, which rejects any
other escape, a trailing lone backslash and NUL.

## Theorems

- `unescape_escapeName`: unescaping inverts escaping on NUL-free names.
- `escapeName_injective`, `printedName_injective`: the printed form of a name determines
  the name.
- `escapeName_not_lf`, `escapeName_not_cr`: escaped names contain no LF or CR, which is
  what lets an escaped output line survive `--check`'s line splitting and CR stripping.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum

/-- Contains `\`, LF or CR. -/
def isProblemByte (c : UInt8) : Bool := c == 92 || c == 10 || c == 13

def problematic (s : Bytes) : Bool := s.any isProblemByte

/-- One byte of `escapeName`. -/
def escChar (c : UInt8) : Bytes :=
  if c = 92 then [92, 92] else if c = 10 then [92, 110] else if c = 13 then [92, 114] else [c]

def escapeName (s : Bytes) : Bytes := s.flatMap escChar

/-- `filename_unescape` (digest.c): the inverse of `escapeName` on its image. -/
def unescape : Bytes → Option Bytes
  | [] => some []
  | c :: t =>
    if c = 92 then
      match t with
      | [] => none
      | d :: t' =>
        if d = 110 then (10 :: ·) <$> unescape t'
        else if d = 114 then (13 :: ·) <$> unescape t'
        else if d = 92 then (92 :: ·) <$> unescape t'
        else none
    else if c = 0 then none
    else (c :: ·) <$> unescape t

/-- How compute mode prints a name without `-z`: escaped, with a leading backslash, when
problematic. (In compute output the leading backslash goes before the whole line; this
is the name-only form used in `--check` reports.) -/
def printedName (s : Bytes) : Bytes := if problematic s then 92 :: escapeName s else s

theorem escapeName_cons (c : UInt8) (s : Bytes) :
    escapeName (c :: s) = escChar c ++ escapeName s := rfl

theorem escapeName_append (s t : Bytes) : escapeName (s ++ t) = escapeName s ++ escapeName t := by
  simp [escapeName, List.flatMap_append]

theorem unescape_escapeName : ∀ s : Bytes, 0 ∉ s → unescape (escapeName s) = some s
  | [], _ => rfl
  | c :: s, h => by
    have hc : c ≠ 0 := fun e => h (e ▸ List.mem_cons_self ..)
    have hs : 0 ∉ s := fun m => h (List.mem_cons_of_mem _ m)
    have ih := unescape_escapeName s hs
    rw [escapeName_cons]
    unfold escChar
    by_cases h92 : c = 92
    · subst h92; simp [unescape, ih]
    by_cases h10 : c = 10
    · subst h10; simp [unescape, ih]
    by_cases h13 : c = 13
    · subst h13; simp [unescape, ih]
    rw [ite_eq_right h92, ite_eq_right h10, ite_eq_right h13]
    show unescape (c :: escapeName s) = _
    rw [unescape.eq_def]; dsimp only; rw [ite_eq_right h92, ite_eq_right hc, ih]; rfl

theorem escapeName_injective : ∀ s t : Bytes, 0 ∉ s → 0 ∉ t → escapeName s = escapeName t → s = t := by
  intro s t hs ht e
  have := unescape_escapeName s hs
  rw [e, unescape_escapeName t ht] at this
  exact (Option.some.inj this).symm

theorem problematic_iff (s : Bytes) : problematic s = true ↔ ∃ c ∈ s, isProblemByte c = true := by
  simp [problematic]

theorem printedName_injective (s t : Bytes) (hs : 0 ∉ s) (ht : 0 ∉ t)
    (e : printedName s = printedName t) : s = t := by
  unfold printedName at e
  cases ps : problematic s <;> cases pt : problematic t <;>
    simp only [ps, pt, Bool.false_eq_true, ↓reduceIte] at e
  · exact e
  · exfalso
    have : problematic s = true := by
      rw [problematic_iff]; exact ⟨92, by rw [e]; exact List.mem_cons_self .., by decide⟩
    simp_all
  · exfalso
    have : problematic t = true := by
      rw [problematic_iff]; exact ⟨92, by rw [← e]; exact List.mem_cons_self .., by decide⟩
    simp_all
  · exact escapeName_injective s t hs ht (List.cons.inj e).2

theorem escChar_not (c x : UInt8) (hx : x = 10 ∨ x = 13) : x ∉ escChar c := by
  unfold escChar
  rcases hx with rfl | rfl <;>
  · split
    · simp
    · split
      · simp
      · split
        · simp
        · simp only [List.mem_singleton]; intro h; simp_all

theorem escapeName_not_lf (s : Bytes) : (10 : UInt8) ∉ escapeName s := by
  simp only [escapeName, List.mem_flatMap, not_exists, not_and]
  exact fun c _ => escChar_not c 10 (.inl rfl)

theorem escapeName_not_cr (s : Bytes) : (13 : UInt8) ∉ escapeName s := by
  simp only [escapeName, List.mem_flatMap, not_exists, not_and]
  exact fun c _ => escChar_not c 13 (.inr rfl)

/-- A non-problematic name has no LF and no CR. -/
theorem not_problematic_mem (s : Bytes) (h : problematic s = false) (c : UInt8) (hc : c ∈ s) :
    c ≠ 92 ∧ c ≠ 10 ∧ c ≠ 13 := by
  have : ¬ ∃ c ∈ s, isProblemByte c = true := by rw [← problematic_iff]; simp [h]
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> exact this ⟨_, hc, by decide⟩

theorem escapeName_nul (s : Bytes) (h : 0 ∉ s) : (0 : UInt8) ∉ escapeName s := by
  simp only [escapeName, List.mem_flatMap, not_exists, not_and]
  intro c hc
  unfold escChar
  split
  · simp
  · split
    · simp
    · split
      · simp
      · simp only [List.mem_singleton]; rintro rfl; exact h hc

end Silmaril.Apps.Sha256sum
