module

public import Silmaril.Wasm.Tools.Gen.Cmd.WatLex.Defs

/-!
# `lexF` is silmaril's `lexGoFull` (raw proof)

The case analysis follows `Silmaril.Formats.SExpEncoding.Wat.lexGoFull_sound` branch by
branch: in each branch the recursive call is on a suffix of the input (`splitLine_some`,
`blockTail?_shorter`, `AnnotationTail.split`, `fullStrBody?_sound`, `QuotedIdTail.split`,
`idRun_append`), so the fuel bound `N` still exceeds its length, and the block comment's fuel
does not matter once it exceeds the comment's input (`blockTail?_fuel`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.WatLex

open Silmaril Silmaril.Formats.SExpEncoding Silmaril.Formats.SExpEncoding.Wat

set_option linter.unusedTactic false in
theorem blockTail?_shorter : ∀ (n : Nat) (cs rest : Chars), blockTail? n cs = some rest →
    rest.length < cs.length
  | 0, _, _, h => by simp [blockTail?] at h
  | _ + 1, [], _, h => by simp [blockTail?] at h
  | n + 1, c :: r, rest, h => by
    unfold blockTail? at h
    by_cases hs : c = ';'
    · simp only [hs, ↓reduceIte] at h
      by_cases hr : r.head? = some ')'
      · simp only [hr, ↓reduceIte, Option.some.injEq] at h
        subst h
        cases r <;> (simp_all; try omega)
      · simp only [hr, ↓reduceIte] at h
        have := blockTail?_shorter n r rest h
        simp; omega
    · simp only [hs, ↓reduceIte] at h
      by_cases hp : c = '('
      · simp only [hp, ↓reduceIte] at h
        by_cases hr : r.head? = some ';'
        · simp only [hr, ↓reduceIte] at h
          cases hm : blockTail? n r.tail with
          | none => simp [hm] at h
          | some mid =>
            simp only [hm, Option.bind_some] at h
            have h1 := blockTail?_shorter n r.tail mid hm
            have h2 := blockTail?_shorter n mid rest h
            cases r <;> (simp_all; try omega)
        · simp only [hr, ↓reduceIte] at h
          have := blockTail?_shorter n r rest h
          simp; omega
      · simp only [hp, ↓reduceIte] at h
        have := blockTail?_shorter n r rest h
        simp; omega

theorem blockTail?_fuel : ∀ (n m : Nat) (cs : Chars), cs.length < n → cs.length < m →
    blockTail? n cs = blockTail? m cs
  | 0, _, _, h, _ => by simp at h
  | _, 0, _, _, h => by simp at h
  | _ + 1, _ + 1, [], _, _ => rfl
  | n + 1, m + 1, c :: r, hn, hm => by
    have hn' : r.length < n := by simp at hn; omega
    have hm' : r.length < m := by simp at hm; omega
    have ht : r.tail.length ≤ r.length := by cases r <;> simp
    have ih := blockTail?_fuel n m r hn' hm'
    unfold blockTail?
    by_cases hs : c = ';'
    · simp only [hs, ↓reduceIte, ih]
    · simp only [hs, ↓reduceIte]
      by_cases hp : c = '('
      · simp only [hp, ↓reduceIte]
        by_cases hr : r.head? = some ';'
        · simp only [hr, ↓reduceIte]
          rw [blockTail?_fuel n m r.tail (by omega) (by omega)]
          cases hb : blockTail? m r.tail with
          | none => rfl
          | some mid =>
            have := blockTail?_shorter m r.tail mid hb
            exact blockTail?_fuel n m mid (by omega) (by omega)
        · simp only [hr, ↓reduceIte, ih]
      · simp only [hp, ↓reduceIte, ih]

theorem splitLine_shorter {p : Profile} {cs rest : Chars} {nl : Char}
    (h : (splitLine p cs).2 = some (nl, rest)) : rest.length < cs.length := by
  have e := (splitLine_some p cs h).1
  have := congrArg List.length e
  simp at this; omega

theorem lexF_eq (p : Profile) : ∀ (n N : Nat) (cs : Chars), cs.length < N →
    lexF p n N cs = lexGoFull p n cs
  | 0, _, _, _ => rfl
  | _ + 1, _, [], _ => rfl
  | n + 1, N, c :: r, hN => by
    have hr : r.length < N := by simp at hN; omega
    have ih : ∀ x : Chars, x.length ≤ r.length → lexF p n N x = lexGoFull p n x :=
      fun x hx => lexF_eq p n N x (by omega)
    have ht : r.tail.length ≤ r.length := by cases r <;> simp
    have hbt : blockTail? N r.tail = blockTail? (r.length + 1) r.tail :=
      blockTail?_fuel _ _ _ (by omega) (by omega)
    unfold lexF lexGoFull
    rw [hbt]
    by_cases hsp : IsSpaceChar c
    · simp only [hsp, ↓reduceIte]; exact ih r (Nat.le_refl _)
    simp only [hsp, ↓reduceIte]
    by_cases hlc : c = ';' ∧ r.head? = some ';'
    · simp only [hlc, and_self, ↓reduceIte]
      cases hs : (splitLine p r.tail).2 with
      | none => rfl
      | some x =>
        obtain ⟨nl, rest⟩ := x
        exact ih rest (by have := splitLine_shorter hs; omega)
    simp only [hlc, ↓reduceIte]
    by_cases hbc : c = '(' ∧ r.head? = some ';'
    · simp only [hbc, and_self, ↓reduceIte]
      cases hb : blockTail? (r.length + 1) r.tail with
      | none => rfl
      | some rest => exact ih rest (by have := blockTail?_shorter _ _ _ hb; omega)
    simp only [hbc, ↓reduceIte]
    by_cases hlp : c = '('
    · simp only [hlp, ↓reduceIte]
      by_cases ha : p = .core3 ∧ r.head? = some '@'
      · simp only [ha, and_self, ↓reduceIte]
        obtain ⟨rfl, _⟩ := ha
        cases han : annotationTail? r with
        | none => rfl
        | some a =>
          exact ih a.rest (by have := congrArg List.length a.split; simp at this; omega)
      · simp only [ha, ↓reduceIte, ih r (Nat.le_refl _)]
    simp only [hlp, ↓reduceIte]
    by_cases hrp : c = ')'
    · simp only [hrp, ↓reduceIte, ih r (Nat.le_refl _)]
    simp only [hrp, ↓reduceIte]
    by_cases hq : c = '"'
    · simp only [hq, ↓reduceIte]
      cases hs : fullStrBody? r with
      | none => rfl
      | some x =>
        obtain ⟨b, bytes, rest⟩ := x
        have hl : rest.length ≤ r.length := by
          have := congrArg List.length (fullStrBody?_sound hs).1; simp at this; omega
        simp only [ih rest hl]
    simp only [hq, ↓reduceIte]
    by_cases hd : p = .core3 ∧ c = '$' ∧ r.head? = some '"'
    · simp only [hd, and_self, ↓reduceIte]
      obtain ⟨rfl, _, _⟩ := hd
      cases hqi : quotedIdTail? r with
      | none => rfl
      | some q =>
        have hl : q.rest.length ≤ r.length := by
          have := congrArg List.length q.split; simp at this; omega
        simp only [ih q.rest hl]
    simp only [hd, ↓reduceIte]
    have hl : (idRun r).2.length ≤ r.length := by
      have := congrArg List.length (idRun_append r); simp at this; omega
    simp only [ih _ hl]

end Silmaril.Wasm.Tools.Gen.Cmd.WatLex
