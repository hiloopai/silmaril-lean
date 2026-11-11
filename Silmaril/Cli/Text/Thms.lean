module

import all Init.Data.String.Search
import all Init.Data.String.Slice.Numeric
import all Init.Data.Repr
import all Init.Data.String.Legacy
public import Batteries.Data.String.Lemmas

/-!
# Facts about strings that command lines need

PROVED (standard axioms), namespace `Silmaril.Cli.Text`:

* `toNat?_toString`: `(toString n).toNat? = some n`, decimal printing reads back (core has no
  lemma; `String.toNat?` loops over a slice with early return and underscores);
* `splitOn_comma_of_not_mem`: `s.splitOn "," = [s]` when `s` has no `,` (core has none for the
  legacy `String.splitOn`; Batteries leaves it a TODO). The induction `splitOnAux_comma`
  follows Batteries' `splitAux_of_valid`.

They make `Silmaril.Wasm.Binaryen.DriverSpec.parseArgs_render` unconditional.
-/

@[expose] public section

namespace Silmaril.Cli.Text

/-- The loop of `String.Slice.isNat` on digits, from a state that has not returned. -/
theorem isNat_loop_digits (l : List Char) (hl : ∀ c ∈ l, c.isDigit = true) (hne : l ≠ [])
    (b : Bool) :
    (forIn (m := Id) l ((none : Option Bool), b) fun c (s : Option Bool × Bool) =>
      if c = '_' then
        if (!s.snd) = true then pure (ForInStep.done (some false, s.snd))
        else pure (ForInStep.yield (none, false))
      else
        if c.isDigit = true then pure (ForInStep.yield (none, true))
        else pure (ForInStep.done (some false, s.snd))) = ((none : Option Bool), true) := by
  induction l generalizing b with
  | nil => exact absurd rfl hne
  | cons c l ih =>
    have hc : c.isDigit = true := hl c (by simp)
    have hc' : c ≠ '_' := by rintro rfl; cases hc
    simp only [List.forIn_cons, hc', hc, ite_false, ite_true]
    cases l with
    | nil => rfl
    | cons d l => exact ih (fun x hx => hl x (by simp_all)) (by simp) true

theorem digitChar_sub (d : Nat) (h : d < 10) : d.digitChar.toNat - 48 = d := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => simp [Nat.digitChar]

/-- A decimal digit is not `_`. -/
theorem digitChar_ne_underscore (d : Nat) (h : d < 10) : d.digitChar ≠ '_' := by
  intro he
  have hdig : d.digitChar.isDigit = decide (d < 10) := Nat.isDigit_digitChar
  rw [he] at hdig
  exact absurd hdig (by simp [h])

/-- The step of the digit fold of `String.Slice.toNat?`. -/
abbrev digitStep (n : Nat) (c : Char) : Nat := if c = '_' then n else n * 10 + (c.toNat - 48)

theorem digitStep_digitChar (n d : Nat) (h : d < 10) : digitStep n d.digitChar = n * 10 + d := by
  simp only [digitStep, digitChar_ne_underscore d h, ite_false, digitChar_sub d h]

theorem foldl_digits (n : Nat) : (Nat.toDigits 10 n).foldl digitStep 0 = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    by_cases h : n < 10
    · simp only [h, ↓reduceIte]
      show ([n.digitChar] : List Char).foldl digitStep 0 = n
      rw [List.foldl_cons, List.foldl_nil, digitStep_digitChar 0 n h]
      omega
    · simp only [h, ↓reduceIte]
      show (Nat.toDigits 10 (n / 10) ++ [(n % 10).digitChar]).foldl digitStep 0 = n
      have h10 : n % 10 < 10 := Nat.mod_lt _ (by decide)
      rw [List.foldl_append, ih (n / 10) (by omega), List.foldl_cons, List.foldl_nil,
        digitStep_digitChar _ _ h10]
      omega

/-- `String.toNat?` reads back decimal printing. -/
theorem toNat?_toString (n : Nat) : (toString n).toNat? = some n := by
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat]
  simp only [String.Slice.forIn_eq_forIn_toList, String.Slice.foldl_eq_foldl_toList,
    String.copy_toSlice]
  have hl : (toString n).toList = Nat.toDigits 10 n := Nat.toList_repr
  rw [hl, isNat_loop_digits _ (fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)
    Nat.toDigits_ne_nil false]
  simp only [Id.run]
  exact congrArg some (foldl_digits n)

open String in
/-- `splitOnAux` at `,` over a rest without `,`: one piece, from the start `b` to the end. -/
theorem splitOnAux_comma (l r : List Char) (acc : List String) (hr : ',' ∉ r)
    (m : List Char) :
    splitOnAux (ofList (l ++ m ++ r)) "," ⟨utf8Len l⟩ ⟨utf8Len l + utf8Len m⟩ 0 acc =
      (ofList (m ++ r) :: acc).reverse := by
  induction r generalizing m with
  | nil =>
    show splitOnAux (ofList (l ++ m ++ [])) "," ⟨utf8Len l⟩ ⟨utf8Len l + utf8Len m⟩ 0 acc =
      (ofList (m ++ []) :: acc).reverse
    unfold splitOnAux
    simp only [List.append_nil, atEnd_iff, rawEndPos_ofList, utf8Len_append, Pos.Raw.mk_le_mk,
      Nat.le_refl, ite_true]
    simpa using extract_of_valid l m []
  | cons c r ih =>
    show splitOnAux (ofList (l ++ m ++ c :: r)) "," ⟨utf8Len l⟩ ⟨utf8Len l + utf8Len m⟩ 0 acc =
      (ofList (m ++ c :: r) :: acc).reverse
    have hc : c ≠ ',' := fun h => hr (h ▸ List.mem_cons_self)
    have hr' : ',' ∉ r := fun h => hr (List.mem_cons_of_mem _ h)
    have hg : Pos.Raw.get (ofList (l ++ m ++ c :: r)) ⟨utf8Len l + utf8Len m⟩ = c := by
      simpa using get_of_valid (l ++ m) (c :: r)
    have hn : Pos.Raw.next (ofList (l ++ m ++ c :: r)) ⟨utf8Len l + utf8Len m⟩ =
        ⟨utf8Len l + utf8Len m + c.utf8Size⟩ := by
      simpa using next_of_valid (l ++ m) c r
    have hz : (⟨utf8Len l + utf8Len m⟩ : Pos.Raw).unoffsetBy 0 = ⟨utf8Len l + utf8Len m⟩ := rfl
    have hcomma : Pos.Raw.get "," 0 = ',' := by decide
    have hend : ¬ (rawEndPos (ofList (l ++ m ++ c :: r)) ≤ ⟨utf8Len l + utf8Len m⟩) := by
      rw [rawEndPos_ofList, Pos.Raw.mk_le_mk]
      simp only [utf8Len_append, utf8Len_cons]
      have := Char.utf8Size_pos c
      omega
    have hae : Pos.Raw.atEnd (ofList (l ++ m ++ c :: r)) ⟨utf8Len l + utf8Len m⟩ = false := by
      cases h : Pos.Raw.atEnd (ofList (l ++ m ++ c :: r)) ⟨utf8Len l + utf8Len m⟩ with
      | false => rfl
      | true => exact absurd ((atEnd_iff _ _).1 h) hend
    have hrec : splitOnAux (ofList (l ++ (m ++ [c]) ++ r)) "," ⟨utf8Len l⟩
        ⟨utf8Len l + utf8Len (m ++ [c])⟩ 0 acc = (ofList ((m ++ [c]) ++ r) :: acc).reverse :=
      ih hr' (m ++ [c])
    unfold splitOnAux
    rw [hae, hg, hcomma, hz, hn]
    simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq, hc]
    simpa [utf8Len_append, Nat.add_assoc] using hrec

/-- **`splitOn` at `,`** of a string without `,` is the string itself. -/
theorem splitOn_comma_of_not_mem (s : String) (h : ',' ∉ s.toList) : s.splitOn "," = [s] := by
  have := splitOnAux_comma [] s.toList [] h []
  simp at this
  simpa [String.splitOn] using this

end Silmaril.Cli.Text