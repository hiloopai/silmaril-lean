module

public import Silmaril.Wasm.SpecTec.Surface.Lexer.Defs

/-!
# Soundness of the SpecTec surface lexer

Each candidate function of `step?` is sound for the `Step` rules it
implements, and `lexList?` chains sound steps. The headline
`lex?_sound` is in `Silmaril.Wasm.SpecTec.Surface.Lexer.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Surface.Lexer

theorem afterNlNl?_sound :
    ∀ (n : Nat) (cs : List Char) (t : Option Token) (r : List Char),
      afterNlNl? n cs = some (t, r) → AfterNlNl cs t r := by
  intro n
  induction n with
  | zero => intro cs t r h; simp [afterNlNl?] at h
  | succ n ih =>
    intro cs t r h
    unfold afterNlNl? at h
    split at h
    next hd => cases h; exact .eof hd
    next hd => cases h; exact .nl hd
    next hd =>
      split at h
      next hc => cases h; exact .bar hd hc
      next => split at h <;> cases h; exact .other ‹_›
    next hd =>
      split at h
      next hb => cases h; exact .eofComment hd hb
      next hb => exact .comment hd hb (ih _ _ _ h)
      next => cases h
    next => split at h <;> cases h; exact .other ‹_›

theorem afterNl?_sound {cs : List Char} {t : Option Token} {r : List Char}
    (h : afterNl? cs = some (t, r)) : AfterNl cs t r := by
  unfold afterNl? at h
  split at h
  next hd => exact .nl hd (afterNlNl?_sound _ _ _ _ h)
  next hd =>
    split at h
    next hc => cases h; exact .bar hd hc
    next => split at h <;> cases h; exact .other ‹_›
  next => split at h <;> cases h; exact .other ‹_›

theorem orElse_some {α : Type} {a b : Option α} {x : α} (h : (a <|> b) = some x) :
    a = some x ∨ b = some x := by
  cases a <;> simp_all

theorem layoutStep?_sound {cs : List Char} {t : Option Token} {r : List Char}
    (h : layoutStep? cs = some (t, r)) : Step cs t r := by
  unfold layoutStep? at h
  split at h
  next => cases h; exact .cont
  next => exact .newline (afterNl?_sound h)
  next =>
    split at h
    next hb => cases h; exact .commentEof hb
    next hb => exact .commentNl hb (afterNl?_sound h)
    next => cases h
  next r0 =>
    cases hc : commaNlTail r0 <;> simp only [hc, Option.map_none, Option.map_some, reduceCtorEq,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .commaNl hc
  next => split at h <;> cases h; exact .space ‹_›
  next => cases h

theorem identAt?_sound {c : Char} {cs : List Char} {t : Option Token} {r : List Char}
    (hs : isIdStart c) (hp : (afterWord (c :: cs)).head? ≠ some '(')
    (h : identAt? (wordOf (c :: cs)) (afterWord (c :: cs)) = some (t, r)) : Step (c :: cs) t r := by
  unfold identAt? at h
  split at h
  next hk => cases h; exact .keyword hs (by simpa using hk) hp
  next hk =>
    split at h
    next => cases h
    next hu =>
      split at h
      next => cases h
      next hb =>
        cases h
        exact .ident hs (by simpa using hk) hp (by simpa using hu)
          (by simpa [List.isPrefixOf_iff_prefix] using hb)

theorem wordAt?_sound {c : Char} {cs : List Char} {t : Option Token} {r : List Char}
    (hs : isIdStart c) (h : wordAt? (wordOf (c :: cs)) (afterWord (c :: cs)) = some (t, r)) :
    Step (c :: cs) t r := by
  unfold wordAt? at h
  split at h
  next hp =>
    have hr : afterWord (c :: cs) = '(' :: (afterWord (c :: cs)).tail := by
      obtain ⟨r', hr'⟩ := List.head?_eq_some_iff.mp (by simpa using hp)
      simp [hr']
    split at h
    next => cases h
    next hw => cases h; exact .idParen hs hr hw
  next hp => exact identAt?_sound hs (by simpa using hp) h

theorem wordStep?_sound {cs : List Char} {t : Option Token} {r : List Char}
    (h : wordStep? cs = some (t, r)) : Step cs t r := by
  unfold wordStep? at h
  split at h
  next => cases h; exact .hint
  next c cs _ =>
    split at h
    next hs => exact wordAt?_sound hs h
    next => cases h
  next => cases h

theorem sepTok?_spec {p : Char → Bool} {mk : List Char → Token} {cs : List Char}
    {t : Option Token} {r : List Char} (h : sepTok? p mk cs = some (t, r)) :
    ∃ s, scanSep p cs = (s, r) ∧ s ≠ [] ∧ t = some (mk s) := by
  unfold sepTok? at h
  split at h
  next => cases h
  next s r0 hne hs => cases h; exact ⟨s, hs, by rintro rfl; simp_all, rfl⟩

theorem hexAfter_x_of_scan {cs r : List Char} (hs : scanSep isHex cs = ([], r)) :
    hexAfter ('x' :: cs) = false := by
  cases cs with
  | nil => rfl
  | cons d ds =>
    have hd : isHex d = false := by
      by_contra hd'
      simp [scanSep, Bool.not_eq_false _ |>.mp hd'] at hs
    simp [hexAfter, hd]

theorem zeroX?_sound {cs : List Char} {t : Option Token} {r : List Char}
    (h : zeroX? cs = some (t, r)) : Step ('0' :: 'x' :: cs) t r := by
  unfold zeroX? at h
  split at h
  next hs =>
    cases h
    exact .nat (by simp [scanSep, scanSepTail, isDigit]) (by simp)
      (by simp [hexAfter_x_of_scan hs])
  next s r0 hne hs => cases h; exact .hex hs (by rintro rfl; simp_all)

theorem natStep?_sound {cs : List Char} {t : Option Token} {r : List Char}
    (h : natStep? cs = some (t, r)) : Step cs t r := by
  unfold natStep? at h
  split at h
  next => cases h
  next s r0 hne hs =>
    split at h
    next => cases h
    next hx => cases h; exact .nat hs (by rintro rfl; simp_all) (by simpa using hx)

theorem tickAt?_sound {c : Char} {cs : List Char} {t : Option Token} {r : List Char}
    (hs : isIdStart c) (h : tickAt? (wordOf (c :: cs)) (afterWord (c :: cs)) = some (t, r)) :
    Step ('`' :: c :: cs) t r := by
  unfold tickAt? at h
  split at h
  next hp =>
    have hr : afterWord (c :: cs) = '(' :: (afterWord (c :: cs)).tail := by
      obtain ⟨r', hr'⟩ := List.head?_eq_some_iff.mp (by simpa using hp)
      simp [hr']
    cases h; exact .tickIdParen hs hr
  next hp => cases h; exact .tickId hs (by simpa using hp)

theorem text_sound {cs : List Char} {t : Option Token} {r : List Char}
    (h : ((scanText (cs.length + 1) cs).map fun (b, r) => (some (Token.text b), r)) = some (t, r)) :
    Step ('"' :: cs) t r := by
  obtain ⟨⟨b, r'⟩, hb, he⟩ := Option.map_eq_some_iff.mp h
  cases he
  exact .text hb

theorem blockComment_sound {cs : List Char} {t : Option Token} {r : List Char}
    (h : ((skipComment (cs.length + 1) 0 cs).map fun r => ((none : Option Token), r)) = some (t, r)) :
    Step ('(' :: ';' :: cs) t r := by
  obtain ⟨r', hb, he⟩ := Option.map_eq_some_iff.mp h
  cases he
  exact .blockComment hb

theorem dotId_sound {c : Char} {cs : List Char} {t : Option Token} {r : List Char}
    (h : (if isIdStart c then some (some (Token.dotId (wordOf (c :: cs))), afterWord (c :: cs))
      else none) = some (t, r)) : Step ('.' :: c :: cs) t r := by
  split at h
  next hc => cases h; exact .dotId hc
  next => cases h

theorem tick_sound {c : Char} {cs : List Char} {t : Option Token} {r : List Char}
    (h : (if isIdStart c then tickAt? (wordOf (c :: cs)) (afterWord (c :: cs)) else none) =
      some (t, r)) : Step ('`' :: c :: cs) t r := by
  split at h
  next hc => exact tickAt?_sound hc h
  next => cases h

theorem sepTok?_char {cs : List Char} {t : Option Token} {r : List Char}
    (h : sepTok? isHex .char cs = some (t, r)) : Step ('U' :: '+' :: cs) t r := by
  obtain ⟨s, hs, hne, rfl⟩ := sepTok?_spec h
  exact .char hs hne

theorem sepTok?_holeN {cs : List Char} {t : Option Token} {r : List Char}
    (h : sepTok? isDigit .holeN cs = some (t, r)) : Step ('%' :: cs) t r := by
  obtain ⟨s, hs, hne, rfl⟩ := sepTok?_spec h
  exact .holeN hs hne

theorem litStep?_sound {cs : List Char} {t : Option Token} {r : List Char}
    (h : litStep? cs = some (t, r)) : Step cs t r := by
  unfold litStep? at h
  split at h
  next => exact zeroX?_sound h
  next => exact sepTok?_char h
  next => exact text_sound h
  next => exact sepTok?_holeN h
  next => exact dotId_sound h
  next => exact tick_sound h
  next => exact blockComment_sound h
  next => exact natStep?_sound h

theorem sym_of_checks {s : String} {cs : List Char} (hm : s ∈ symbols) (hp : s.toList <+: cs)
    (hsp : special cs = false)
    (hall : ∀ s' ∈ symbols, s'.toList.isPrefixOf cs = false ∨ s'.toList.length ≤ s.toList.length) :
    Step cs (some (.sym s)) (cs.drop s.toList.length) := by
  have hcs : s.toList ++ cs.drop s.toList.length = cs := List.prefix_iff_eq_append.mp hp
  have hlong : ∀ s' ∈ symbols, s'.toList <+: s.toList ++ cs.drop s.toList.length →
      s'.toList.length ≤ s.toList.length := by
    intro s' hs' hp'
    rcases hall s' hs' with h1 | h1
    · exact absurd (by simpa [hcs] using hp') (by simpa [← List.isPrefixOf_iff_prefix] using h1)
    · exact h1
  have key := Step.sym hm hlong (by rw [hcs]; exact hsp)
  rwa [hcs] at key

theorem symStep?_sound {cs : List Char} {t : Option Token} {r : List Char}
    (h : symStep? cs = some (t, r)) : Step cs t r := by
  unfold symStep? at h
  dsimp only at h
  split at h
  next => cases h
  next s _ =>
    split at h
    next hc =>
      cases h
      simp only [Bool.and_eq_true, List.contains_iff_mem, List.isPrefixOf_iff_prefix,
        beq_iff_eq, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
      exact sym_of_checks hc.1.1.1 hc.1.1.2 hc.1.2 hc.2
    next => cases h

theorem step?_sound {cs : List Char} {t : Option Token} {r : List Char}
    (h : step? cs = some (t, r)) : Step cs t r := by
  unfold step? at h
  rcases orElse_some h with h | h
  · exact layoutStep?_sound h
  rcases orElse_some h with h | h
  · exact wordStep?_sound h
  rcases orElse_some h with h | h
  · exact litStep?_sound h
  · exact symStep?_sound h

theorem lexList?_sound :
    ∀ (n : Nat) (cs : List Char) (ts : List Token), lexList? n cs = some ts → Lexes cs ts := by
  intro n
  induction n with
  | zero => intro cs ts h; cases cs <;> simp_all [lexList?, Lexes.nil]
  | succ n ih =>
    intro cs ts h
    cases cs with
    | nil => cases h; exact .nil
    | cons c cs =>
      unfold lexList? at h
      split at h
      next r hs => exact .skip (step?_sound hs) (ih _ _ h)
      next t r hs =>
        cases hl : lexList? n r <;> simp only [hl, Option.map_none, Option.map_some, reduceCtorEq,
          Option.some.injEq] at h
        cases h
        exact .tok (step?_sound hs) (ih _ _ hl)
      next => cases h

end Silmaril.Wasm.SpecTec.Surface.Lexer
