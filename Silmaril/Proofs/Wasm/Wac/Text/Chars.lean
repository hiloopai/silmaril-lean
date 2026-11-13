module

public import Silmaril.Proofs.Wasm.Wac.Text.Lex

/-!
# WAC text: printed text has no rejected character

The scanners only accept ASCII letters, digits and punctuation (`*_good`), so
well-formed tokens are spelled without the characters `inputOk` rejects.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Text

/-- A character `lex` accepts in its input. -/
abbrev Good (c : Char) : Prop := badChar c = false

theorem good_of_ascii {c : Char} (h1 : 0x20 ≤ c.toNat) (h2 : c.toNat < 0x7f) : Good c := by
  unfold Good badChar
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_imp, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  all_goals first | (intro h; simp_all; omega) | (simp; omega) | omega

theorem good_letter {c : Char} (h : isLetter c = true) : Good c := by
  simp only [isLetter, isLower, isUpper, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have a : 97 ≤ c.toNat := h1; have b : c.toNat ≤ 122 := h2; exact good_of_ascii (by omega) (by omega)
  · have a : 65 ≤ c.toNat := h1; have b : c.toNat ≤ 90 := h2; exact good_of_ascii (by omega) (by omega)

theorem good_digit {c : Char} (h : isDigitC c = true) : Good c := by
  simp only [isDigitC, Bool.and_eq_true, decide_eq_true_eq] at h
  have a : 48 ≤ c.toNat := h.1; have b : c.toNat ≤ 57 := h.2
  exact good_of_ascii (by omega) (by omega)

theorem good_wordCont {up : Bool} {c : Char} (h : wordCont up c = true) : Good c := by
  cases up <;> simp only [wordCont, Bool.or_eq_true, ↓reduceIte, Bool.false_eq_true] at h <;>
    rcases h with h | h
  all_goals first
    | exact good_digit h
    | exact good_letter (by simp [isLetter, h])

theorem good_verCont {c : Char} (h : verCont c = true) : Good c := by
  simp only [verCont, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h
  · exact good_letter h
  · exact good_digit h
  · subst h; decide
  · subst h; decide

theorem spanL_fst (p : Char → Bool) (l : List Char) : ∀ x ∈ (spanL p l).1, p x = true := by
  fun_induction spanL p l <;> simp_all

theorem idTail_good (l : List Char) : ∀ x ∈ (idTail l).1, Good x := by
  fun_induction idTail l with
  | case1 c r hc ih =>
    intro x hx
    simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | rfl | hx | hx
    · decide
    · exact good_letter hc
    · exact good_wordCont (spanL_fst _ r x hx)
    · exact ih x hx
  | case2 => simp
  | case3 => simp

theorem idBody_good {l w r : List Char} (h : idBody l = some (w, r)) : ∀ x ∈ w, Good x := by
  match l with
  | [] => simp [idBody] at h
  | c :: l =>
    simp only [idBody] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      intro x hx
      simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx
      · exact good_letter ‹_›
      · exact good_wordCont (spanL_fst _ l x hx)
      · exact idTail_good _ x hx
    · simp at h

theorem idRaw_good {l w r : List Char} (h : idRaw l = some (w, r)) : ∀ x ∈ w, Good x := by
  unfold idRaw at h
  split at h
  · rename_i t
    cases hb : idBody t with
    | none => simp [hb] at h
    | some p =>
      simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · decide
      · exact idBody_good (l := t) (w := p.1) (r := p.2) (by simp [hb]) x hx
  · exact idBody_good h

theorem sepIds_good (sep : Char) (hs : Good sep) : ∀ (k : Nat) (l : List Char), l.length < k →
    ∀ x ∈ (sepIds sep l).1, Good x
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, [], _ => by simp [sepIds]
  | k + 1, y :: l, hl => by
    by_cases hy : y = sep
    · subst hy
      cases hi : idRaw l with
      | none => rw [sepIds_cons_none y hi]; simp
      | some p =>
        have := idRaw_lt hi
        rw [sepIds_cons_some y hi]
        intro x hx
        simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
        rcases hx with rfl | hx | hx
        · exact hs
        · exact idRaw_good hi x hx
        · exact sepIds_good y hs k p.2 (by simp at hl; omega) x hx
    · rw [sepIds_cons_ne hy]; simp

theorem verTail_good (l : List Char) : ∀ x ∈ (verTail l).1, Good x := by
  fun_induction verTail l with
  | case1 c r hc ih =>
    intro x hx
    simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | rfl | hx | hx
    · decide
    · exact good_verCont hc
    · exact good_verCont (spanL_fst _ r x hx)
    · exact ih x hx
  | case2 => simp
  | case3 => simp

theorem atVer_good {l v : List Char} (h : (atVer l).1 = some v) : ∀ x ∈ v, Good x := by
  unfold atVer at h
  split at h
  · rename_i c r
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      intro x hx
      simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx
      · exact good_digit ‹_›
      · exact good_digit (spanL_fst _ r x hx)
      · exact verTail_good _ x hx
    · simp at h
  · simp at h

theorem idOk_good {s : String} (h : idOk s = true) : ∀ x ∈ s.toList, Good x := by
  obtain ⟨-, -, -, -, -, hb⟩ := idOk_spec h
  exact idBody_good hb

theorem nameOk_good {n : String} (h : nameOk n = true) : ∀ x ∈ n.toList, Good x := by
  unfold nameOk at h
  split at h
  · rename_i w r1 hid
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    have hs := sepIds_split ':' (r1.length + 1) r1 (by omega)
    rw [h.2, List.append_nil] at hs
    rw [← idRaw_split hid]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact idRaw_good hid x hx
    · rw [← hs] at hx; exact sepIds_good ':' (by decide) (r1.length + 1) r1 (by omega) x hx
  · simp at h

theorem segsOk_good {sg : String} (h : segsOk sg = true) : ∀ x ∈ sg.toList, Good x := by
  simp only [segsOk, Bool.and_eq_true, List.isEmpty_iff] at h
  have hs := sepIds_split '/' (sg.toList.length + 2) ('/' :: sg.toList) (by simp)
  rw [h.1, List.append_nil] at hs
  intro x hx
  have : x ∈ (sepIds '/' ('/' :: sg.toList)).1 := by rw [hs]; simp [hx]
  exact sepIds_good '/' (by decide) (sg.toList.length + 2) _ (by simp) x this

theorem verLexOk_good {v : String} (h : verLexOk v = true) : ∀ x ∈ v.toList, Good x := by
  have h' : atVer ('@' :: v.toList) = (some v.toList, []) := by simpa [verLexOk] using h
  exact atVer_good (l := '@' :: v.toList) (by rw [h'])

theorem kw_good (k : Kw) : ∀ x ∈ k.name.toList, Good x := by
  cases k <;> decide +kernel

theorem tok_good_id {s : String} (h : (Tok.id s).ok = true) : ∀ x ∈ (Tok.id s).chars, Good x := by
  have hg := idOk_good h
  intro x hx
  simp only [Tok.chars] at hx
  split at hx
  · rcases List.mem_cons.mp hx with rfl | hx
    · decide
    · exact hg x hx
  · exact hg x hx

theorem tok_good_str {s : String} (h : (Tok.str s).ok = true) :
    ∀ x ∈ (Tok.str s).chars, Good x := by
  simp only [Tok.ok, strOk, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at h
  intro x hx
  simp only [Tok.chars, List.cons_append, List.mem_cons, List.mem_append] at hx
  rcases hx with rfl | hx | hx
  · decide
  · simpa using h.2 x hx
  · simp at hx; subst hx; decide

theorem ver_good {v : Option String} (h : (match v with | some v => verLexOk v | none => true) = true) :
    ∀ x ∈ (match v with | some v => '@' :: v.toList | none => []), Good x := by
  cases v with
  | none => simp
  | some v =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · decide
    · exact verLexOk_good h x hx

theorem tok_good_pname {n : String} {v : Option String} (h : (Tok.pname n v).ok = true) :
    ∀ x ∈ (Tok.pname n v).chars, Good x := by
  simp only [Tok.ok, Bool.and_eq_true] at h
  intro x hx
  simp only [Tok.chars, List.mem_append] at hx
  rcases hx with hx | hx
  · exact nameOk_good h.1 x hx
  · exact ver_good h.2 x hx

theorem tok_good_ppath {n sg : String} {v : Option String} (h : (Tok.ppath n sg v).ok = true) :
    ∀ x ∈ (Tok.ppath n sg v).chars, Good x := by
  simp only [Tok.ok, Bool.and_eq_true] at h
  intro x hx
  simp only [Tok.chars, List.mem_append, List.mem_cons] at hx
  rcases hx with (hx | rfl | hx) | hx
  · exact nameOk_good h.1.1 x hx
  · decide
  · exact segsOk_good h.1.2 x hx
  · exact ver_good h.2 x hx

theorem tok_good_sym {c : Char} (h : (Tok.sym c).ok = true) : ∀ x ∈ (Tok.sym c).chars, Good x := by
  simp only [Tok.ok, symChars] at h
  intro x hx
  simp only [Tok.chars, List.mem_singleton] at hx
  subst hx
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

theorem tok_good {t : Tok} (h : t.ok = true) : ∀ x ∈ t.chars, Good x := by
  cases t with
  | id s => exact tok_good_id h
  | kw k => exact kw_good k
  | str s => exact tok_good_str h
  | pname n v => exact tok_good_pname h
  | ppath n sg v => exact tok_good_ppath h
  | sym c => exact tok_good_sym h
  | arrow => decide
  | ellipsis => decide

theorem docStr_good {d : String} (h : docOk d = true) : ∀ x ∈ docStr d, Good x := by
  simp only [docOk, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at h
  intro x hx
  simp only [docStr, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | hx | rfl
  · decide
  · decide
  · decide
  · decide
  · simpa using h.2 x hx
  · decide

/-- A layout of well-formed tokens has no rejected character when its separators have
none. -/
theorem renderWith_good (sep ind : Nat → List Char) (hsep : ∀ i, ∀ x ∈ sep i, Good x)
    (hind : ∀ i, ∀ x ∈ ind i, Good x) :
    ∀ (ts : List ATok) (i : Nat), (∀ a ∈ ts, a.tok.ok = true ∧ docsOk a.docs = true) →
      ∀ x ∈ renderWith sep ind i ts, Good x
  | [], _, _ => by simp [renderWith]
  | a :: ts, i, h => by
    have ha := h a (by simp)
    have ih := renderWith_good sep ind hsep hind ts (i + 1) (fun y hy => h y (by simp [hy]))
    intro x hx
    simp only [renderWith, List.mem_append, List.mem_flatMap] at hx
    rcases hx with ((⟨d, hd, hx⟩ | hx) | hx) | hx
    · have hdok : docOk d = true := by
        have := ha.2; simp only [docsOk, List.all_eq_true] at this; exact this d hd
      rcases hx with hx | hx
      · exact docStr_good hdok x hx
      · exact hind i x hx
    · exact tok_good ha.1 x hx
    · exact hsep i x hx
    · exact ih x hx

theorem inputOk_of_good {cs : List Char} (h : ∀ x ∈ cs, Good x) : inputOk cs = true := by
  simp only [inputOk, Bool.not_eq_true', List.any_eq_false]
  intro x hx; simpa using h x hx

end Silmaril.Wasm.Wac.Text
