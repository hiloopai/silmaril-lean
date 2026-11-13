module

public import Silmaril.Wasm.Wac.Text.Print.Defs

/-!
# WAC text: the scanners stop at whitespace

Each scanner of the lexer (`spanL`, `idTail`, `idBody`, `idRaw`, `sepIds`, `verTail`,
`atVer`) is local: appending a whitespace character and anything after it to its input
appends the same to what it leaves (`*_append_ws`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Text

/-- What a whitespace character is not. -/
theorem ws_not {c : Char} (h : isWs c = true) :
    isLetter c = false ∧ isDigitC c = false ∧ isUpper c = false ∧ isLower c = false ∧
    verCont c = false ∧ c ≠ '-' ∧ c ≠ ':' ∧ c ≠ '/' ∧ c ≠ '@' ∧ c ≠ '.' ∧ c ≠ '%' ∧
    c ≠ '"' ∧ c ≠ '*' := by
  simp only [isWs, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (((h | h) | h) | h) | h <;> subst h <;> decide

/-- A character that ends an identifier. -/
def IdStop (c : Char) : Prop := isLetter c = false ∧ isDigitC c = false ∧ c ≠ '-' ∧ c ≠ '%'

theorem IdStop.of_ws {c : Char} (h : isWs c = true) : IdStop c :=
  let h' := ws_not h
  ⟨h'.1, h'.2.1, h'.2.2.2.2.2.1, h'.2.2.2.2.2.2.2.2.2.2.1⟩

theorem idStop_at : IdStop '@' := by unfold IdStop; decide
theorem idStop_slash : IdStop '/' := by unfold IdStop; decide
theorem idStop_colon : IdStop ':' := by unfold IdStop; decide

theorem wordCont_stop {c : Char} (h : IdStop c) (up : Bool) : wordCont up c = false := by
  obtain ⟨h1, h2, -⟩ := h
  have : isUpper c = false ∧ isLower c = false := by
    simp only [isLetter, Bool.or_eq_false_iff] at h1; exact ⟨h1.2, h1.1⟩
  cases up <;> simp [wordCont, h2, this.1, this.2]

theorem spanL_append_stop (p : Char → Bool) {c : Char} (hc : p c = false) (r : List Char) :
    ∀ l : List Char, spanL p (l ++ c :: r) = ((spanL p l).1, (spanL p l).2 ++ c :: r)
  | [] => by simp [spanL, hc]
  | x :: l => by
    by_cases hx : p x = true
    · simp [spanL, hx, spanL_append_stop p hc r l]
    · simp [spanL, hx]

theorem idTail_of_ne {x : Char} (hx : x ≠ '-') (l : List Char) : idTail (x :: l) = ([], x :: l) := by
  rw [idTail.eq_def]; split <;> simp_all

theorem idTail_append_ws {c : Char} (hc : IdStop c) (r : List Char) (l : List Char) :
    idTail (l ++ c :: r) = ((idTail l).1, (idTail l).2 ++ c :: r) := by
  have hc' := hc
  obtain ⟨hl, -, hm, -⟩ := hc'
  fun_induction idTail l with
  | case1 x r' hx ih =>
    have hs := spanL_append_stop (wordCont (isUpper x)) (wordCont_stop hc _) r r'
    rw [List.cons_append, List.cons_append, idTail]; simp only [hx, ↓reduceIte]; rw [hs, ih]
  | case2 x r' hx =>
    rw [List.cons_append, List.cons_append, idTail]; simp only [hx]; rfl
  | case3 cs h =>
    match cs, h with
    | [], _ => simp [idTail, hm]
    | x :: l, h =>
      by_cases hx : x = '-'
      · subst hx
        cases l with
        | nil => simp [idTail, hl]
        | cons y l' => exact absurd rfl (h y l')
      · simp [idTail_of_ne hx]

theorem idBody_append_ws {c : Char} (hc : IdStop c) (r : List Char) :
    ∀ l : List Char, idBody (l ++ c :: r) = (idBody l).map fun p => (p.1, p.2 ++ c :: r)
  | [] => by simp [idBody, hc.1]
  | x :: l => by
    by_cases hx : isLetter x = true
    · have hs := spanL_append_stop (wordCont (isUpper x)) (wordCont_stop hc _) r l
      simp [idBody, hx, hs, idTail_append_ws hc]
    · simp [idBody, hx]

theorem idRaw_append_ws {c : Char} (hc : IdStop c) (r : List Char) (l : List Char) :
    idRaw (l ++ c :: r) = (idRaw l).map fun p => (p.1, p.2 ++ c :: r) := by
  match l with
  | '%' :: l => simp [idRaw, idBody_append_ws hc, Option.map_map, Function.comp_def]
  | [] => simp [idRaw, idBody, hc.1, hc.2.2.2]
  | x :: l =>
    by_cases hx : x = '%'
    · subst hx; simp [idRaw, idBody_append_ws hc, Option.map_map, Function.comp_def]
    · have e1 : idRaw (x :: l) = idBody (x :: l) := by rw [idRaw.eq_def]; split <;> simp_all
      have e2 : idRaw (x :: (l ++ c :: r)) = idBody (x :: (l ++ c :: r)) := by
        rw [idRaw.eq_def]; split <;> simp_all
      rw [List.cons_append, e2, e1, ← List.cons_append, idBody_append_ws hc]

theorem sepIds_cons_some (sep : Char) {l w r' : List Char} (h : idRaw l = some (w, r')) :
    sepIds sep (sep :: l) = (sep :: w ++ (sepIds sep r').1, (sepIds sep r').2) := by
  rw [sepIds.eq_def]; split <;> (try split) <;> (try split) <;> simp_all

theorem sepIds_cons_none (sep : Char) {l : List Char} (h : idRaw l = none) :
    sepIds sep (sep :: l) = ([], sep :: l) := by
  rw [sepIds.eq_def]; split <;> (try split) <;> (try split) <;> simp_all

theorem sepIds_cons_ne {sep x : Char} (h : x ≠ sep) (l : List Char) :
    sepIds sep (x :: l) = ([], x :: l) := by
  rw [sepIds.eq_def]; simp [h]

theorem sepIds_append_ws {c : Char} (hc : IdStop c) (r : List Char) (sep : Char)
    (hcs : c ≠ sep) : ∀ (k : Nat) (l : List Char), l.length < k →
    sepIds sep (l ++ c :: r) = ((sepIds sep l).1, (sepIds sep l).2 ++ c :: r)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, [], _ => by simp [sepIds_cons_ne hcs, sepIds]
  | k + 1, x :: l, hl => by
    by_cases hx : x = sep
    · subst hx
      cases hi : idRaw l with
      | none =>
        have e : idRaw (l ++ c :: r) = none := by rw [idRaw_append_ws hc, hi]; rfl
        rw [List.cons_append, sepIds_cons_none x e, sepIds_cons_none x hi]; rfl
      | some p =>
        have e : idRaw (l ++ c :: r) = some (p.1, p.2 ++ c :: r) := by
          rw [idRaw_append_ws hc, hi]; rfl
        have hlt := idRaw_lt hi
        have ih := sepIds_append_ws hc r x hcs k p.2 (by simp at hl; omega)
        rw [List.cons_append, sepIds_cons_some x e, sepIds_cons_some x hi, ih]
    · rw [List.cons_append, sepIds_cons_ne hx, sepIds_cons_ne hx]; rfl

theorem verTail_of_ne {x : Char} (hx : x ≠ '.') (l : List Char) :
    verTail (x :: l) = ([], x :: l) := by
  rw [verTail.eq_def]; split <;> simp_all

theorem verTail_append_ws {c : Char} (hc : isWs c = true) (r : List Char) (l : List Char) :
    verTail (l ++ c :: r) = ((verTail l).1, (verTail l).2 ++ c :: r) := by
  obtain ⟨-, -, -, -, hv, -, -, -, -, hd, -⟩ := ws_not hc
  fun_induction verTail l with
  | case1 x r' hx ih =>
    have hs := spanL_append_stop verCont hv r r'
    rw [List.cons_append, List.cons_append, verTail]; simp only [hx, ↓reduceIte]; rw [hs, ih]
  | case2 x r' hx =>
    rw [List.cons_append, List.cons_append, verTail]; simp only [hx]; rfl
  | case3 cs h =>
    match cs, h with
    | [], _ => simp [verTail_of_ne hd]
    | x :: l, h =>
      by_cases hx : x = '.'
      · subst hx
        cases l with
        | nil => simp [verTail, hv]
        | cons y l' => exact absurd rfl (h y l')
      · simp [verTail_of_ne hx]

theorem atVer_at_append {c : Char} (hc : isWs c = true) (r : List Char) (x : Char) (l : List Char) :
    atVer ('@' :: x :: l ++ c :: r) = ((atVer ('@' :: x :: l)).1, (atVer ('@' :: x :: l)).2 ++ c :: r) := by
  obtain ⟨-, hdg, -⟩ := ws_not hc
  by_cases hx : isDigitC x = true
  · have hs := spanL_append_stop isDigitC hdg r l
    simp [atVer, hx, hs, verTail_append_ws hc]
  · simp [atVer, hx]

theorem atVer_append_ws {c : Char} (hc : isWs c = true) (r : List Char) (l : List Char) :
    atVer (l ++ c :: r) = ((atVer l).1, (atVer l).2 ++ c :: r) := by
  obtain ⟨-, hdg, -, -, -, -, -, -, ha, -⟩ := ws_not hc
  match l with
  | [] => simp [atVer, ha]
  | ['@'] => simp [atVer, hdg]
  | '@' :: x :: l => exact atVer_at_append hc r x l
  | x :: l =>
    by_cases hx : x = '@'
    · subst hx
      cases l with
      | nil => simp [atVer, hdg]
      | cons y l' => exact atVer_at_append hc r y l'
    · have e : ∀ m, atVer (x :: m) = (none, x :: m) := fun m => by
        rw [atVer.eq_def]; split <;> simp_all
      simp [e]

/-! ## The scanners split their input -/

theorem spanL_split (p : Char → Bool) (l : List Char) : (spanL p l).1 ++ (spanL p l).2 = l := by
  fun_induction spanL p l <;> simp_all

theorem idTail_split (l : List Char) : (idTail l).1 ++ (idTail l).2 = l := by
  fun_induction idTail l with
  | case1 x r hx ih =>
    have := spanL_split (wordCont (isUpper x)) r
    simp only [List.cons_append, List.append_assoc, ih, this]
  | case2 => rfl
  | case3 => rfl

theorem idBody_split {l w r : List Char} (h : idBody l = some (w, r)) : w ++ r = l := by
  match l with
  | [] => simp [idBody] at h
  | x :: l =>
    simp only [idBody] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := spanL_split (wordCont (isUpper x)) l
      simp only [List.cons_append, List.append_assoc, idTail_split, this]
    · simp at h

theorem idRaw_split {l w r : List Char} (h : idRaw l = some (w, r)) : w ++ r = l := by
  unfold idRaw at h
  split at h
  · rename_i t
    cases hb : idBody t with
    | none => simp [hb] at h
    | some p =>
      simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [idBody_split (l := t) (w := p.1) (r := p.2) (by simp [hb])]
  · exact idBody_split h

theorem sepIds_split (sep : Char) : ∀ (k : Nat) (l : List Char), l.length < k →
    (sepIds sep l).1 ++ (sepIds sep l).2 = l
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, [], _ => by simp [sepIds]
  | k + 1, x :: l, hl => by
    by_cases hx : x = sep
    · subst hx
      cases hi : idRaw l with
      | none => rw [sepIds_cons_none x hi]; rfl
      | some p =>
        have := idRaw_lt hi
        rw [sepIds_cons_some x hi]
        simp only [List.cons_append, List.append_assoc,
          sepIds_split x k p.2 (by simp at hl; omega), idRaw_split hi]
    · rw [sepIds_cons_ne hx]; rfl

end Silmaril.Wasm.Wac.Text
