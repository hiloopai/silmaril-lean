module

public import Silmaril.Wasm.Wit.Binary.Docs.Defs

/-!
# The `package-docs` JSON fragment reads back

`JVal.parse_print : JVal.parse v.print = some v`: the reader inverts the
serde_json-style printer. Strings: `unquote_quote`; objects: by the size of
the printed text, which bounds the reader's fuel.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

/-! ## Strings -/

theorem hexVal_hexDigit {d : Nat} (h : d < 16) : hexVal (hexDigit d) = some d := by
  match d, h with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl
  | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl | 10, _ => rfl | 11, _ => rfl
  | 12, _ => rfl | 13, _ => rfl | 14, _ => rfl | 15, _ => rfl
  | _ + 16, h => omega

theorem hexVal_zero : hexVal '0' = some 0 := rfl

theorem bs_ne_quote : ('\\' : Char) ≠ '"' := by decide

/-- The escape of a control character reads back. -/
theorem unquote_ctrl {c : Char} (hc : c.toNat < 0x20) (r : List Char) :
    unquote (['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)] ++ r) =
      (unquote r).map fun (s, r) => (c :: s, r) := by
  have h1 : hexVal (hexDigit (c.toNat / 16)) = some (c.toNat / 16) := hexVal_hexDigit (by omega)
  have h2 : hexVal (hexDigit (c.toNat % 16)) = some (c.toNat % 16) := hexVal_hexDigit (by omega)
  simp only [List.cons_append, List.nil_append]
  rw [unquote.eq_def]; dsimp only
  simp only [bs_ne_quote, ite_false, ite_true]
  cases unquote r <;> simp [hexVal_zero, h1, h2, Nat.div_add_mod', Char.ofNat_toNat]

/-- A character needing no escape reads back. -/
theorem unquote_plain {c : Char} (h1 : c ≠ '"') (h2 : c ≠ '\\') (r : List Char) :
    unquote (c :: r) = (unquote r).map fun (s, r) => (c :: s, r) := by
  rw [unquote.eq_def]; dsimp only
  simp only [h1, h2, ite_false]
  cases unquote r <;> rfl

/-- A two-character escape reads back. -/
theorem unquote_esc2 {c e : Char} (he : e ≠ 'u') (hm : unesc e = some c) (r : List Char) :
    unquote ('\\' :: e :: r) = (unquote r).map fun (s, r) => (c :: s, r) := by
  rw [unquote.eq_def]; dsimp only
  simp only [bs_ne_quote, ite_false, ite_true, he, hm]
  cases unquote r <;> rfl

theorem unquote_escChar (c : Char) (r : List Char) :
    unquote (escChar c ++ r) = (unquote r).map fun (s, r) => (c :: s, r) := by
  unfold escChar
  split
  · next h => rw [h]; exact unquote_esc2 (by decide) rfl r
  split
  · next h => rw [h]; exact unquote_esc2 (by decide) rfl r
  split
  · next h => rw [h]; exact unquote_esc2 (by decide) rfl r
  split
  · next h => rw [h]; exact unquote_esc2 (by decide) rfl r
  split
  · next h => rw [h]; exact unquote_esc2 (by decide) rfl r
  split
  · next h => rw [h]; exact unquote_esc2 (by decide) rfl r
  split
  · next h => rw [h]; exact unquote_esc2 (by decide) rfl r
  split
  · next h => exact unquote_ctrl h r
  · next h₁ h₂ _ _ _ _ _ _ => exact unquote_plain h₁ h₂ r

theorem unquote_quote (s r : List Char) : unquote (s.flatMap escChar ++ '"' :: r) = some (s, r) := by
  induction s with
  | nil => rw [List.flatMap_nil, List.nil_append, unquote.eq_def]; simp
  | cons c s ih => rw [List.flatMap_cons, List.append_assoc, unquote_escChar, ih]; rfl

/-! ## Objects -/

theorem quoteChars_eq (s : List Char) (r : List Char) :
    quoteChars s ++ r = '"' :: (s.flatMap escChar ++ '"' :: r) := by
  simp [quoteChars]

theorem parseAux_quote (n : Nat) (r : List Char) :
    JVal.parseAux (n + 1) ('"' :: r) = (unquote r).map fun (s, r) => (.str (String.ofList s), r) := by
  rw [JVal.parseAux.eq_def]; rfl

theorem parseAux_empty (n : Nat) (r : List Char) : JVal.parseAux (n + 1) ('{' :: '}' :: r) = some (.obj [], r) := by
  rw [JVal.parseAux.eq_def]; rfl

theorem parseAux_obj (n : Nat) (r : List Char) :
    JVal.parseAux (n + 1) ('{' :: '"' :: r) = (JVal.parseMembers n ('"' :: r)).map fun (fs, r) => (.obj fs, r) := by
  rw [JVal.parseAux.eq_def]; rfl

theorem parseMembers_quote (n : Nat) (r : List Char) :
    JVal.parseMembers (n + 1) ('"' :: r) = (do
      let (k, r) ← unquote r
      let r ← match r with | ':' :: r => some r | _ => none
      let (v, r) ← JVal.parseAux n r
      match r with
      | '}' :: r => pure ([(String.ofList k, v)], r)
      | ',' :: r => do
        let (fs, r) ← JVal.parseMembers n r
        pure ((String.ofList k, v) :: fs, r)
      | _ => none) := by
  rw [JVal.parseMembers.eq_def]; rfl

theorem printMembers_cons (k : String) (v : JVal) (fs : List (String × JVal)) :
    JVal.printMembers ((k, v) :: fs) = quoteChars k.toList ++ ':' :: (v.print ++ JVal.printRest fs) := by
  rw [JVal.printMembers]

theorem printRest_cons (k : String) (v : JVal) (fs : List (String × JVal)) :
    JVal.printRest ((k, v) :: fs) = ',' :: JVal.printMembers ((k, v) :: fs) := by
  rw [JVal.printRest, printMembers_cons]

theorem len_printMembers (k : String) (v : JVal) (fs : List (String × JVal)) :
    v.print.length + (JVal.printRest fs).length + 3 ≤ (JVal.printMembers ((k, v) :: fs)).length := by
  rw [printMembers_cons]; simp [quoteChars]

mutual
/-- **The JSON reader inverts the printer**, given enough fuel. -/
theorem parseAux_print : ∀ (v : JVal) (n : Nat) (r : List Char), v.print.length ≤ n →
    JVal.parseAux n (v.print ++ r) = some (v, r)
  | .str s, 0, r, h => by simp [JVal.print, quoteChars] at h
  | .str s, m + 1, r, _ => by
    rw [JVal.print, quoteChars_eq, parseAux_quote, unquote_quote]; simp [String.ofList_toList]
  | .obj [], 0, r, h => by simp [JVal.print] at h
  | .obj [], m + 1, r, _ => by
    rw [JVal.print, JVal.printMembers]; exact parseAux_empty m r
  | .obj ((k, v) :: fs), 0, r, h => by simp [JVal.print] at h
  | .obj ((k, v) :: fs), m + 1, r, h => by
    have hl : (JVal.printMembers ((k, v) :: fs)).length < m := by
      simp only [JVal.print, List.length_cons, List.length_append] at h; simp at h; omega
    have hm := parseMembers_print ((k, v) :: fs) m r (by simp) hl
    have he : (JVal.obj ((k, v) :: fs)).print ++ r =
        '{' :: '"' :: (k.toList.flatMap escChar ++ '"' :: ':' :: (v.print ++ (JVal.printRest fs ++ '}' :: r))) := by
      simp [JVal.print, printMembers_cons, quoteChars]
    have hm' : JVal.parseMembers m ('"' :: (k.toList.flatMap escChar ++ '"' :: ':' :: (v.print ++ (JVal.printRest fs ++ '}' :: r)))) = some ((k, v) :: fs, r) := by
      rw [← hm, printMembers_cons]; simp [quoteChars]
    rw [he, parseAux_obj, hm']; rfl

theorem parseMembers_print : ∀ (fs : List (String × JVal)) (n : Nat) (r : List Char), fs ≠ [] →
    (JVal.printMembers fs).length < n → JVal.parseMembers n (JVal.printMembers fs ++ '}' :: r) = some (fs, r)
  | [], _, _, h, _ => absurd rfl h
  | (k, v) :: fs, 0, r, _, h => absurd h (Nat.not_lt_zero _)
  | (k, v) :: fs, m + 1, r, _, h => by
    have hlen := len_printMembers k v fs
    have hpa := parseAux_print v m (JVal.printRest fs ++ '}' :: r) (by omega)
    rw [printMembers_cons, quoteChars_eq, List.cons_append, parseMembers_quote]
    simp only [List.cons_append, List.append_assoc]
    rw [unquote_quote]
    cases fs with
    | nil => simp [JVal.printRest] at hpa ⊢; simp [hpa]
    | cons f fs =>
      obtain ⟨k', v'⟩ := f
      have hms := parseMembers_print ((k', v') :: fs) m r (by simp)
        (by rw [printRest_cons] at hlen; simp at hlen; omega)
      rw [printRest_cons] at hpa ⊢
      simp only [List.cons_append] at hpa
      simp [hpa, hms]
end

/-- **`package-docs` JSON reads back.** -/
theorem JVal.parse_print (v : JVal) : JVal.parse v.print = some v := by
  have h := parseAux_print v (v.print.length + 1) [] (Nat.le_succ _)
  rw [List.append_nil] at h
  simp only [JVal.parse, h]

end Silmaril.Wasm.Wit.Binary
