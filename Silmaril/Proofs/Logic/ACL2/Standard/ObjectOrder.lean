module

public import Silmaril.Logic.ACL2.Standard.ObjectOrder.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.Standard.ObjectOrder

open Silmaril.Logic.ACL2.Standard Silmaril.Logic.ACL2.Standard.ObjectOrder
open scoped Silmaril.Logic.ACL2.Standard.ObjectOrder

theorem stringLessIndex_spec (x y : ByteString) (i : Nat) :
    (stringLessIndex x y i).isSome = true ↔ x < y := by
  induction x generalizing y i with
  | nil => cases y <;> simp [stringLessIndex]
  | cons a as ih =>
    cases y with
    | nil => simp [stringLessIndex]
    | cons b bs =>
      by_cases h : a = b
      · subst b
        simp [stringLessIndex, ih]
      · simp [stringLessIndex, h, List.cons_lt_cons_iff]

theorem stringLeIndex_spec (x y : ByteString) : (stringLeIndex x y).isSome = true ↔ x ≤ y := by
  by_cases h : x = y
  · subst y
    simp [stringLeIndex]
  · simp [stringLeIndex, h, stringLessIndex_spec, le_iff_lt_or_eq]

theorem symbolLess_spec (x y : Symbol) : symbolLess x y = true ↔
    x.spelling < y.spelling ∨ x.spelling = y.spelling ∧ x.package < y.package := by
  simp [symbolLess, stringLessIndex_spec]

theorem before_eq_true (x y : Object) : before x y = true ↔ encode x [] < encode y [] := by
  unfold before
  exact Iff.of_eq decide_eq_true_eq

/-- Appending continuations exposes the right subtrees only after the left
subtrees compare equal. The statement also rules out false equality of codes. -/
theorem encode_lt (x y : Object) (s t : List Key) :
    encode x s < encode y t ↔ encode x [] < encode y [] ∨ x = y ∧ s < t := by
  induction x generalizing y s t <;> cases y
  case cons.cons a b ihA ihB c d =>
    simp only [encode, key, List.cons_lt_cons_iff, true_and, Object.cons.injEq]
    rw [ihA c (encode b s) (encode d t), ihA c (encode b []) (encode d []), ihB d s t]
    have hm : ¬ key (.cons a b) < key (.cons a b) := lt_irrefl _
    have hn : ¬ ([] : List Key) < [] := lt_irrefl _
    simp only [key] at hm
    tauto
  case symbol.symbol a b =>
    cases a
    cases b
    simp [encode, List.cons_lt_cons_iff, key, key.make, and_comm]
  all_goals simp [encode, List.cons_lt_cons_iff, key, key.make, Prod.Lex.toLex_lt_toLex]

theorem encode_append (x : Object) (tail : List Key) :
    encode x tail = encode x [] ++ tail := by
  induction x generalizing tail <;> try rfl
  case cons a b ihA ihB =>
    simp only [encode, List.cons_append]
    rw [ihA (encode b tail), ihA (encode b []), ihB tail, List.append_assoc]

theorem encode_injective : Function.Injective (fun x : Object => encode x []) := by
  intro x y h
  change encode x [] = encode y [] at h
  have htail : encode x [] < encode y [key y] := by
    rw [encode_append y [key y], h]
    have shorter := (List.append_left_lt_iff (encode y [])).2
      (show ([] : List Key) < [key y] from List.nil_lt_iff.2 (by simp))
    simpa only [List.append_nil] using shorter
  rcases (encode_lt x y [] [key y]).1 htail with lt | ⟨eq, _⟩
  · rw [h] at lt
    exact (lt_irrefl _ lt).elim
  · exact eq

theorem before_cons (a b c d : Object) :
    before (.cons a b) (.cons c d) = if a = c then before b d else before a c := by
  apply Bool.eq_iff_iff.mpr
  rw [before_eq_true]
  simp only [encode, key, List.cons_lt_cons_iff, true_and]
  rw [encode_lt a c (encode b []) (encode d [])]
  by_cases h : a = c
  · subst c
    simp [before_eq_true]
  · simp [before_eq_true, h]

theorem lexorder_cons (a b c d : Object) :
    lexorder (.cons a b) (.cons c d) = if a = c then lexorder b d else lexorder a c := by
  by_cases h : a = c
  · rw [lexorder, before_cons, ite_eq_left h.symm, ite_eq_left h, lexorder]
  · rw [lexorder, before_cons, ite_eq_right (Ne.symm h), ite_eq_right h, lexorder]

theorem before_native (x y : Object) :
    before x y = (lexorder x y && decide (x ≠ y)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [before, lexorder, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, not_lt]
  exact ⟨fun h => ⟨le_of_lt h, fun eq => (ne_of_lt h) (congrArg (fun t => encode t []) eq)⟩,
    fun ⟨le, ne⟩ => lt_of_le_of_ne le (fun eq => ne (encode_injective eq))⟩

theorem lexorder_atoms (x y : Object) (hx : x.consp = false) (hy : y.consp = false) :
    lexorder x y = true ↔ key x ≤ key y := by
  have atom (a : Object) (h : a.consp = false) : encode a [] = [key a] := by
    cases a <;> first | contradiction | rfl
  simp [lexorder, Bool.eq_false_iff, before_eq_true, atom _ hx, atom _ hy, List.cons_lt_cons_iff]

theorem lexorder_atom_cons (x a b : Object) (hx : x.consp = false) :
    lexorder x (.cons a b) = true := by
  cases x <;> simp_all [Object.consp, lexorder, Bool.eq_false_iff, before_eq_true, encode,
    key, key.make, List.cons_lt_cons_iff, Prod.Lex.toLex_lt_toLex]

theorem lexorder_cons_atom (a b y : Object) (hy : y.consp = false) :
    lexorder (.cons a b) y = false := by
  cases y <;> simp_all [Object.consp, lexorder, before_eq_true, encode,
    key, key.make, List.cons_lt_cons_iff, Prod.Lex.toLex_lt_toLex]

theorem lexorder_symbols (x y : Symbol) :
    lexorder (.symbol x) (.symbol y) = !symbolLess y x := by
  have eq : before (.symbol y) (.symbol x) = symbolLess y x := by
    apply Bool.eq_iff_iff.mpr
    rw [before_eq_true, symbolLess_spec]
    simp [encode, key, key.make, List.cons_lt_cons_iff, Prod.Lex.toLex_lt_toLex]
  simp only [lexorder, eq]

theorem lexorder_strings (x y : ByteString) :
    lexorder (.string x) (.string y) = (stringLeIndex x y).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [lexorder_atoms _ _ rfl rfl, stringLeIndex_spec]
  simp [key, key.make, Prod.Lex.toLex_lt_toLex, le_iff_lt_or_eq]

theorem lexorder_alphorder (x y : Object) (hx : x.consp = false) (hy : y.consp = false) :
    lexorder x y = alphorder x y := by
  cases x <;> cases y <;> try contradiction
  case string.string x y => exact lexorder_strings x y
  case symbol.symbol x y => exact lexorder_symbols x y
  all_goals
    apply Bool.eq_iff_iff.mpr
    rw [lexorder_atoms _ _ rfl rfl]
    simp [alphorder, key, key.make, Prod.Lex.toLex_lt_toLex,
      List.cons_lt_cons_iff, le_iff_lt_or_eq]
  case complexRational.complexRational => tauto

theorem before_irrefl (x : Object) : before x x = false :=
  Bool.eq_false_iff.mpr (fun h => lt_irrefl _ ((before_eq_true x x).1 h))

theorem before_trans {x y z : Object} (hxy : before x y = true) (hyz : before y z = true) :
    before x z = true :=
  (before_eq_true x z).2 (lt_trans ((before_eq_true x y).1 hxy) ((before_eq_true y z).1 hyz))

theorem before_asymm {x y : Object} (h : before x y = true) : before y x = false :=
  Bool.eq_false_iff.mpr (fun rev => not_lt_of_gt ((before_eq_true x y).1 h) ((before_eq_true y x).1 rev))

theorem before_trichotomy (x y : Object) : before x y = true ∨ x = y ∨ before y x = true := by
  rcases lt_trichotomy (encode x []) (encode y []) with h | h | h
  · exact Or.inl ((before_eq_true x y).2 h)
  · exact Or.inr (Or.inl (encode_injective h))
  · exact Or.inr (Or.inr ((before_eq_true y x).2 h))

end Silmaril.Proofs.Logic.ACL2.Standard.ObjectOrder
