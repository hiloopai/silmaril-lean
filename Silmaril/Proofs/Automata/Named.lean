module

public import Silmaril.Automata.Named.Defs

/-!
# Finite named types: proofs

Injectivity of the names of `Option`, `Sum` and `Prod` (for `Silmaril.Automata.Named.Thms`).
The key lemma is `esc_split`: in `escape a ++ "," ++ escape b` the first unescaped comma is
the separator.
-/

@[expose] public section

namespace Silmaril.Proofs.Automata

open Silmaril.Automata

theorem escChar_head (c : Char) : ∃ t, escChar c = (if c = ',' ∨ c = '\\' then '\\' else c) :: t := by
  unfold escChar; split <;> simp_all

theorem esc_split : ∀ (a a' r r' : List Char),
    a.flatMap escChar ++ ',' :: r = a'.flatMap escChar ++ ',' :: r' → a = a' ∧ r = r'
  | [], [], r, r', h => by simpa using h
  | [], c :: t, r, r', h => by
    exfalso
    simp only [List.flatMap_nil, List.nil_append, List.flatMap_cons, List.append_assoc] at h
    unfold escChar at h
    split at h
    · simp at h
    · next hc =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨h1, -⟩ := h
      subst h1; simp at hc
  | c :: t, [], r, r', h => by
    exfalso
    simp only [List.flatMap_nil, List.nil_append, List.flatMap_cons, List.append_assoc] at h
    unfold escChar at h
    split at h
    · simp at h
    · next hc =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨h1, -⟩ := h
      subst h1; simp at hc
  | c :: t, c' :: t', r, r', h => by
    simp only [List.flatMap_cons, List.append_assoc] at h
    unfold escChar at h
    split at h <;> split at h
    · simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, h⟩ := h
      have := esc_split t t' r r' h
      exact ⟨by rw [this.1], this.2⟩
    · next hc hc' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      exact absurd (Or.inr h.1.symm) hc'
    · next hc hc' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      exact absurd (Or.inr h.1) hc
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have := esc_split t t' r r' h
      exact ⟨by rw [this.1], this.2⟩

theorem pairName_inj {a b a' b' : String} (h : pairName a b = pairName a' b') :
    a = a' ∧ b = b' := by
  have h' := congrArg String.toList h
  simp only [pairName, escapeName, String.toList_append, String.toList_ofList] at h'
  simp only [String.reduceToList, List.cons_append, List.nil_append, List.cons.injEq, true_and,
    List.append_assoc] at h'
  obtain ⟨h1, h2⟩ := esc_split _ _ _ _ h'
  have h3 := List.append_cancel_right h2
  refine ⟨String.toList_inj.mp h1, String.toList_inj.mp ?_⟩
  -- `escChar` is injective on lists: a flatMap that splits uniquely
  have key : ∀ x y : List Char, x.flatMap escChar = y.flatMap escChar → x = y := by
    intro x y hxy
    have := esc_split x y [] [] (by rw [hxy])
    exact this.1
  exact key _ _ h3

theorem wrap_inj (p : String) {a b : String} (h : p ++ a ++ ")" = p ++ b ++ ")") : a = b := by
  have h' := congrArg String.toList h
  simp only [String.toList_append, List.append_assoc] at h'
  exact String.toList_inj.mp (List.append_cancel_right (List.append_cancel_left h'))

theorem someName_inj {a b : String} (h : someName a = someName b) : a = b := wrap_inj _ h
theorem inlName_inj {a b : String} (h : inlName a = inlName b) : a = b := wrap_inj _ h
theorem inrName_inj {a b : String} (h : inrName a = inrName b) : a = b := wrap_inj _ h

theorem none_ne_someName (a : String) : "none" ≠ someName a := by
  intro h
  have h' := congrArg String.toList h
  simp [someName, String.toList_append] at h'

theorem inlName_ne_inrName (a b : String) : inlName a ≠ inrName b := by
  intro h
  have h' := congrArg String.toList h
  simp [inlName, inrName, String.toList_append] at h'

theorem name_injective {α : Type} [FinNamed α] : Function.Injective (FinNamed.name (α := α)) :=
  fun a b h => List.inj_on_of_nodup_map FinNamed.nodup (FinNamed.complete a)
    (FinNamed.complete b) h

theorem elems_nodup {α : Type} [FinNamed α] : (FinNamed.elems (α := α)).Nodup :=
  List.Nodup.of_map _ FinNamed.nodup

end Silmaril.Proofs.Automata
