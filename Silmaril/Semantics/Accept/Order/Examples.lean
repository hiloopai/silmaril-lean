module

public import Silmaril.Semantics.Accept.Order.Thms
public import Mathlib.Data.List.Perm.Basic

/-! # Programs ordered by language: worked examples and regression tests

Programs are lists of naturals accepting their members (`listLang`); a second shape is a bound
`n` accepting everything below it (`belowLang`). The supplied equivalence is permutation of
lists. Every `example` is checked when the library builds.
-/

@[expose] public section

namespace Silmaril.Accept.OrderExamples

open Silmaril.Accept

/-- A list accepts its members. -/
def listLang (l : List ℕ) : Set ℕ := {n | n ∈ l}

/-- A bound accepts the numbers below it. -/
def belowLang (n : ℕ) : Set ℕ := {k | k < n}

/-! ## The preorder is not antisymmetric -/

example : LangPre.of listLang [1] ≤ LangPre.of listLang [2, 1] := by
  simp [listLang]

/-- `[1]` and `[1, 1]` are different programs with the same language. -/
example : AntisymmRel (· ≤ ·) (LangPre.of listLang [1]) (LangPre.of listLang [1, 1]) :=
  LangPre.antisymmRel_iff.2 (by ext; simp [listLang])

/-! ## A supplied equivalence: permutation -/

instance : RespectsLang (List.isSetoid ℕ) listLang :=
  ⟨fun _ _ h => Set.ext fun _ => h.mem_iff⟩

/-- Permutation identifies `[1, 2]` and `[2, 1]` … -/
example : LangQuot.mk (List.isSetoid ℕ) listLang [1, 2] = LangQuot.mk _ _ [2, 1] :=
  LangQuot.mk_eq_mk_iff.2 (List.Perm.swap 2 1 [])

/-- … but not `[1]` and `[1, 1]`, which are only equivalent in the preorder. -/
example : LangQuot.mk (List.isSetoid ℕ) listLang [1] ≠ LangQuot.mk _ _ [1, 1] := fun h =>
  absurd (LangQuot.mk_eq_mk_iff.1 h).length_eq (by decide)

/-- So permutation is strictly finer than equal language. -/
example : ¬ Function.Injective
    (LangQuot.toLangEq (s := List.isSetoid ℕ) (lang := listLang)) := fun h =>
  absurd ((LangQuot.toLangEq_injective_iff.1 h) [1] [1, 1] (by ext; simp [listLang])).length_eq
    (by decide)

/-! ## The partial order of languages -/

example : LangEq.mk listLang [1] = LangEq.mk listLang [1, 1] :=
  LangEq.mk_eq_mk_iff.2 (by ext; simp [listLang])

/-! ## Two shapes in one order -/

/-- A list and a bound with the same language: distinct programs, equal in `LangEq`. -/
example : LangEq.mk (langSum listLang belowLang) (Sum.inl [0, 1]) =
    LangEq.mk _ (Sum.inr 2) :=
  LangEq.mk_inl_eq_mk_inr_iff.2 (by ext k; simp [listLang, belowLang]; omega)

example : (Sum.inl [0, 1] : List ℕ ⊕ ℕ) ≠ Sum.inr 2 := Sum.inl_ne_inr

/-- Comparison across shapes is inclusion of languages. -/
example : LangPre.of (langSum listLang belowLang) (Sum.inl [0]) ≤ LangPre.of _ (Sum.inr 5) :=
  inl_le_inr_iff.2 (by simp [listLang, belowLang])

/-- The left shape is an order embedding. -/
example (l l' : List ℕ) :
    inlEmb (lang₂ := belowLang) (LangPre.of listLang l) ≤ inlEmb (LangPre.of listLang l') ↔
      listLang l ⊆ listLang l' :=
  inlEmb.le_iff_le

end Silmaril.Accept.OrderExamples
