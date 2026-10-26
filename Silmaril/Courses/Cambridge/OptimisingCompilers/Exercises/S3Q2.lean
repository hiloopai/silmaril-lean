module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.ControlFlowAnalysis

/-! # Exercise sheet 3, question 2 (0CFA with integer flows)

Source: `cam-optcomp-2025-exercise-sheet-3` in `references.bib`, question 2.


(a) A *binding site* introduces a variable: the `v` of `λv.e` and of
`let v = e₁ in e₂` (`Term.lam`, `Term.letE` carry its label). A *use site* is an
occurrence `v` as an expression (`Term.var`).

(b) `exampleB` labels every node; the binder of `x` is `0`.

(c) `alpha0_B`: `α₀ = {2, 3}`. No integer values flow out of the body: 0CFA
does not evaluate `⊕`, so the body's flow set is empty (`body_B`).

(d) The clauses of `Term.Sat` (notes p. 27): a use `vⁱ` bound at `j` gives
`αᵢ ⊇ αⱼ`; `(let vˡ = e₁ʲ in e₂ᵏ)ⁱ` gives `αₗ ⊇ αⱼ` (the variable gets the
bound value) and `αᵢ ⊇ αₖ` (the let yields its body's value).

(e) `alpha1_E`: `α₁ = {λy.y+1}`; `alpha0_E`: `α₀ = {0, 1}`.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S3Q2

open ControlFlowAnalysis

/-- (b) `(let f¹⁰ = (λx⁰.(x¹¹ + x¹²)¹³)¹⁴ in ((f¹⁵ 2¹⁶)¹⁷ + (f¹⁸ 3¹⁹)²⁰)²¹)¹`. -/
def exampleB : Term :=
  .letE 1 10 "f" (.lam 14 0 "x" (.binop 13 (.var 11 "x") (.var 12 "x")))
    (.binop 21 (.app 17 (.var 15 "f") (.const 16 2)) (.app 20 (.var 18 "f") (.const 19 3)))

/-- The least solution for `exampleB`. -/
def solB (l : ℕ) : Set FlowVal :=
  if l ∈ [14, 10, 15, 18] then {.lam 14}
  else if l = 16 then {.const 2 16}
  else if l = 19 then {.const 3 19}
  else if l ∈ [0, 11, 12] then {.const 2 16, .const 3 19}
  else ∅

theorem solB_mem : solB ∈ exampleB.solutions := by
  simp only [Term.solutions, Set.mem_ofPred_eq, exampleB, Term.Sat, Term.lams, Term.label,
    List.append_nil, Term.forall_mem_triple_iff,
    List.forall_mem_cons]
  simp [solB]

/-- (c) `α₀ = {2, 3}`. -/
theorem alpha0_B : exampleB.cfa 0 = {.const 2 16, .const 3 19} := by
  refine Term.cfa_apply_eq solB_mem (by simp [solB]) fun α hα => ?_
  obtain ⟨⟨h14, h11, h12⟩, ⟨⟨h15, h16, a17⟩, ⟨h18, h19, a20⟩⟩, s1, s10⟩ := hα
  have hL : ((14 : ℕ), (0 : ℕ), (13 : ℕ)) ∈ exampleB.lams := by
    simp [exampleB, Term.lams, Term.label]
  have m14 : FlowVal.lam 14 ∈ α 14 := h14
  have m10 : FlowVal.lam 14 ∈ α 10 := s10 m14
  have m15 : FlowVal.lam 14 ∈ α 15 := h15 10 (by simp) m10
  have m18 : FlowVal.lam 14 ∈ α 18 := h18 10 (by simp) m10
  have c2 : FlowVal.const 2 16 ∈ α 0 := (a17 14 0 13 hL m15).1 h16
  have c3 : FlowVal.const 3 19 ∈ α 0 := (a20 14 0 13 hL m18).1 h19
  exact Set.insert_subset_iff.2 ⟨c2, Set.singleton_subset_iff.2 c3⟩

/-- (c) Nothing flows out of the body `x + x`. -/
theorem body_B : exampleB.cfa 13 = ∅ :=
  Set.subset_empty_iff.1 fun _ hx => by
    have := Term.cfa_le solB_mem 13 hx
    simp [solB] at this

/-- (e) `(let f²⁰ = (λx²¹.(x¹ 0²²)²³)²⁴ in
(let g²⁵ = (λy⁰.(y²⁶ + 1²⁷)²⁸)²⁹ in ((f³⁰ g³¹)³² + (g³³ 1³⁴)³⁵)³⁶)³⁷)³⁸`. -/
def exampleE : Term :=
  .letE 38 20 "f" (.lam 24 21 "x" (.app 23 (.var 1 "x") (.const 22 0)))
    (.letE 37 25 "g" (.lam 29 0 "y" (.binop 28 (.var 26 "y") (.const 27 1)))
      (.binop 36 (.app 32 (.var 30 "f") (.var 31 "g")) (.app 35 (.var 33 "g") (.const 34 1))))

/-- The least solution for `exampleE`. -/
def solE (l : ℕ) : Set FlowVal :=
  if l ∈ [24, 20, 30] then {.lam 24}
  else if l ∈ [29, 25, 31, 33, 21, 1] then {.lam 29}
  else if l = 22 then {.const 0 22}
  else if l = 27 then {.const 1 27}
  else if l = 34 then {.const 1 34}
  else if l ∈ [0, 26] then {.const 0 22, .const 1 34}
  else ∅

theorem solE_mem : solE ∈ exampleE.solutions := by
  simp only [Term.solutions, Set.mem_ofPred_eq, exampleE, Term.Sat, Term.lams, Term.label,
    List.cons_append, List.nil_append, List.append_nil, Term.forall_mem_triple_iff,
    List.forall_mem_cons]
  simp [solE]

/-- The facts every solution of `exampleE`'s constraints satisfies. -/
theorem exampleE_lower {α : ℕ → Set FlowVal} (hα : α ∈ exampleE.solutions) :
    FlowVal.lam 29 ∈ α 1 ∧ FlowVal.const 0 22 ∈ α 0 ∧ FlowVal.const 1 34 ∈ α 0 := by
  obtain ⟨⟨m24, h1, c22, a23⟩, ⟨⟨m29, h26, c27⟩, ⟨⟨h30, h31, a32⟩, ⟨h33, c34, a35⟩⟩, s37, s25⟩,
    s38, s20⟩ := hα
  have hL24 : ((24 : ℕ), (21 : ℕ), (23 : ℕ)) ∈ exampleE.lams := by
    simp [exampleE, Term.lams, Term.label]
  have hL29 : ((29 : ℕ), (0 : ℕ), (28 : ℕ)) ∈ exampleE.lams := by
    simp [exampleE, Term.lams, Term.label]
  have n24 : FlowVal.lam 24 ∈ α 24 := m24
  have n29 : FlowVal.lam 29 ∈ α 29 := m29
  have n25 : FlowVal.lam 29 ∈ α 25 := s25 n29
  have n31 : FlowVal.lam 29 ∈ α 31 := h31 25 (by simp) n25
  have n33 : FlowVal.lam 29 ∈ α 33 := h33 25 (by simp) n25
  have n20 : FlowVal.lam 24 ∈ α 20 := s20 n24
  have n30 : FlowVal.lam 24 ∈ α 30 := h30 20 (by simp) n20
  have n21 : FlowVal.lam 29 ∈ α 21 := (a32 24 21 23 hL24 n30).1 n31
  have n1 : FlowVal.lam 29 ∈ α 1 := h1 21 (by simp) n21
  have z0 : FlowVal.const 0 22 ∈ α 0 := (a23 29 0 28 hL29 n1).1 c22
  have o0 : FlowVal.const 1 34 ∈ α 0 := (a35 29 0 28 hL29 n33).1 c34
  exact ⟨n1, z0, o0⟩

/-- (e) `α₁ = {λy.y+1}`. -/
theorem alpha1_E : exampleE.cfa 1 = {.lam 29} :=
  Term.cfa_apply_eq solE_mem (by simp [solE]) fun _ hα =>
    Set.singleton_subset_iff.2 (exampleE_lower hα).1

/-- (e) `α₀ = {0, 1}`. -/
theorem alpha0_E : exampleE.cfa 0 = {.const 0 22, .const 1 34} :=
  Term.cfa_apply_eq solE_mem (by simp [solE]) fun _ hα =>
    Set.insert_subset_iff.2
      ⟨(exampleE_lower hα).2.1, Set.singleton_subset_iff.2 (exampleE_lower hα).2.2⟩

end Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S3Q2
