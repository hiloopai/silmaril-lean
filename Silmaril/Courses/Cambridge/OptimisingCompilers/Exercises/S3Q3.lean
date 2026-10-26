module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.ControlFlowAnalysis

/-! # Exercise sheet 3, question 3 (0CFA of function flows)

Source: `cam-optcomp-2025-exercise-sheet-3` in `references.bib`, question 3.


The analysis `Term.cfa` tracks constants too; the function values are its
`FlowVal.lam` elements, and restricting to them gives the requested analysis.

(a) With the labelling of `example3`, `alphaX`: `x` may be bound to either
argument, `{λy.y∗3, λz.z+1}`, so the application `x 0` may call either; `f` is
only ever `λx.x 0` (`alphaF`).

(b) The clauses of `Term.Sat` (notes p. 27): `(λxʲ.eᵏ)ⁱ` gives
`αᵢ ⊇ {(λxʲ.eᵏ)ⁱ}` (an abstraction evaluates to itself), and `(e₁ʲ e₂ᵏ)ⁱ` gives,
for every `(λx_q.e_r)ₚ` that may flow to `αⱼ`, `α_q ⊇ αₖ` (the argument flows to
the parameter) and `αᵢ ⊇ α_r` (the body's result flows out of the call).
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S3Q3

open ControlFlowAnalysis

/-- `(let f¹ = (λx².(x³ 0⁴)⁵)⁶ in
((f⁷ (λy⁸.(y⁹ ∗ 3¹⁰)¹¹)¹²)¹³ + (f¹⁴ (λz¹⁵.(z¹⁶ + 1¹⁷)¹⁸)¹⁹)²⁰)²¹)²²`. -/
def example3 : Term :=
  .letE 22 1 "f" (.lam 6 2 "x" (.app 5 (.var 3 "x") (.const 4 0)))
    (.binop 21
      (.app 13 (.var 7 "f") (.lam 12 8 "y" (.binop 11 (.var 9 "y") (.const 10 3))))
      (.app 20 (.var 14 "f") (.lam 19 15 "z" (.binop 18 (.var 16 "z") (.const 17 1)))))

/-- The function values flowing to a point. -/
def funFlows (P : Term) (l : ℕ) : Set ℕ := {p | FlowVal.lam p ∈ P.cfa l}

/-- The least solution for `example3`. -/
def sol3 (l : ℕ) : Set FlowVal :=
  if l ∈ [6, 1, 7, 14] then {.lam 6}
  else if l = 12 then {.lam 12}
  else if l = 19 then {.lam 19}
  else if l ∈ [2, 3] then {.lam 12, .lam 19}
  else if l = 4 then {.const 0 4}
  else if l = 10 then {.const 3 10}
  else if l = 17 then {.const 1 17}
  else if l ∈ [8, 9, 15, 16] then {.const 0 4}
  else ∅

theorem sol3_mem : sol3 ∈ example3.solutions := by
  simp only [Term.solutions, Set.mem_ofPred_eq, example3, Term.Sat, Term.lams, Term.label,
    List.cons_append, List.nil_append, List.append_nil, Term.forall_mem_triple_iff,
    List.forall_mem_cons]
  simp [sol3]

/-- The function flows of every solution of `example3`'s constraints. -/
theorem example3_lower {α : ℕ → Set FlowVal} (hα : α ∈ example3.solutions) :
    FlowVal.lam 6 ∈ α 1 ∧ FlowVal.lam 12 ∈ α 2 ∧ FlowVal.lam 19 ∈ α 2 := by
  obtain ⟨⟨m6, h3, c4, a5⟩, ⟨⟨h7, ⟨l12, h9, c10⟩, a13⟩, ⟨h14, ⟨l19, h16, c17⟩, a20⟩⟩, s22, s1⟩ := hα
  have hL : ((6 : ℕ), (2 : ℕ), (5 : ℕ)) ∈ example3.lams := by
    simp [example3, Term.lams, Term.label]
  have n6 : FlowVal.lam 6 ∈ α 6 := m6
  have n1 : FlowVal.lam 6 ∈ α 1 := s1 n6
  have n7 : FlowVal.lam 6 ∈ α 7 := h7 1 (by simp) n1
  have n14 : FlowVal.lam 6 ∈ α 14 := h14 1 (by simp) n1
  have n12 : FlowVal.lam 12 ∈ α 12 := l12
  have n19 : FlowVal.lam 19 ∈ α 19 := l19
  exact ⟨n1, (a13 6 2 5 hL n7).1 n12, (a20 6 2 5 hL n14).1 n19⟩

/-- No function flows to a point where `sol3` has none. -/
theorem funFlows_eq_empty {l : ℕ} (h : ∀ p, FlowVal.lam p ∉ sol3 l) : funFlows example3 l = ∅ :=
  Set.eq_empty_of_forall_notMem fun p hp => h p (Term.cfa_le sol3_mem l hp)

/-- (a) `x` may be either argument. -/
theorem alphaX : funFlows example3 2 = {12, 19} := by
  have h : example3.cfa 2 = {.lam 12, .lam 19} :=
    Term.cfa_apply_eq sol3_mem (by simp [sol3]) fun _ hα =>
      Set.insert_subset_iff.2
        ⟨(example3_lower hα).2.1, Set.singleton_subset_iff.2 (example3_lower hα).2.2⟩
  ext p
  simp [funFlows, h]

/-- (a) `f` is only ever `λx.x 0`. -/
theorem alphaF : funFlows example3 1 = {6} := by
  have h : example3.cfa 1 = {.lam 6} :=
    Term.cfa_apply_eq sol3_mem (by simp [sol3]) fun _ hα =>
      Set.singleton_subset_iff.2 (example3_lower hα).1
  ext p
  simp [funFlows, h]

/-- (a) No function flows to `y` or `z`, or out of the calls. -/
theorem alpha_rest : funFlows example3 8 = ∅ ∧ funFlows example3 15 = ∅ ∧
    funFlows example3 13 = ∅ ∧ funFlows example3 20 = ∅ := by
  refine ⟨funFlows_eq_empty ?_, funFlows_eq_empty ?_, funFlows_eq_empty ?_,
    funFlows_eq_empty ?_⟩ <;> simp [sol3]

end Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S3Q3
