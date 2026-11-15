module

public import Silmaril.Semantics.Accept.Rel.Thms

/-! # Acceptance through relations: worked examples and regression tests

A partial decoder (`half`, defined on even numbers), a nondeterministic relation (`succOrDouble`),
their composition, and indexed languages. Every `example` is checked when the library builds.
-/

@[expose] public section

namespace Silmaril.Accept.RelExamples

open Silmaril.Accept
open scoped SetRel

/-- A partial decoder: halves even numbers, fails on odd ones. -/
def half (n : ℕ) : Option ℕ := if n % 2 = 0 then some (n / 2) else none

/-- The small numbers. -/
def small : Set ℕ := {n | n < 3}

/-- `5` has no output: it is never rejected by `small` but never accepted either. -/
example : (5 : ℕ) ∈ pullAll (ofPartial half) small :=
  mem_pullAll_ofPartial_of_none (by decide)
example : (5 : ℕ) ∉ pullSome (ofPartial half) small :=
  not_mem_pullSome_ofPartial_of_none (by decide)

/-- `4` decodes to `2`, which is small. -/
example : (4 : ℕ) ∈ pullSome (ofPartial half) small :=
  mem_pullSome_ofPartial.2 ⟨2, by decide, by simp [small]⟩

/-- Bool checkers lift through the decoder with `Option.any`/`Option.all`. -/
example : Decides (fun n => (half n).any (fun m => decide (m < 3)))
    (pullSome (ofPartial half) small) :=
  Decides.optionAny (fun m => by simp [small]) half

example : (half 5).all (fun m => decide (m < 3)) = true := by decide

/-- A nondeterministic step: `n ↦ n + 1` or `n ↦ 2 * n`. -/
def succOrDouble : ℕ -|> ℕ := {p | p.2 = p.1 + 1 ∨ p.2 = 2 * p.1}

/-- Both successors of `1` (`2` and `2`) are small. -/
example : (1 : ℕ) ∈ pullAll succOrDouble small := by
  intro b hb; rcases hb with h | h <;> simp_all [small]

/-- `2` can step to `3` or `4`: not small on every path, nor on any. -/
example : (2 : ℕ) ∉ pullSome succOrDouble small := by
  rintro ⟨b, hb, h | h⟩ <;> simp_all [small]

/-- Composition: step then decode. -/
example : pullSome (succOrDouble ○ ofPartial half) small =
    pullSome succOrDouble (pullSome (ofPartial half) small) := pullSome_comp

/-! ## Indexed languages -/

/-- Index `true`: even numbers; index `false`: small numbers. -/
def byFlag : Bool → Set ℕ := fun b => if b then {n | n % 2 = 0} else small

example : (8 : ℕ) ∈ eraseSome byFlag := mem_eraseSome.2 ⟨true, by simp [byFlag]⟩
example : (8 : ℕ) ∉ eraseAll byFlag := not_mem_eraseAll.2 ⟨false, by simp [byFlag, small]⟩
/-- Rejection by the existential erasure needs rejection at every index. -/
example : (5 : ℕ) ∉ eraseSome byFlag :=
  not_mem_eraseSome.2 fun b => by cases b <;> simp [byFlag, small]

example : (⟨true, 8⟩ : Σ _ : Bool, ℕ) ∈ eraseSigma byFlag := by simp [byFlag]

end Silmaril.Accept.RelExamples
