module

public import Silmaril.Semantics.Accept.Bounded.Thms

/-! # Bounded domains: worked examples and regression tests

A toy document format (`Doc`) with a nesting depth and a size. The specification (an even
number of atoms) has a total checker, *and* a checker that also enforces a depth bound, the
shape of a one-shot interface with a bounded buffer. Both are stated; neither is privileged.
Every `example` is checked when the library builds.
-/

@[expose] public section

namespace Silmaril.Accept.BoundedExamples

open Silmaril.Accept

/-- A toy document format. -/
inductive Doc where
  | atom
  | wrap (d : Doc)
  | pair (l r : Doc)

namespace Doc

/-- Nesting depth. -/
def depth : Doc → ℕ
  | atom => 0
  | wrap d => d.depth + 1
  | pair l r => max l.depth r.depth + 1

/-- Number of atoms. -/
def atoms : Doc → ℕ
  | atom => 1
  | wrap d => d.atoms
  | pair l r => l.atoms + r.atoms

/-- Size: number of constructors. -/
def size : Doc → ℕ
  | atom => 1
  | wrap d => d.size + 1
  | pair l r => l.size + r.size + 1

end Doc

/-- The specification: an even number of atoms. -/
def evenAtoms : Set Doc := {d | d.atoms % 2 = 0}

/-- A total checker, complete on every document. -/
def checkAll (d : Doc) : Bool := decide (d.atoms % 2 = 0)

theorem checkAll_decides : Decides checkAll evenAtoms := fun _ => decide_eq_true_iff

/-- A checker that also rejects documents deeper than `k`. -/
def checkDepth (k : ℕ) (d : Doc) : Bool := decide (d.depth ≤ k) && checkAll d

/-- It decides the depth-bounded subset of the specification … -/
theorem checkDepth_decides (k : ℕ) : Decides (checkDepth k) (evenAtoms ∩ within Doc.depth k) :=
  (checkAll_decides.decidesOn _).andBound fun _ => decide_eq_true_iff

/-- … so it decides the specification on the bounded domain, and on every smaller one … -/
example (k : ℕ) : DecidesOn (within Doc.depth k) (checkDepth k) evenAtoms :=
  (decides_inter_iff.1 (checkDepth_decides k)).1

example : DecidesOn (within Doc.depth 2) (checkDepth 5) evenAtoms :=
  ((decides_inter_iff.1 (checkDepth_decides 5)).1).within_mono (by decide)

/-- … but it is not complete outside the bound: a deep document with two atoms. -/
example : (Doc.wrap (.wrap (.pair .atom .atom))) ∈ evenAtoms ∧
    checkDepth 1 (Doc.wrap (.wrap (.pair .atom .atom))) = false := by
  refine ⟨?_, ?_⟩
  · show (2 : ℕ) % 2 = 0; rfl
  · rfl

/-- The total checker is complete on every bounded domain, hence everywhere; bounded
completeness was not forced. -/
example : Complete checkAll evenAtoms :=
  complete_of_forall_within (μ := Doc.depth) fun _ => checkAll_decides.complete.completeOn _

/-- A combined size-and-depth bound is a bound in the product order. -/
example : within (fun d : Doc => (d.size, d.depth)) (10, 3) =
    within Doc.size 10 ∩ within Doc.depth 3 := within_prod

/-! ## Length-bounded subsets -/

/-- Lists of length at most `3` with all entries below `10`. -/
example : [1, 2, 3] ∈ {l : List ℕ | ∀ x ∈ l, x < 10} ∩ within List.length 3 := by
  refine ⟨?_, ?_⟩ <;> simp

example : upTo List.length 3 {l : List ℕ | ∀ x ∈ l, x < 10} =
    {l : List ℕ | ∀ x ∈ l, x < 10} ∩ within List.length 3 := upTo_eq_inter_within

end Silmaril.Accept.BoundedExamples
