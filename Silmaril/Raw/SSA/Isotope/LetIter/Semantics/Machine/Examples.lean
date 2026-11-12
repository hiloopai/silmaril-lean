module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Machine.Divergence

/-! # State order, lexical scope, and divergence in the continuation machine -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.Semantics.Machine.Examples

open LocallyNameless

/-- An atomic instruction records its identifier and preserves its input value. -/
def emit (f : Nat) (a : Value Unit) (s : List Nat) (b : Value Unit) (s' : List Nat) : Prop :=
  b = a ∧ s' = s ++ [f]

def free : FreeEnv Empty Unit := Empty.elim
def bound : BoundEnv Unit 0 := Fin.elim0

/-- The left operand's atomic effect precedes the right operand's effect. -/
theorem pair_effect_order :
    Steps emit free
      (.eval bound (.pair (.op 1 .unit) (.op 2 .unit)) .halt [])
      (.ret (.pair .unit .unit) .halt [1, 2]) :=
  eval_steps (.pair (.op .unit ⟨rfl, rfl⟩) (.op .unit ⟨rfl, rfl⟩)) .halt

/-- An inner let does not overwrite the environment saved for the right operand. -/
theorem lexical_scope_restored :
    Steps emit free
      (.eval bound (.let₁ .unit
        (.pair (.let₁ (.pair .unit .unit) (.bv 0)) (.bv 0))) .halt [])
      (.ret (.pair (.pair .unit .unit) .unit) .halt []) :=
  eval_steps (.let₁ .unit (.pair (.let₁ (.pair .unit .unit) .bv) .bv)) .halt

/-- The initializer effect runs once, followed by the exiting body effect. -/
theorem initializer_effect_once :
    Steps emit free
      (.eval bound (.iter (.op 0 .unit) (.inl (.op 1 (.bv 0)))) .halt [])
      (.ret .unit .halt [0, 1]) :=
  eval_steps (.iter (.op .unit ⟨rfl, rfl⟩)
    (.done (.inl (.op .bv ⟨rfl, rfl⟩)))) .halt

/-- A continuation backedge yields infinitely many genuine machine steps. -/
theorem continue_forever :
    Diverges emit free
      (.eval bound (.iter .unit (.inr (.bv 0))) .halt []) :=
  source_diverges (Eval.iter_continue_diverges bound [] Eval.unit) .halt

/-- The coinductive loop witness yields a concrete infinite path of single
machine transitions, rather than a sequence of big-step evaluations. -/
theorem continue_forever_trace :
    Silmaril.InfiniteTrace (Step emit free)
      (.eval bound (.iter .unit (.inr (.bv 0))) .halt []) :=
  Diverges.iff_infiniteTrace.mp continue_forever

/-- Empty elimination reaches a stuck continuation rather than a trap or an infinite run. -/
theorem abort_reaches_stuck :
    Steps emit free (.eval bound (.abort .unit) .halt []) (.ret .unit (.abort .halt) []) ∧
      (∀ d, ¬ Step emit free (.ret .unit (.abort .halt) []) d) ∧
      ¬ Diverges emit free (.ret .unit (.abort .halt) []) := by
  exact ⟨.cons (.abort ..) (Step.unit ..).steps, abort_stuck ..⟩

end Silmaril.Isotope.LetIter.Semantics.Machine.Examples
