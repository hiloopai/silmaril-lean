module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Behaviour
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Machine.Examples

/-!
# The three outcomes a LetIter configuration can show

`Silmaril/Isotope/LetIter/Semantics/Behaviour.lean` packages LetIter's CK
machine as a `Machine.Behaviour.Semantics` whose outcomes are `.returned`,
`.undefined` and `.diverges`. This file exhibits one program of each kind, over
the recording instruction relation `Machine.Examples.emit` of
`Silmaril/Isotope/LetIter/Semantics/Machine/Examples.lean`, so that the
packaging is visibly inhabited at every outcome rather than only at none.

* `beh_pair` — a pair of primitive calls returns `((), ())` with the effect log
  `[1, 2]`, through `beh_returned_iff`, which is an `iff`, so the big-step
  derivation is all that is needed.
* `beh_iter_diverges` — a loop that always takes its back edge diverges,
  through `beh_diverges_of_source`.
* `beh_abort_undefined` — empty elimination reaches a configuration with no
  successor, which this packaging reports as `.undefined`, and
  `not_safe_abort` reads that back as `¬ Safe`.

`emit` is deterministic (`emit_deterministic`), so by `beh_unique` each of the
three is the *only* behaviour of its configuration: the outcomes are not merely
available, they are forced.
-/

@[expose] public section

namespace Silmaril.Isotope.LetIter.Semantics.Machine.BehaviourExamples

open LocallyNameless
open Silmaril.Isotope.LetIter.Semantics.Machine.Examples (emit free bound)
open Relation

/-- **The recording instruction relation is deterministic**: it fixes both the
returned value and the successor state. -/
theorem emit_deterministic : InstrDeterministic emit := by
  rintro f a s b s' c s'' ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  exact ⟨rfl, rfl⟩

/-! ## Returning -/

/-- **A returning behaviour.** The pair `(op 1 (), op 2 ())` evaluates to
`((), ())` leaving the effect log `[1, 2]`, so the packaged semantics shows
`.returned`. The proof is the big-step derivation and nothing else, because
`beh_returned_iff` is an `iff`. -/
theorem beh_pair :
    (sem emit free).Beh (entryConfig bound (.pair (.op 1 .unit) (.op 2 .unit)) [])
      (.returned (.pair .unit .unit, [1, 2])) :=
  beh_returned_iff.mpr (.pair (.op .unit ⟨rfl, rfl⟩) (.op .unit ⟨rfl, rfl⟩))

/-- Returning is the *only* behaviour of that configuration, because `emit` is
deterministic. -/
theorem beh_pair_unique {o : Silmaril.Machine.Behaviour.Outcome (Value Unit × List Nat) Empty Empty}
    (h : (sem emit free).Beh (entryConfig bound (.pair (.op 1 .unit) (.op 2 .unit)) []) o) :
    o = .returned (.pair .unit .unit, [1, 2]) :=
  beh_unique emit_deterministic h beh_pair

/-! ## Diverging -/

/-- **A diverging behaviour.** `iter () (inr (bv 0))` always takes its back
edge, so the machine runs forever and the packaged semantics shows
`.diverges`. -/
theorem beh_iter_diverges :
    (sem emit free).Beh (entryConfig bound (.iter .unit (.inr (.bv 0))) []) .diverges :=
  beh_diverges_of_source (Eval.iter_continue_diverges bound [] Eval.unit) .halt

/-! ## Undefined -/

/-- The machine reaches the stuck configuration `.ret () (.abort .halt) []`:
`Kont.abort` has no consuming rule. -/
theorem abort_stuck_reach :
    ReflTransGen (Step emit free) (entryConfig bound (.abort .unit) [])
        (.ret .unit (.abort .halt) []) ∧
      Stuck emit free (.ret .unit (.abort .halt) []) :=
  ⟨steps_iff_reflTransGen.mp (.cons (.abort ..) (Step.unit ..).steps),
    ⟨rfl, (abort_stuck (instr := emit) (free := free) .unit .halt []).1⟩⟩

/-- **An undefined behaviour.** Empty elimination evaluates its operand and then
has nowhere to go; this packaging reports a configuration with no successor that
has not halted as `.undefined`, exactly as `RTL` reports its stuck states. -/
theorem beh_abort_undefined :
    (sem emit free).Beh (entryConfig bound (.abort .unit) []) .undefined :=
  beh_undefined_iff.mpr ⟨_, abort_stuck_reach.1, abort_stuck_reach.2⟩

/-- **Empty elimination is not safe.** `Safe` is "no reachable configuration is
stuck", and this one reaches one. This is the clause that gives
`safe_iff_no_stuck` content: were `Safe` vacuously true, it would be useless as
the side condition of a refinement. -/
theorem not_safe_abort : ¬ (sem emit free).Safe (entryConfig bound (.abort .unit) []) :=
  fun h => h beh_abort_undefined

end Silmaril.Isotope.LetIter.Semantics.Machine.BehaviourExamples
