module

public import Silmaril.Logic.Arithmetic.Completeness.FiniteBounds

/-! Open-variable finite-bound theorems with actual Q derivation trees. -/

@[expose] public section

namespace Silmaril.Logic.Arithmetic.Completeness.Examples

/-- Q proves the concrete finite case split under its arithmetic order graph. -/
def belowThreeCases : QProof [] (Formula.all
    (.imp (below (.var 0) (.numeral 3)) (enumeration 0 3 (.var 0))) : Sentence) :=
  .allIntro (belowFinite 3 (.var 0))

/-- The same finite theorem works for a non-strict existential arithmetic bound. -/
def atMostTwoCases : QProof [] (Formula.all
    (.imp (atMost (.var 0) (.numeral 2)) (enumeration 0 2 (.var 0))) : Sentence) :=
  .allIntro (finiteBound 2 (.var 0))

/-- Q bounds the first summand without assuming universal addition commutativity. -/
def firstSummandCases : QProof [] (Formula.all (Formula.all
    (.imp (.equal (.add (.var 1) (.var 0)) (.numeral 4))
      (enumeration 0 4 (.var 1)))) : Sentence) :=
  .allIntro (.allIntro (finiteFirstSumBound 4 (.var 1) (.var 0)))

end Silmaril.Logic.Arithmetic.Completeness.Examples
