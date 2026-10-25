module

public import Silmaril.Logic.Arithmetic.Completeness.QuantifierFree

/-! Concrete arithmetic conclusions proved by the Q reconstruction functions. -/

@[expose] public section

namespace Silmaril.Logic.Arithmetic.Completeness.Examples

/-- A nested addition/multiplication expression is normalized by a Q proof tree. -/
def pythagorean : QProof [] (Formula.equal
    (.add (.mul (.numeral 3) (.numeral 3)) (.mul (.numeral 4) (.numeral 4)))
    (.numeral 25) : Sentence) :=
  proveEqual _ _ (by decide)

/-- A false multiplication equality is refuted in Q's actual calculus. -/
def sevenTimesEightNeFiftyFive : QProof [] (Formula.equal
    (.mul (.numeral 7) (.numeral 8)) (.numeral 55) : Sentence).neg :=
  refuteEqual _ _ (by decide)

/-- The existential closure retains its explicit numeral witness and derivation. -/
def squareRootNine : QProof [] (Formula.ex
    (.equal (.mul (.var 0) (.var 0)) (.numeral 9)) : Sentence) :=
  proveExistentialWitness _ (.equal _ _) 3 (by change 3 * 3 = 9; decide)

/-- Boolean reconstruction combines independent positive and negative arithmetic leaves. -/
def trueConjunction : QProof [] (Formula.conj
    (.equal (.add (.numeral 2) (.numeral 3)) (.numeral 5))
    (Formula.equal (.numeral 7) (.numeral 8)).neg : Sentence) :=
  proveQuantifierFree (.conj (.equal _ _) (.imp (.equal _ _) .bot))
    (by change 2 + 3 = 5 ∧ (7 = 8 → False); decide)

end Silmaril.Logic.Arithmetic.Completeness.Examples
