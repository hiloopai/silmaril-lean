module

public import Silmaril.Logic.ArithmeticToSecondOrder.Category
public import Silmaril.Logic.ArithmeticToSecondOrder.Semantics

@[expose] public section

namespace Silmaril.Logic.ArithmeticToSecondOrder

open Arithmetic

/-- The base arithmetic theorem compiles to precisely the target arithmetic axiom. -/
theorem zeroAddZero_compiler :
    paToSOA paZeroAddZero = .axiom (.base (.axPl0 .zero)) := rfl

/-- The non-basic seventh Q axiom passes through PA induction and the full
ND-to-Hilbert compiler, including disjunction and existential proof rules. -/
def soaPredecessorZero : SecondOrderArithmetic.Proof .Z2Full
    (sentence (predecessor (.zero : Term 0))) := paToSOA (paPredecessor .zero)

/-- Equality elimination is exercised with an arithmetic equality as premise. -/
def equalityElimination : PAProof [] (.equal .zero .zero : Sentence) :=
  .eqElim (.equal (.var 0) .zero)
    (.ax (.basic (.addZero .zero))) (.ax (.basic (.addZero .zero)))

def soaEqualityElimination : SecondOrderArithmetic.Proof .Z2Full
    (sentence (.equal .zero .zero)) := paToSOA equalityElimination

/-- A universal proof introduces a scoped eigenvariable and then substitutes zero. -/
def universalElimination : PAProof [] (.equal .zero .zero : Sentence) :=
  .allElim (.allIntro (.eqRefl (.var 0))) .zero

def soaUniversalElimination : SecondOrderArithmetic.Proof .Z2Full
    (sentence (.equal .zero .zero)) := paToSOA universalElimination

/-- Existential elimination removes its eigenvariable from the conclusion. -/
def existentialElimination : PAProof [] (.equal .zero .zero : Sentence) :=
  .exElim (φ := .equal (.var 0) .zero) (.exIntro .zero (.eqRefl .zero)) (.eqRefl .zero)

def soaExistentialElimination : SecondOrderArithmetic.Proof .Z2Full
    (sentence (.equal .zero .zero)) := paToSOA existentialElimination

/-- Every ordinary arithmetic induction instance has a target derivation. -/
def soaInduction (p : Formula 1) : SecondOrderArithmetic.Proof .Z2Full
    (sentence (inductionSchema p)) := paToSOA (.ax (.induction p))

/-- The disjunction tag distinguishes the collision in the implication-only encoding. -/
theorem disjunction_bot_distinct :
    sentence (.disj (.equal .zero .zero) .bot) ≠ sentence (.imp .bot .bot) := by
  decide

end Silmaril.Logic.ArithmeticToSecondOrder
