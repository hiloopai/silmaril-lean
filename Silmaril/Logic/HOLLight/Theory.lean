module

public import Silmaril.Logic.HOLLight.Logic

@[expose] public section

/-!
# Finite HOL theories

Object axioms are syntax, not Lean axioms. Object-axiom free type and term variables
are schematic: its interpretation must hold at every valuation.
-/

namespace Silmaril.Logic.HOLLight

abbrev Theory := List Tm

def Theory.WellFormed (sig : Signature) (theory : Theory) : Prop :=
  ∀ p ∈ theory, HasType sig [] p .bool

def initialSignature : Signature := ⟨[], []⟩

/-- The eta, selection, and infinity axioms of classical HOL. -/
def classicalTheory : Theory :=
  [Tm.eta (.var 0) (.var 1) (.fvar 0 (.arr (.var 0) (.var 1))),
   Tm.selection (.var 0) (.fvar 0 (.arr (.var 0) .bool)) (.fvar 1 (.var 0)),
   Tm.infinity]

end Silmaril.Logic.HOLLight
