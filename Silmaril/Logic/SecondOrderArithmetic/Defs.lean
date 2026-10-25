module

public import Silmaril.Logic.SecondOrderArithmetic.Systems
public import Silmaril.Logic.SecondOrderArithmetic.Category
public import Silmaril.Logic.SecondOrderArithmetic.Henkin

/-! Second-order arithmetic has independent finite syntax, Hilbert proof trees
and two-sorted semantics. `WKL0Sep` is the Σ⁰₁-separation presentation; its
equivalence to a tree formulation of weak König's lemma is a separate result.
`HenkinStructure` permits arbitrary number and set carriers; `omegaStructure`
fixes the numbers to ℕ, and `fullStandard` uses all subsets of ℕ. -/

@[expose] public section

namespace Silmaril.Logic.SecondOrderArithmetic

/-- A structure validates each independent axiom instance in every environment. -/
def ValidAxioms {N : Type} [DecidableEq N] (S : Subsystem) (M : HenkinStructure) : Prop :=
  ∀ {p : Formula N}, Axiom S p → ∀ ρ : M.Env N, p.henkinEval M ρ

end Silmaril.Logic.SecondOrderArithmetic
