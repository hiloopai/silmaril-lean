module

public import Silmaril.Cerberus.Core.Dynamics.Defs

/-! # Locally forced executions of the Core machine

Every edge is an actual Core transition together with uniqueness of its label
and successor at that particular state. Core choices elsewhere remain unrestricted.
-/

@[expose] public section

namespace Silmaril.Cerberus.Core.Forced

open Silmaril.Cerberus.Core.Dynamics

/-- A finite Core execution whose visited live states each have one outgoing
label and successor. The endpoint need not be terminal. -/
inductive Reaches (file : Program) (labels : Labels) : State → State → Prop where
  | refl {state : State} : Reaches file labels state state
  | cons {source next target : State} {action : Label}
      (edge : Step file labels source action next)
      (unique : ∀ otherAction otherNext, Step file labels source otherAction otherNext →
        otherAction = action ∧ otherNext = next)
      (tail : Reaches file labels next target) : Reaches file labels source target

end Silmaril.Cerberus.Core.Forced
