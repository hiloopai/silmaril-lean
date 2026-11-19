module

public import Silmaril.Wasm.Execution.Core.Intrinsic.Defs
public import Silmaril.Wasm.Behaviour.Semantics.V3.Defs

@[expose] public section

/-! # Observing typed Core instruction sequences

The observer is Core's actual `behavioursOf`, after exact erasure and with a
fixed host-free deterministic profile. This is not equality of syntax, store
identity across instances, or component contextual equivalence.
-/

namespace Silmaril.Wasm.Execution.Core.Intrinsic

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type} {context : Context} {world : World H context}
  {locals input middle output : List IntType}

abbrev Oracle := GrowKind → Nat → Nat → Nat → Bool

def Code.observe (oracle : Oracle) (code : Code locals input output)
    (frame : LocalFrame world locals) (stack : Values input) : Set (Behaviour Val) :=
  behavioursOf (.deterministic oracle) (fun _ _ _ _ => False) (State.mk frame (.run stack code)).erase

/-- Equality of observations from every frame and operand stack at the common
indices; both invocations use the same world, not an equality across worlds. -/
def Code.ObsEq (oracle : Oracle) (left right : Code locals input output) : Prop :=
  ∀ {H : Type} {context : Context} {world : World H context}
    (frame : LocalFrame world locals) (stack : Values input),
    left.observe oracle frame stack = right.observe oracle frame stack

def Code.obsSetoid (oracle : Oracle) (locals input output : List IntType) :
    Setoid (Code locals input output) where
  r := Code.ObsEq oracle
  iseqv := by
    constructor
    · intro code H context world frame stack
      rfl
    · intro left right h H context world frame stack
      exact (h frame stack).symm
    · intro first second third h₁ h₂ H context world frame stack
      exact (h₁ frame stack).trans (h₂ frame stack)

abbrev Code.Observations (oracle : Oracle) (locals input output : List IntType) :=
  Quotient (Code.obsSetoid oracle locals input output)

/-- A sufficient condition for a context step to reach its continuation. -/
def Op.Nontrapping (op : Op locals input middle) : Prop :=
  ∀ (frame : Values locals) (stack : Values input), ∃ next, op.eval frame stack = .next next

def Code.Nontrapping : {input output : List IntType} → Code locals input output → Prop
  | _, _, .done => True
  | _, _, .seq op tail => op.Nontrapping ∧ tail.Nontrapping

end Silmaril.Wasm.Execution.Core.Intrinsic
