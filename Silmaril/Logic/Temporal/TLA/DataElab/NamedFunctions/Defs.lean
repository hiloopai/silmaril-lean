module

public import Silmaril.Logic.Temporal.TLA.Data.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.Defs

/-! # Named predecessor functions over finite integer intervals

A semantic fragment of the named function definition in *Specifying Systems*
§§5.5, 6.3 and 16.1.7, including the local function in WriteThroughCache.vmem.
See docs/projects/tla-named-functions.md.
-/

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions

open Data Data.Tagged

universe u

/-- A successor body either returns the preceding value or updates one of its keys. -/
inductive Step where
  | keep
  | write (key value : Value.{u})

noncomputable def Step.apply (policy : Unspecified.{u}) (previous : Value.{u}) :
    Step.{u} → Value.{u}
  | .keep => previous
  | .write key value => previous.update policy key value

/-- A zero case and one successor body for each positive key of the declared interval. -/
structure Definition where
  base : Value.{u}
  steps : List Step.{u}

namespace Definition

noncomputable def domain (d : Definition.{u}) : SetData.{u} :=
  .intRange 0 d.steps.length

/-- Embed an indexed body into the tagged constructor. Only keys in the
declared interval contribute pairs. -/
noncomputable def graphOf (d : Definition.{u})
    (body : (i : Nat) → i ≤ d.steps.length → Value.{u}) : Graph.{u} :=
  .ofFn d.domain fun key =>
    let i := (key.asInt.getD 0).toNat
    if h : i ≤ d.steps.length then body i h else d.base

/-- The anonymous constructor on the right of equation (6.3), with the
candidate value in scope for self-application. -/
noncomputable def rhs (d : Definition.{u}) (policy : Unspecified.{u})
    (candidate : Value.{u}) : Graph.{u} :=
  d.graphOf fun
    | 0, _ => d.base
    | i + 1, hi => (d.steps[i]'(by omega)).apply policy (candidate.apply policy (.integer i))

def FixedPoint (d : Definition.{u}) (policy : Unspecified.{u}) (candidate : Value.{u}) : Prop :=
  candidate = .function (d.rhs policy candidate)

/-- At a positive index the predecessor is in the declared domain and strictly smaller. -/
noncomputable def eval (d : Definition.{u}) (policy : Unspecified.{u}) :
    (i : Nat) → i ≤ d.steps.length → Value.{u}
  | 0, _ => d.base
  | i + 1, hi => (d.steps[i]'(by omega)).apply policy (d.eval policy i (by omega))
termination_by i => i
decreasing_by exact Nat.lt_succ_self _

noncomputable def graph (d : Definition.{u}) (policy : Unspecified.{u}) : Graph.{u} :=
  d.graphOf (d.eval policy)

end Definition

/-- The branch selected by the second component of a WriteThroughCache queue entry. -/
noncomputable def vmemStep (policy : Unspecified.{u}) (entry : Value.{u}) : Step.{u} :=
  open Classical in
  let request := entry.apply policy (.integer 2)
  if request.apply policy (.string "op") = .string "Rd" then .keep
  else .write (request.apply policy (.string "adr")) (request.apply policy (.string "val"))

/-- Translate the pinned local definition with `memQ = Value.tuple entries`. -/
noncomputable def vmemDefinition (policy : Unspecified.{u}) (wmem : Value.{u})
    (entries : List Value.{u}) : Definition.{u} :=
  ⟨wmem, entries.map (vmemStep policy)⟩

/-- The `IN` expression of the pinned LET, with the local graph bound to `f`. -/
noncomputable def vmem (policy : Unspecified.{u}) (wmem : Value.{u})
    (entries : List Value.{u}) : Value.{u} :=
  (Value.function ((vmemDefinition policy wmem entries).graph policy)).apply policy
    (.integer entries.length)

end Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions
