module

public import Silmaril.Formats.Dasl.Arena.Prolly.Slots.Defs
public import Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Mark.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Arena.Prolly.Surface

open Silmaril.Semantics.Prolly (Policy)

variable {Owner Kind Name Key Payload Authority : Type}

/-- Owner is the identity of an arena lifetime, not a CAS identifier.
Adapters must not recycle it while any token from that lifetime can return. -/
structure Token (Owner Kind : Type) where
  owner : Owner
  kind : Kind
  index : Nat
  deriving DecidableEq, Repr

inductive Target (Owner Kind Name : Type) where
  | local (token : Token Owner Kind)
  | backing (name : Name)

inductive Fault (Name : Type) where
  | wrongArena
  | wrongKind
  | neverAllocated
  | stale
  | query (reason : Silmaril.Formats.Dasl.Prolly.Fault (Handle Name))
  deriving DecidableEq, Repr

/-- `basis` pins the immutable local-index lineage for refinement and marking.
The resident view is the only local input to `read` and routed queries. -/
structure View (Owner Kind : Type) (basis : Indexed Name Key Payload) where
  owner : Owner
  kind : Kind
  roots : List (Handle Name)
  retained : List Nat
  resident : Sweep.Collected Name Key Payload

variable {basis : Indexed Name Key Payload}

def View.Valid (view : View Owner Kind basis) : Prop :=
  Sweep.sweep? basis view.roots view.retained = some view.resident

/-- A mount begins with a wholly resident local snapshot and no live roots.
This operation does not read or require any external names. -/
def mount (basis : Indexed Name Key Payload) (owner : Owner) (kind : Kind) : Option (View Owner Kind basis) := do
  let retained := List.range basis.blocks.size
  let resident ← Sweep.sweep? basis [] retained
  return ⟨owner, kind, [], retained, resident⟩

def View.resolve [DecidableEq Owner] [DecidableEq Kind] (view : View Owner Kind basis) :
    Target Owner Kind Name → Except (Fault Name) (Handle Name)
  | .backing name => .ok (.external name)
  | .local token =>
    if token.owner ≠ view.owner then .error .wrongArena
    else if token.kind ≠ view.kind then .error .wrongKind
    else match view.resident.slots[token.index]? with
      | none => .error .neverAllocated
      | some none => .error .stale
      | some (some _) => .ok (.local token.index)

/-- Registration is set-like. Duplicate registration adds no ownership or
pin count; unregistering removes all occurrences. -/
def View.register [DecidableEq Owner] [DecidableEq Kind] (view : View Owner Kind basis)
    (target : Target Owner Kind Name) : Except (Fault Name) (View Owner Kind basis) :=
  (view.resolve target).map fun ref => {view with roots := ref :: view.roots}

def View.unregister [DecidableEq Owner] [DecidableEq Kind] [DecidableEq Name] (view : View Owner Kind basis)
    (target : Target Owner Kind Name) : Except (Fault Name) (View Owner Kind basis) :=
  (view.resolve target).map fun ref => {view with roots := view.roots.filter (· != ref)}

def View.read (view : View Owner Kind basis) (external : Reader Name Key Payload) :
    Reader (Handle Name) Key Payload := view.resident.read external

def View.lookup [DecidableEq Owner] [DecidableEq Kind] [LinearOrder Key] (view : View Owner Kind basis)
    (external : Reader Name Key Payload) (policy : Policy Key) (fuel : Nat) (target : Target Owner Kind Name)
    (key : Key) : Except (Fault Name) (Option Payload) := do
  let ref ← view.resolve target
  ((view.read external).lookup policy fuel ref key).mapError Fault.query

/-- Apply the landed finite marker to all registered roots. The subset
check prevents a retired index being introduced by collection. `none`
is a rejected collection, not a query outcome or an authoritative miss. -/
def View.collect (view : View Owner Kind basis) : Option (View Owner Kind basis) := do
  let retained := Sweep.mark basis view.roots
  if retained.all view.retained.contains then
    let resident ← Sweep.markAndSweep? basis view.roots
    return {view with retained, resident}
  else none

/-- The authority is opaque to surface collection. A backing read adapter
may be fixed as a function of this value for snapshot query comparison. -/
structure Layer (Owner Kind Authority : Type) (basis : Indexed Name Key Payload) where
  surface : View Owner Kind basis
  authority : Authority

def Layer.collect (layer : Layer Owner Kind Authority basis) : Option (Layer Owner Kind Authority basis) :=
  layer.surface.collect.map fun surface => {layer with surface}

end Silmaril.Formats.Dasl.Arena.Prolly.Surface
