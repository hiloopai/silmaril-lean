module

public import Silmaril.Wasm.Atlas.Defs
public import Silmaril.Wasm.Behaviour.Semantics.V3

/-!
# The Core chart

The base chart of the Wasm atlas: silmaril-lean's Core 3.0 reduction `Step P host` at an
arbitrary profile `P`. Points are a store and a host relation; calls are function addresses
with arguments; the observations of a call are `behaviours P host s a vs` (finite results and
may-divergence). The domain is everything: Core is the reference chart.

* `Core.chart P H`: the Core chart over host states `H`.
* `Core.StepLE P' P H`: every step at `P'` is a step at `P`, for every host (profile refinement,
  the host-generic form of `Det.Core.ProfileLE`); `Core.profileUniv`/`Core.profileExist` (in
  `Thms`) are the resulting inclusion transitions of the profile family.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- Core points: a store and a host relation. -/
abbrev Pt (H : Type) : Type := Store H × HostSemantics H

/-- Core calls: a function address and its arguments. -/
abbrev Call : Type := Nat × List Val

/-- The observations of a call: silmaril's `behaviours`. -/
def obs (P : Profile) {H : Type} (x : Pt H) (c : Call) : Set (Behaviour Val) :=
  behaviours P x.2 x.1 c.1 c.2

/-- **The Core chart** at profile `P`: domain everything. -/
def chart (P : Profile) (H : Type) : Chart :=
  BChart (Pt H) Call (Behaviour Val) (fun _ => True) (obs P)

/-- Profile refinement: every step at `P'` is a step at `P`, for every host. -/
def StepLE (P' P : Profile) (H : Type) : Prop :=
  ∀ (host : HostSemantics H) (c c' : Config H), Step P' host c c' → Step P host c c'

end Silmaril.Wasm.Atlas.Core
