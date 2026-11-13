module

public import Silmaril.Wasm.Atlas.SpecTecR6.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Unstrip.Defs

/-!
# The SpecTec step charts at the round-7 reading (restated `$utf8` target)

`Atlas.SpecTecR6` wires (`Round6.Int.wholeStepValidR_backend`) into the atlas: Core's
step chart against SpecTec's `Step` read in `simEnv B`, on configurations whose module instances
export nothing (`NoExports`, part of `Round5.Target.BoundedSel`). reads `Step` in
`utf8Env B` (the `$utf8` erratum, `Round7.backendE`) so that module instances may export names.
The restated round-7 target is `Round7.Task.wholeStepValidREI`. This header fixes the charts it
speaks about; `Atlas.SpecTecR7.Thms` builds the transitions.

* `DomE P host c`: the domain of `Round7.Task.wholeStepValidREI`. `c` is valid, `BoundedSelE`
 , `StripInj`
  (two module instances of `c` with the same stripped form are equal), and every Core successor of
  `c` is `BoundedSelE`.
* `DomDetE P host c`: `DomE`, and Core has at most one successor at `c`.
* The SpecTec side is `SpecTecR6.readChart Round7.backendE B`.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.SpecTecR7

open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec

variable {H : Type}

/-- **The domain of the restated round-7 target** (`Round7.Task.wholeStepValidREI`): valid,
`BoundedSelE`, `StripInj`, with `BoundedSelE` Core successors. -/
def DomE (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  (∃ ts : List CValType, ConfigOk c ts) ∧ Sim.Round7.BoundedSelE c ∧ Sim.Round7.StripInj c ∧
    ∀ c₁, Step P host c c₁ → Sim.Round7.BoundedSelE c₁

/-- **The deterministic part of `DomE`**: there the forward half is exact. -/
def DomDetE (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  DomE P host c ∧ SpecTecR6.StepDet P host c

end Silmaril.Wasm.Atlas.SpecTecR7
