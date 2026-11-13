module

public import Silmaril.Wasm.Atlas.Games.Thms
public import Silmaril.Wasm.Atlas.Det.Thms

/-!
# The Wasm call-level atlas

`Calls.atlas P`: base chart `Core.chart P Nat`; charts indexed by `Calls.Idx`:

* `game I`: the game chart of a scalar instance, with M2 (`Games.toCore`) to Core;
* `det F`: the determinism chart against the oracle `F`, with the inclusion `Det.toCore`;
* `link S`: the composite of a linking setup's parts, with M2 + M3 (`Games.linkToCore`).

Every transition to the base is an equality transition on its class: `Games.toCore` and
`Games.linkToCore` on `diverges`-ignoring sentences, `Det.toCore` on every sentence.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.Calls

open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core (Result)
open Silmaril.Wasm.Numerics (Profile)

/-- Chart names of the call-level atlas. -/
inductive Idx where
  /-- The game chart of a scalar instance. -/
  | game (I : ScalarInstance)
  /-- The determinism chart against an oracle. -/
  | det (F : Nat → List Silmaril.Wasm.Execution.Core.Val → Result)
  /-- The composite of a static-linking setup's parts. -/
  | link (S : Linking.Setup)

/-- The charts. -/
noncomputable def chart (P : Profile) : Idx → Chart
  | .game I => Games.chart P I
  | .det F => Det.chart P F
  | .link S => Games.linkChart P S

/-- The transitions to Core. -/
noncomputable def toBase (P : Profile) : (i : Idx) → Transition (chart P i) (Core.chart P Nat)
  | .game I => Games.toCore P I
  | .det F => Det.toCore P F
  | .link S => Games.linkToCore P S

/-- **The Wasm call-level atlas** at profile `P`. -/
noncomputable def atlas (P : Profile) : ChartAtlas where
  base := Core.chart P Nat
  ι := Idx
  chart := chart P
  toBase := toBase P

end Silmaril.Wasm.Atlas.Calls
