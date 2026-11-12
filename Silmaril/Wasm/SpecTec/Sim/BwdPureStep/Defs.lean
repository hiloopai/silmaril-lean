module

public import Silmaril.Wasm.SpecTec.Sim.Bwd.Defs

/-!
# SpecTec ↔ Core 3.0, round 3, track bwd-pure-step: the rules it inverts

The `Step_pure` and `Step` rule indices this track proves backward lemmas for, at every
`simEnv B` (`Silmaril.Wasm.SpecTec.Sim.BwdPureStep.Thms`). `Integrate.RemainingW` excludes them.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.BwdPureStep

/-- The `Step_pure` rules inverted here: the reference rules 31–40, 42–45 and `array.new` (41). -/
def pureDone : List Nat := [31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45]

/-- The `Step` rules inverted here: `local.set` (11), `global.set` (12), `table.set` (13, 14),
`elem.drop` (17), `store-num-oob` (18), `store-pack-oob` (20), `data.drop` (28),
`struct.set-null` (30), `array.set-null` (33), `array.set-oob` (34). -/
def stepDone : List Nat := [11, 12, 13, 14, 17, 18, 20, 28, 30, 33, 34]

end Silmaril.Wasm.SpecTec.Sim.BwdPureStep
