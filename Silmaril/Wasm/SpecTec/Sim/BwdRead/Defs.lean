module

public import Silmaril.Wasm.SpecTec.Sim.Defs

/-!
# SpecTec ↔ Core 3.0, round 3, track bwd-read: definitions

The track proves backward lemmas (SpecTec → Core) for `Step_read` rules among 23–102, for every
`B` that leaves the state accessors to their clauses (`NoAcc`), and so for the concrete
`Prims.builtins`. `readDone` lists the rules dispatched; `Integrate.RemainingW.read` excludes
them.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.BwdRead

open Silmaril.SpecTec.Sem

/-- `B` interprets none of the state accessors: their single clauses decide them. -/
structure NoAcc (B : Builtins) : Prop where
  /-- `$local`. -/
  local_ : ∀ ws, B.call "local" ws = none
  /-- `$global`. -/
  global : ∀ ws, B.call "global" ws = none
  /-- `$table`. -/
  table : ∀ ws, B.call "table" ws = none
  /-- `$mem`. -/
  mem : ∀ ws, B.call "mem" ws = none
  /-- `$elem`. -/
  elem : ∀ ws, B.call "elem" ws = none
  /-- `$data`. -/
  data : ∀ ws, B.call "data" ws = none

/-- The `Step_read` rules this track dispatches: `local.get` (23), `global.get` (24),
`table.get-oob` (25), `table.get-val` (26), `table.fill-oob` (28), `memory.fill-oob` (53), and
the aggregate null traps `struct.get-null` (70), `array.get-null` (77), `array.len-null` (80),
`array.fill-null` (82), `array.init_elem-null` (93), `array.init_data-null` (98). -/
def readDone : List Nat := [23, 24, 25, 26, 28, 53, 70, 77, 80, 82, 93, 98]

end Silmaril.Wasm.SpecTec.Sim.BwdRead
