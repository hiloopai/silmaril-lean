module

public import Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp.Defs

/-! # Round 8, typing across erasure without a swap set: the check, slice 2 (kernel)

One kernel computation (`decide +kernel`, kernel reduction, no native code) on the remaining entries: every type
over `tyB` passes `nInsts tyB`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp

open Silmaril.Wasm.SpecTec.Sim
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)

set_option maxRecDepth 100000 in
/-- Slice 2 of `nTypMap_fixed`. -/
theorem nTypMap_s2 : nTypMap Round7.TypAgree.tyB ((typsOfDefs fixed).drop 140) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp
