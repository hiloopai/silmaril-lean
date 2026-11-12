module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant.Defs

/-! # Round 7, REH route 2: the aliases of `sigX` unfold within seven steps (kernel) -/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant

open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped (sigX)

set_option maxRecDepth 100000 in
/-- **The aliases of `sigX` unfold within seven steps.** -/
theorem aliasFuelOk_sigX : aliasFuelOk sigX = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant
