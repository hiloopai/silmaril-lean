module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Swap.NxTypes

/-!
# Round 7, encoder lemma: `Equiv.instrV` is free of `EXPORTS` records
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm

@[simp] theorem nxB_instrV (i : Instr) : nxB (Silmaril.SpecTec.Equiv.instrV i) = true := by
  cases i
  all_goals first | rfl | exact nxB_heapType _ | nxb_leaf

end Silmaril.Wasm.SpecTec.Sim.Round7.Swap
