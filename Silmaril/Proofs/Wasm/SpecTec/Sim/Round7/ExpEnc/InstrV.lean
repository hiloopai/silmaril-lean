module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.ExpEnc.Types

/-!
# Round 7, encoder lemma: `Equiv.instrV` is `EXPORTS`-free
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm

@[simp] theorem efB_instrV (i : Instr) : efB (Silmaril.SpecTec.Equiv.instrV i) = true := by
  cases i
  all_goals first | rfl | exact efB_heapType _ | efb_leaf

end Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc
