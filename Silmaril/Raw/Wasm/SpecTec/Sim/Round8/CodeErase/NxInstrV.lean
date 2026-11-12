module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.CodeErase.NxTypes

/-!
# Round 8 (copy of round 7 for `CODE` fields), encoder lemma: `Equiv.instrV` is free of `CODE` records

Copied mechanically from round 7 (export erasure) with `EXPORTS` read as `CODE` and
`eraseV` as `eraseC`; where the prose below speaks of export lists, module records or the swap
set `QC c`, it describes the original. Here every value is in the swap set (`fun _ => True`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm

@[simp] theorem ncB_instrV (i : Instr) : ncB (Silmaril.SpecTec.Equiv.instrV i) = true := by
  cases i
  all_goals first | rfl | exact ncB_heapType _ | nxb_leaf

end Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap
