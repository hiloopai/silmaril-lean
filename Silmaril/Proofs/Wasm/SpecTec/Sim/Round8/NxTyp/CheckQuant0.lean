module

public import Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp.Defs

/-! # Round 8, typing across erasure without a swap set: the check, slice 0 (kernel)

One kernel computation (`decide +kernel`, kernel reduction, no native code) on the first 42 entries: every
quantifier type of every rule `Step` reaches passes `nTy tyB` over the rule's quantifiers of export-
free type.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp

open Silmaril.Wasm.SpecTec.Sim
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)

set_option maxRecDepth 100000 in
/-- Slice 0 of `nRelQuants_fixed`. -/
theorem nRelQuants_s0 : nRelQuants Round7.TypAgree.tyB ((relsOfDefs fixed).take 42) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp
