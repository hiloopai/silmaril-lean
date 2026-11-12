module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.RefOkV.RefOk

/-!
# Round 6: `RefOkBV` from the interpreter half

`refOkBV_of_agree`: `Round6.RefOkB.RefOkBV env` follows from `Agree env` (the interpreter reads
SpecTec's `Ref_ok` as `RefOkS`) and the Core half `refOkS_iff`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

/-- **`RefOkBV` from the interpreter half**: the Core half (`refOkS_iff`) is proved. -/
theorem refOkBV_of_agree {env : Env} (A : Agree env) : RefOkB.RefOkBV env where
  refOk hn s rt hs hS hb hok O r := (A.refOk hn s rt hs hS hb hok O r).trans (refOkS_iff hS hok)

end Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV
