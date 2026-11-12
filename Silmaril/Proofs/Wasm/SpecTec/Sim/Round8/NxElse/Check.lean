module

public import Silmaril.Wasm.SpecTec.Sim.Round8.NxElse.Defs

/-!
# Round 8, `otherwise` across erasure: the check on left-hand sides

One kernel computation (`decide +kernel`, kernel reduction, no native code): every rule of a `grE` relation with
an `otherwise` premise has a conclusion `lhs ~> rhs`, at every alternative, whose left-hand side
reads only quantifiers of export-free type. `CheckNames` lists the seven such rules.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxElse

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7

set_option maxRecDepth 100000 in
/-- **Every `otherwise` rule of a `grE` relation has an export-free left-hand side.** -/
theorem elseLhs_fixed : elseLhs (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round8.NxElse
