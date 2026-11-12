module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckBase

/-!
# Round 7, the whole-evaluator erasure: `$blocktype_` and `Step_read` join the checked part

`gdB`, `grB`: `gdE` with `$blocktype_`, and `grE` with `Step_read`. Once `$blocktype_`'s primitive
is known to commute with erasure (`Round7.EraseAll.call_blocktype_erase`), the only reason left to
exclude the two is gone. One kernel computation (`decide +kernel`): the top-level definitions that
bind `$blocktype_` or `Step_read` pass the check at `grB`, `gdB` (`xBNamedOk_fixed`). The others
pass it at `grE`, `gdE` (`xScriptOk_fixed`), hence at `grB`, `gdB` by monotonicity.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- `gdE` with `$blocktype_`. -/
def gdB (x : String) : Bool := gdE x || x == "blocktype_"

/-- `grE` with `Step_read`. -/
def grB (x : String) : Bool := grE x || x == "Step_read"

/-- The top-level definition binds `$blocktype_` or `Step_read`. -/
def xBNamed (d : Def) : Bool :=
  (defsOfDef d).any (fun p => p.1 == "blocktype_") || (relsOfDef d).any (fun p => p.1 == "Step_read")

set_option maxRecDepth 100000 in
/-- **The definitions of `$blocktype_` and `Step_read` pass the check at `grB`, `gdB`.** -/
theorem xBNamedOk_fixed :
    Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed.all (fun d => !xBNamed d || xDefOk grB gdB d) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
