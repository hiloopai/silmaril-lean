module

public import Silmaril.Wasm.SpecTec.Sim20.XSwap.Defs
public import Silmaril.Wasm.SpecTec.Sim20.StoreFix.Defs

/-!
# the 2.0 types pass the re-encoding check

Two kernel computations (`decide +kernel`, no native evaluation) on the corrected 2.0 script:

* `xTypMap20`: every type `Step` reaches (`tyC20`) has checked instances. The one record type with
  an `EXPORTS` field, `moduleinst`, declares it at `exportinst*` without premises and has no
  argument patterns.
* `xRelQuants20`: every quantifier type of a rule of `Step`, `Step_read` and `Step_pure` is
  checked.
* `relsNoParams20`: those three relations have no parameters.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.Typ

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-- **Every type `Step` reaches is checked.** -/
theorem xTypMap20 : xTypMap tyC20 (typsOfDefs Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20) = true := by
  decide +kernel

/-- **Every quantifier type of a rule of `Step`, `Step_read` or `Step_pure` is checked.** -/
theorem xRelQuants20 :
    xRelQuants tyC20 (relsOfDefs Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20) = true := by
  decide +kernel

/-- **`Step`, `Step_read` and `Step_pure` have no parameters.** -/
theorem relsNoParams20 : (relsOfDefs Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20).all
    (fun p => !EraseAll.gr20 p.1 || p.2.1.isEmpty) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim20.XSwap.Typ
