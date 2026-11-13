module

public import Silmaril.Wasm.SpecTec.Sim20.XSwap.Defs
public import Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.Defs

/-!
# the 1.0 types pass the re-encoding check

`CheckTyp` for the 1.0 script with both errata (`Utf8Fix.fixedU10`): every type `Step` reaches is
checked (`xTypMap10`), every quantifier type of `Step`, `Step_read`, `Step_pure` is checked
(`xRelQuants10`), and those relations have no parameters (`relsNoParams10`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.Typ10

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-- **Every type `Step` reaches is checked.** -/
theorem xTypMap10 : xTypMap tyC10 (typsOfDefs Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.fixedU10) = true := by
  decide +kernel

/-- **Every quantifier type of a rule of `Step`, `Step_read` or `Step_pure` is checked.** -/
theorem xRelQuants10 :
    xRelQuants tyC10 (relsOfDefs Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.fixedU10) = true := by
  decide +kernel

/-- **`Step`, `Step_read` and `Step_pure` have no parameters.** -/
theorem relsNoParams10 : (relsOfDefs Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.fixedU10).all
    (fun p => !EraseAll.gr10 p.1 || p.2.1.isEmpty) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim20.XSwap.Typ10
