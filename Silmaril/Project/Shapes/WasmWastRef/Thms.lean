module

public import Silmaril.Project.Shapes.WasmWastRef.Defs
public import Silmaril.Wasm.Execution.Core.Instantiation
public import Silmaril.Wasm.Execution.MemRep.Sim.Defs
import Silmaril.Proofs.Project.Shapes.WasmWastRef

/-!
# WAST host references (theorems)

* `invokeOkRB_sound`: arguments that `argsOkR` accepts (numbers of their parameter type, and
  `(ref.extern n)` = `.ref (.extern (.host n))` for an `extern` reference parameter) are typed:
  the premise `InvokeOk` of `$invoke` holds (`RefOk.extern` of `RefOk.host`, Wasm 3.0
  `Ref_ok/extern`, `Ref_ok/host`).
* `invokeOkRB_toBytes`: the check reads only the functions of the store.
* `matchAll_sound`: `matchAll ps vs = true` decides `MatchAll ps vs`.

Proofs: `Silmaril.Proofs.Project.Shapes.WasmWastRef`.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.WasmWastRef

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- **Accepted arguments are typed**: the premise `InvokeOk` of `$invoke`. -/
theorem invokeOkRB_sound {s : Store Nat} {a : Nat} {args : List Val}
    (h : invokeOkRB s a args = true) : InvokeOk s a args :=
  Silmaril.Proofs.Project.Shapes.WasmWastRef.invokeOk_of_invokeOkRB h

/-- The argument check reads only the functions of the store. -/
theorem invokeOkRB_toBytes {R : Type} [Silmaril.Wasm.Execution.MemRep R] (s : Store Nat R)
    (a : Nat) (args : List Val) : invokeOkRB s.toBytes a args = invokeOkRB s a args := rfl

/-- **The pattern decision is sound.** -/
theorem matchAll_sound {ps : List Pat} {vs : List Val} (h : matchAll ps vs = true) :
    MatchAll ps vs :=
  Silmaril.Proofs.Project.Shapes.WasmWastRef.matchAll_sound h

end Silmaril.Project.Shapes.WasmWastRef

end
