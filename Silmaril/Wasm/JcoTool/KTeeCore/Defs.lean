module

public import Silmaril.Wasm.JcoTool.KCoreHost.Defs
public import Silmaril.Wasm.JcoTool.KTeeEmit.Defs

/-!
# The generated tee on Core 3.0: the host store of its built-ins

`KCoreRun` runs the generated modules on Core 3.0 with the eight imported built-ins supplied as
host functions. The tee (`KTeeEmit.toModuleT N name`, the module of `KTee.genT N`) imports
`task.return` with **two** parameters (type `4` of `KCoreEmit.types`), so its host store differs
from `KCoreHost.hostStore` in that one function:

* `impTyT b`: the type index of built-in `b`'s import in the tee (`KTeeEmit.importsT`);
* `hostStoreT hb`: functions `0..7` are the built-ins as host functions `hb b`, at the closed
  types the tee imports them with (`KCoreHost.hostAddrs` are their addresses).

`KTeeCore.Thms` proves that this store supplies the tee's imports (`KCoreRun.ImpsOKN 2`), and
links the tee to Core 3.0 from instantiation on: the lift (`task.return` of two values) and every
runtime step.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KTeeCore

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.JcoTool.KCore (BI)

/-- The type index of built-in `b`'s import in the tee: `task.return` takes two `i32`s. -/
def impTyT : BI → Nat
  | .taskReturn => 4
  | b => KCoreHost.impTy b

/-- The closed defined type of built-in `b`'s import in the tee. -/
def hostDTT (b : BI) : DefType :=
  .defn (liftRec (Silmaril.Wasm.JcoTool.KCoreEmit.types.getD (impTyT b) ⟨[]⟩)) 0

variable {H : Type}

/-- **The host store of the tee**: functions `0..7` are the built-ins, as host functions `hb b`. -/
def hostStoreT (hb : BI → H) : Store H :=
  { funcs := KCoreHost.bis.map fun b => ⟨hostDTT b, {}, .host (hb b)⟩ }

end Silmaril.Wasm.JcoTool.KTeeCore
