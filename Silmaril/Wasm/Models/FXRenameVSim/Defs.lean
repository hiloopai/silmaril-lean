module

public import Silmaril.Wasm.Models.FXRenameV.Defs

/-!
# Exception renaming for `StepFX'`: values and contexts

`Silmaril.Wasm.Models.FXRenameV` renames the exception addresses of FX code (`rnA`, `rnL`) and of
continuation stores (`KRn`). The simulation for `StepFX'` also renames what the rules take
apart:

* `rnFV`: an FX value (a Core value is renamed, a continuation reference is kept);
* `rnCtx`: a context of suspension (value prefixes, suffixes and frames' locals renamed).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXRenameVSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXRename
open Silmaril.Wasm.Models.FXRenameV

/-- Rename the exception addresses of an FX value. -/
def rnFV (n : Nat) : FVal → FVal
  | .val v => .val (rnVal n v)
  | .cont k => .cont k

/-- Rename the exception addresses of a context of suspension. -/
def rnCtx (n : Nat) : CtxV → CtxV
  | .hole => .hole
  | .seq vs E rest => .seq (vs.map (rnFV n)) (rnCtx n E) (rnL n rest)
  | .label m k E => .label m k (rnCtx n E)
  | .frame m f E => .frame m (rnFrame n f) (rnCtx n E)
  | .handler hs E => .handler hs (rnCtx n E)

end Silmaril.Wasm.Models.FXRenameVSim
