module

public import Silmaril.Wasm.FX.Asyncify.Tool.Selective.Defs

/-!
# Calm functions never suspend

The selective mode (`Silmaril.Wasm.FX.Asyncify.Tool.Selective`) leaves the calls of *calm* functions
(outside `mayS P`) uninstrumented. This module states what calm means on the source machine:

* `CalmFrame P fr`: the frame runs a calm defined function and its code is a suffix of the
  function's flat body;
* `CalmCfg P c`: every frame of `c` is calm.

`Silmaril.Wasm.FX.Asyncify.Tool.Calm.Thms` proves that `mayS P` is closed under callers (it is a
fixed point of `suspStep`), that a calm function's call statements call calm defined functions,
and that a source run from calm frames never reaches an import call, so a call of a calm
function never consults the host.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

/-- A frame runs a calm defined function, at a suffix of its flat body. -/
def CalmFrame (P : Prog) (fr : Frame) : Prop :=
  ∃ fn, P.imps.length ≤ fr.fid ∧ P.fns[fr.fid - P.imps.length]? = some fn ∧
    mayS P fr.fid = false ∧ ∃ pre, pre ++ fr.code = fn.body

/-- Every frame of a configuration is calm. -/
def CalmCfg (P : Prog) (c : Cfg) : Prop := ∀ fr ∈ c.frames, CalmFrame P fr

end Silmaril.Wasm.FX.Asyncify.Tool
