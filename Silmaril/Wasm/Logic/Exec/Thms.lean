module

public import Silmaril.Wasm.Logic.Exec.Defs
public import Silmaril.Wasm.Examples.Common.Thms

@[expose] public section

/-!
# Straight-line execution and function bodies in the every-run logic: results

Re-exported from `Silmaril.Wasm.Examples.Common` (proofs in
`Silmaril.Proofs.Wasm.Examples.Common.{Exec,Session}`), at every profile and for every host
relation:

* **`Wp.exec1`**: one instruction evaluated by `Silmaril.Wasm.Logic.Core.exec1` (integer
  arithmetic, locals, globals, integer loads and stores) in the every-run logic, either reading
  (`HWP`/`TWP`): the evaluated result is the **only** continuation;
* **`Wp.exec`** and `Wp.exec_eq`: the same for a whole evaluated sequence
  (`Silmaril.Wasm.Logic.Core.exec`);
* **`FSpecValid.of_body_hwp`**: a function specification from an every-run proof of the body
  that returns or traps (`bodyPost`), and `bodyPost_bodyPostK`;
* the head-step inversions `head_*` and `HeadSpec`.

A Silmaril addition (the names; see `Silmaril.Wasm.Logic.Exec.Defs` for why the declarations stay in
`Silmaril.Wasm.Examples.Common`).
-/

namespace Silmaril.Wasm.Logic.Exec

export Silmaril.Wasm.Examples.Common (
  HeadSpec HeadSpec.wp head_nop head_drop head_localGet head_localSet head_globalGet
  head_globalSet head_intUnOp head_intBinOp head_intTestOp head_intRelOp head_intLoadFull
  head_intLoadPack head_intStoreFull head_intStorePack Wp.exec1_intConst Wp.exec1_localTee
  Wp.exec1 Wp.exec Wp.exec_eq bodyPost_bodyPostK FSpecValid.of_body_hwp)

end Silmaril.Wasm.Logic.Exec
