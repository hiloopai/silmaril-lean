module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffKeys
public import Silmaril.Wasm.SpecTec.Versions.Defs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `theory-diff`, wasm-3.0 pinned → main `e7a9df7c`, rules 540–565: the dropped rules, by the kernel

Every rule of the earlier script in this range is kept by the later one exactly when its key
is not in `keysWasm30Main`.

One of 28 chunks of about 20 rules, so that each
module stays under the time budget under parallel load.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Versions

open Silmaril.Wasm.SpecTec.Scripts

set_option maxRecDepth 100000 in
theorem check_main30_540 :
    chunkOk Wasm30.envOriginal Versions.Main.Wasm30.env keysWasm30Main 540 26 = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Institution.Versions
