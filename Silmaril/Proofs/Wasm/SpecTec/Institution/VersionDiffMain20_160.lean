module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffKeys
public import Silmaril.Wasm.SpecTec.Versions.Defs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `theory-diff`, wasm-2.0 pinned → main `e7a9df7c`, rules 160–191: the dropped rules, by the kernel

Every rule of the earlier script in this range is kept by the later one exactly when its key
is not in `keysWasm20Main`.

One of 8 chunks of about 32 rules, so that each
module stays under the time budget under parallel load.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Versions

open Silmaril.Wasm.SpecTec.Scripts

set_option maxRecDepth 100000 in
theorem check_main20_160 :
    chunkOk Wasm20.envOriginal Versions.Main.Wasm20.env keysWasm20Main 160 32 = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Institution.Versions
