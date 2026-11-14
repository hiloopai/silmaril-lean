module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffKeys
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `theory-diff`, wasm-1.0 original → fixed, rules 33–65: the dropped rules, by the kernel

Every rule of the earlier script in this range is kept by the later one exactly when its key
is not in `keysWasm10Fixed`.

One of 4 chunks of about 33 rules, so that each
module stays under the time budget under parallel load.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Versions

open Silmaril.Wasm.SpecTec.Scripts

set_option maxRecDepth 100000 in
theorem check_wasm10Fixed_33 :
    chunkOk Wasm10.envOriginal Wasm10.envFixed keysWasm10Fixed 33 33 = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Institution.Versions
