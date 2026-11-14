module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffKeys
public import Silmaril.Wasm.SpecTec.Meta.Defs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `theory-diff`, meta-IL original → fixed, rules 117–232: the dropped rules, by the kernel

Every rule of the earlier script in this range is kept by the later one exactly when its key
is not in `keysMetaFixed`.

One of 2 chunks, so that each module stays under the time budget.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Versions

open Silmaril.Wasm.SpecTec.Scripts

set_option maxRecDepth 100000 in
theorem check_metaIL_117 :
    chunkOk Meta.envO Meta.envF keysMetaFixed 117 116 = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Institution.Versions
