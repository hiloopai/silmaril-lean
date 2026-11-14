module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffKeys
public import Silmaril.Wasm.SpecTec.Versions.Defs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `theory-diff`, wasm-3.0 pinned → main: the keys of the dropped entries, by the kernel

The entries of `ruleList Wasm30.envOriginal` with a key in `keysWasm30Main` have exactly those
23 keys, once each and in order. Only names are evaluated; no rule is printed.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Versions

open Silmaril.Wasm.SpecTec.Scripts

set_option maxRecDepth 100000 in
theorem droppedKeys_wasm30_main :
    droppedKeys Wasm30.envOriginal keysWasm30Main = keysWasm30Main := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Institution.Versions
