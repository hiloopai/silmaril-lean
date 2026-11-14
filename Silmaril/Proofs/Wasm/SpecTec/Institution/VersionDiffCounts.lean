module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffKeys
public import Silmaril.Wasm.SpecTec.Versions.Defs
public import Silmaril.Wasm.SpecTec.Meta.Defs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `theory-diff` rows: the keys of the dropped entries, by the kernel

For the wasm-1.0, meta-IL and wasm-2.0 rows, the entries of `ruleList env₁` with a key in the
row's list have exactly those keys, once each and in order (`droppedKeys`). Only names are
evaluated; no rule is printed. The meta-IL script has 233 rules (`ruleList_metaIL_length`).
The wasm-3.0 row is in `VersionDiffCounts30`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Versions

open Silmaril.Wasm.SpecTec.Scripts

set_option maxRecDepth 100000 in
theorem ruleList_metaIL_length : (ruleList Meta.envO).length = 233 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem droppedKeys_wasm10_fixed :
    droppedKeys Wasm10.envOriginal keysWasm10Fixed = keysWasm10Fixed := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem droppedKeys_metaIL : droppedKeys Meta.envO keysMetaFixed = keysMetaFixed := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem droppedKeys_wasm10_main :
    droppedKeys Wasm10.envOriginal keysWasm10Main = keysWasm10Main := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem droppedKeys_wasm20_main :
    droppedKeys Wasm20.envOriginal keysWasm20Main = keysWasm20Main := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Institution.Versions
