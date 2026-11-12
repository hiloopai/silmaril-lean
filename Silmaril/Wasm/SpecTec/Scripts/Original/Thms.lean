module

public import Silmaril.Wasm.SpecTec.Scripts.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Scripts.Original

/-!
# Identities of the original SpecTec scripts

These identities connect the named generated originals to the pinned importer.
They do not depend on the corrected scripts' audits or revalidation.
-/

public section

namespace Silmaril.Wasm.SpecTec.Scripts

open Silmaril.SpecTec

theorem wasm10_original_eq : Wasm10.original = Specs.wasm10 := generated_wasm10_eq

theorem wasm20_original_eq : Wasm20.original = Specs.wasm20 := generated_wasm20_eq

theorem wasm30_original_eq : Wasm30.original = Specs.wasm30 := generated_wasm30_eq

end Silmaril.Wasm.SpecTec.Scripts
