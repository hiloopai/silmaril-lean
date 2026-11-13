module

public import Silmaril.Wasm.Models.Lime1Bin.Thms
public import Silmaril.Wasm.Models.Lime1Mvp.Defs

/-!
# Profiles of the Core 3.0 binary front end, read up to the legacy forms

`Lime1Bin.coreBin P H S` takes as modules the byte strings that Core 3.0's grammar decodes to a
valid module of `S` (`ValidC S`). The 3.0 grammar decodes a legacy (1.0 form) element segment
to element type `(ref func)`, which the profile restriction files under typed function
references, a 3.0 feature; and a 1.0 table's implicit initialiser is `ref.null func`, filed
under reference types. So `coreBin` at an earlier profile does not take the bytes of that
profile (`BinProfile.Thms`). This topic reads the decoding up to both legacy forms:

* `ValidCR S b`: Core 3.0 decodes `b` to a module `M` whose retyped form (`Lime1Bin.retype`:
  element types widened to `funcref`, as `toCore` writes them) is valid and a module of `S` up
  to the canonical MVP initialisers (`Lime1Mvp.ValidInM S`);
* `coreBinR P H S`: `coreModel P H S` with byte strings as modules and `ValidCR S` as validity.
  Points, calls and observations are those of `core|S`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.BinProfile

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Models

/-- **Core 3.0 bytes of `S`, read up to the legacy element type and MVP initialisers.** -/
def ValidCR (S : FeatureSet) (b : Bytes) : Prop :=
  ∃ M, Core.Encodes b M ∧ Lime1Mvp.ValidInM S (Silmaril.Proofs.Wasm.Models.Lime1Bin.retype M)

/-- **The binary front end of the profile `S`**, read up to the legacy forms. -/
def coreBinR (P : Numerics.Profile) (H : Type) (S : FeatureSet) : WasmModel :=
  { coreModel P H S with Module := Bytes, Valid := ValidCR S }

end Silmaril.Wasm.Models.BinProfile
