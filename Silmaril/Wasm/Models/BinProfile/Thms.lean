module

public import Silmaril.Proofs.Wasm.Models.BinProfile.Profile
public import Silmaril.Wasm.Models.V10.Thms
public import Silmaril.Wasm.Models.Realise.Defs

/-!
# The 1.0, 2.0 and Lime1 profiles of the Core 3.0 binary front end

There is no 2.0 binary grammar in the copied sources; the 2.0 and 3.0 binary formats are read
here through Core 3.0's grammar (`Binary.Core.Encodes`), restricted to a profile. Over
`Silmaril.Proofs.Wasm.Models.BinProfile`:

**Refutation.** `Lime1Bin.coreBin P H S` (Core bytes of a valid module of `S`) is the wrong
front end for an earlier profile: the 3.0 grammar decodes a legacy element segment to type
`(ref func)`, which needs typed function references (`not_inFeat_toCoreBinary`). So
* `not_validC`, `not_validC_v1`: valid Lime1 bytes and valid 1.0 bytes with an element segment
  are not `ValidC S` for any `S` without typed function references (`v10`, `v20`, `lime1`);
* `wit_profile`: at `Lime1Bin`'s 22-byte witness, `ValidL` and `ValidC v30` hold, while
  `ValidC v10`, `ValidC v20` and `ValidC lime1` fail.

**Restatement.** `coreBinR P H S` reads the decoding up to the legacy forms (`ValidCR S`:
element types widened to `funcref` by `Lime1Bin.retype`, MVP initialisers erased by
`Lime1Mvp.ValidInM`). Then:
* `validCR_of_validL`: valid Lime1 bytes are `ValidCR lime1`; `validCR_of_validV1`: valid
  1.0 bytes are `ValidCR v10` (and `ValidCR v20`, `validCR_mono`);
* **`lime1BinR H : (lime1Bin H).Emb (coreBinR Profile.spec H lime1)`**: the identity on byte
  strings, with `lime1EmbM`'s points and calls, so Lime1 bytes land in the Lime1 profile of
  the 3.0 binary front end, not only in `v30` (`Lime1Bin.lime1BinCore`);
* **`v10BinR H : (v10Bin H).Emb (coreBinR v2Profile H v20)`**: the identity on byte strings,
  with the points and calls of `V10.v10Emb` followed by `V2Core.v20Emb`: 1.0 bytes are 2.0
  bytes of the 3.0 binary format read in the 2.0 profile.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.BinProfile

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Models Silmaril.Wasm.Models.Lime1Bin
open Silmaril.Wasm.Lime1.Execution (v2Profile)

/-- **Lime1 bytes are Core bytes of the Lime1 profile**, up to the legacy forms: the identity on
byte strings. -/
def lime1BinR (H : Type) : (lime1Bin H).Emb (coreBinR Numerics.Profile.spec H lime1) where
  mod b := b
  valid _ h := Silmaril.Proofs.Wasm.Models.BinProfile.validCR_of_validL h
  pt := (Lime1Mvp.lime1EmbM H).pt
  call := (Lime1Mvp.lime1EmbM H).call
  readback := some
  dom := (Lime1Mvp.lime1EmbM H).dom
  dir := .sub
  sat := (Lime1Mvp.lime1EmbM H).sat

/-- The 1.0 → Core composite of `v10Emb` and `v20Emb`. -/
def v10Core (H : Type) : (V10.v10own H).Emb (coreModel v2Profile H v20) :=
  (V10.v10Emb H).comp (V2Core.v20Emb v2Profile H) (d := .sub) rfl

/-- **1.0 bytes are Core bytes of the 2.0 profile**, up to the legacy forms: the identity on
byte strings. -/
def v10BinR (H : Type) : (v10Bin H).Emb (coreBinR v2Profile H v20) where
  mod b := b
  valid _ h := Silmaril.Proofs.Wasm.Models.BinProfile.validCR_mono v10_le_v20
    (Silmaril.Proofs.Wasm.Models.BinProfile.validCR_of_validV1 h)
  pt := (v10Core H).pt
  call := (v10Core H).call
  readback := (v10Core H).readback
  dom := (v10Core H).dom
  dir := .sub
  sat := (v10Core H).sat

theorem lime1BinR_mod (H : Type) (b : Bytes) : (lime1BinR H).mod b = b := rfl
theorem v10BinR_mod (H : Type) (b : Bytes) : (v10BinR H).mod b = b := rfl

/-- **`coreBin` at the 2.0 profile does not take 1.0 bytes with an element segment.** -/
theorem not_validC_v20 {b : Bytes} {m : V1.Module} (he : V1.Binary.Encodes b m)
    (hv : V1.Validation.ModuleValid m) (hel : m.elems ≠ []) : ¬ ValidC v20 b :=
  Silmaril.Proofs.Wasm.Models.BinProfile.not_validC_v1
    Silmaril.Proofs.Wasm.Models.BinProfile.v20_typedFuncRef he hv hel

end Silmaril.Wasm.Models.BinProfile

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.Models.BinProfile.lime1BinR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.BinProfile.lime1BinR

/-- info: 'Silmaril.Wasm.Models.BinProfile.v10BinR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.BinProfile.v10BinR

/-- info: 'Silmaril.Wasm.Models.BinProfile.not_validC_v20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.BinProfile.not_validC_v20

/-- info: 'Silmaril.Proofs.Wasm.Models.BinProfile.wit_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Proofs.Wasm.Models.BinProfile.wit_profile
