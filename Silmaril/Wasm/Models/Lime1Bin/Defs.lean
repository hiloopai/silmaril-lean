module

public import Silmaril.Wasm.SpecTec.BinaryAgree.Thms
public import Silmaril.Wasm.Models.Lime1Core.Thms
public import Silmaril.Wasm.Models.V10.Defs

/-!
# Binary front ends of the Lime1, 1.0 and Core 3.0 models

The Wasm models of `Silmaril.Wasm.Models` take abstract syntax as modules. Their binary front ends
take **byte strings**, valid when the binary grammar reads them as a valid module:

* `decodeL`, `decodeC`, `decodeV1`: the Lime1, Core 3.0 and 1.0 decodings of a byte string
  (each grammar is functional, so a byte string has at most one decoding);
* `ValidL b`: `b` encodes a valid Lime1 module (`Lime1.Binary.Encodes`, the Lime1 profile's
  grammar with call-indirect-overlong); `ValidC S b`: `b` encodes a module of `core|S`
  (`Binary.Core.Encodes`, every gated form allowed); `ValidV1 b`: `b` encodes a module of
  `v10own` (`V1.Binary.Encodes`);
* `lime1Bin H`, `coreBin P H S`, `v10Bin H`: `lime1own H`, `coreModel P H S` and `v10own H`
  with byte strings as modules. Points, calls and observations are unchanged: the front end
  only changes what a module is.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.Lime1Bin

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Models

/-- The Lime1 decoding of a byte string, if it has one. -/
noncomputable def decodeL (b : Bytes) : Option Lime1.Module := by
  classical
  exact if h : ∃ m, Lime1.Binary.Encodes b m then some h.choose else none

/-- The Core 3.0 decoding of a byte string, if it has one. -/
noncomputable def decodeC (b : Bytes) : Option Silmaril.Wasm.Module := by
  classical
  exact if h : ∃ m, Core.Encodes b m then some h.choose else none

/-- The Wasm 1.0 decoding of a byte string, if it has one. -/
noncomputable def decodeV1 (b : Bytes) : Option V1.Module := by
  classical
  exact if h : ∃ m, V1.Binary.Encodes b m then some h.choose else none

/-- Valid Lime1 bytes: the encoding of a valid Lime1 module. -/
def ValidL (b : Bytes) : Prop :=
  ∃ m, Lime1.Binary.Encodes b m ∧ Lime1.Validation.ModuleValid m

/-- Valid Core 3.0 bytes of `S`: the encoding of a valid module of `S`. -/
def ValidC (S : FeatureSet) (b : Bytes) : Prop := ∃ m, Core.Encodes b m ∧ ValidIn S m

/-- Valid 1.0 bytes: the encoding of a module of `v10own`. -/
def ValidV1 (b : Bytes) : Prop :=
  ∃ m, V1.Binary.Encodes b m ∧ V1.Validation.ModuleValid m ∧
    Lime1.Validation.Module.SegmentOffsetsImported m.toLime

/-- **The binary front end of `lime1own`**: modules are byte strings. -/
def lime1Bin (H : Type) : WasmModel :=
  { Lime1Core.lime1own H with Module := Bytes, Valid := ValidL }

/-- **The binary front end of `core|S`.** -/
def coreBin (P : Numerics.Profile) (H : Type) (S : FeatureSet) : WasmModel :=
  { coreModel P H S with Module := Bytes, Valid := ValidC S }

/-- **The binary front end of `v10own`.** -/
def v10Bin (H : Type) : WasmModel :=
  { V10.v10own H with Module := Bytes, Valid := ValidV1 }

end Silmaril.Wasm.Models.Lime1Bin
