module

public import Silmaril.Proofs.Wasm.Models.Lime1Bin.Decode
public import Silmaril.Proofs.Wasm.Models.Lime1Bin.Witness

/-!
# Binary front ends of the Lime1, 1.0 and Core 3.0 models: theorems

The Lime1 binary grammar (`Lime1.Binary.Encodes`, copied with the SpecTec import) and the
copied 1.0/Lime1/Core 3.0 agreement (`Silmaril.Wasm.SpecTec.BinaryAgree`) related to the models
of `Silmaril.Wasm.Models`. Proofs in `Silmaril.Proofs.Wasm.Models.Lime1Bin`.

* **`lime1BinCore H : (lime1Bin H).Emb (coreBin Profile.spec H v30)`**: the identity on byte
  strings. Valid Lime1 bytes are valid Core 3.0 bytes of `v30` (`validC_of_validL`), and on
  points it is `lime1Emb` (direction `sub`). So the Lime1 profile's binary format embeds in
  the 3.0 binary format **without re-encoding**;
* `lime1BinEmb H : (lime1Bin H).Emb (lime1own H)`: decoding, direction `eq`;
* **the decoding square** (`square`): Lime1 decodes the bytes of a valid module `m` to `m`,
  Core 3.0 decodes them to `m.toCoreBinary`. `lime1Emb`'s module map `toCore` is Core's
  decoding with element segments retyped to `funcref` (`square_retype`), and is **not** Core's
  decoding when there is an element segment (`decodeC_ne_toCore`, a refutation of the naive
  square, restated by `square_retype`). `witness`: a valid module with one table and one
  element segment, and its 22 bytes from the copied encoder, at which all three hold;
* `inst_bytes`, `instDiv_bytes`: a Lime1 instantiation of the module the bytes decode to is
  simulated by a Core 3.0 instantiation of the module **Core decodes from the same bytes**,
  then Core execution (finite and diverging);
* `validL_of_validV1`, `decodeL_of_v1`, `validC_of_validV1`: valid 1.0 bytes are valid Lime1
  bytes (decoding to `m.toLime`) and valid Core 3.0 bytes.

Not done: an embedding `v10Bin → lime1Bin` (the 1.0 and Lime1 models have different points,
and no `v10own → lime1own` embedding exists); binary grammars for the 2.0 and 3.0 version
models other than Core's.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.Lime1Bin

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Models
open Silmaril.Proofs.Wasm.Models.Lime1Bin

variable {H : Type}

/-- **Valid Lime1 bytes are valid Core 3.0 bytes of `v30`.** -/
theorem validC_of_validL {b : Bytes} (h : ValidL b) : ValidC v30 b :=
  Silmaril.Proofs.Wasm.Models.Lime1Bin.validC_of_validL h

/-- **The binary embedding `lime1Bin → coreBin v30`**: the identity on bytes, `lime1Emb` on
points (direction `sub`). -/
def lime1BinCore (H : Type) : (lime1Bin H).Emb (coreBin Numerics.Profile.spec H v30) where
  mod b := b
  valid _ h := validC_of_validL h
  pt := (Lime1Core.lime1Emb H).pt
  call := (Lime1Core.lime1Emb H).call
  readback := some
  dom := (Lime1Core.lime1Emb H).dom
  dir := .sub
  sat := (Lime1Core.lime1Emb H).sat

theorem lime1BinCore_dir (H : Type) : (lime1BinCore H).dir = .sub := rfl

/-- **Decoding `lime1Bin → lime1own`** (direction `eq`). -/
noncomputable def lime1BinEmb (H : Type) : (lime1Bin H).Emb (Lime1Core.lime1own H) where
  mod b := (decodeL b).getD {}
  valid b h := by
    obtain ⟨m, he, hv⟩ := h
    rw [decodeL_eq he]
    exact hv
  pt p := p
  call c := c
  readback := some
  dom _ hp := hp
  dir := .eq
  sat p _ c := WasmModel.view_some (Lime1Core.lime1own H) p c

/-- **The decoding square.** -/
theorem square {b : Bytes} {m : Lime1.Module} (he : Lime1.Binary.Encodes b m)
    (hv : Lime1.Validation.ModuleValid m) :
    decodeL b = some m ∧ decodeC b = some m.toCoreBinary :=
  Silmaril.Proofs.Wasm.Models.Lime1Bin.square he hv

/-- **`lime1Emb`'s module map is Core's decoding, retyped.** -/
theorem square_retype {b : Bytes} {m : Lime1.Module} (he : Lime1.Binary.Encodes b m)
    (hv : Lime1.Validation.ModuleValid m) : (decodeC b).map retype = some m.toCore :=
  Silmaril.Proofs.Wasm.Models.Lime1Bin.square_retype he hv

/-- **Refutation of the naive square**: with an element segment, Core 3.0 does not decode the
bytes to `toCore`. -/
theorem decodeC_ne_toCore {b : Bytes} {m : Lime1.Module} (he : Lime1.Binary.Encodes b m)
    (hv : Lime1.Validation.ModuleValid m) (hel : m.elems ≠ []) :
    decodeC b ≠ some m.toCore :=
  Silmaril.Proofs.Wasm.Models.Lime1Bin.decodeC_ne_toCore he hv hel

/-- **The square and its refutation at a concrete valid module**: `witBytes`, the encoder's
output for one table and one legacy element segment, decodes to `witMod` in Lime1, to
`witMod.toCoreBinary` in Core 3.0, and not to `witMod.toCore`. -/
theorem witness :
    Lime1.Validation.ModuleValid witMod ∧ Lime1.Binary.Encodes witBytes witMod ∧
      decodeL witBytes = some witMod ∧ decodeC witBytes = some witMod.toCoreBinary ∧
      decodeC witBytes ≠ some witMod.toCore :=
  ⟨wit_valid, wit_encodes, wit_square⟩

/-- **Instantiation from the same bytes**: a Lime1 instantiation of the module that `b`
encodes is simulated by a Core 3.0 instantiation of the module Core decodes from `b`, then a
Core run to the same outcome and the image of the final store. -/
theorem inst_bytes {src : Lime1.Execution.HostSemantics H}
    {tgt : Lime1.Execution.ToCore.CHostSemantics H} (hosts : Lime1.Execution.HostCompatible src tgt)
    {b : Bytes} {m : Lime1.Module} (he : Lime1.Binary.Encodes b m)
    {before after : Lime1.Execution.Store H} {imports : List Execution.Runtime.ExternVal}
    {module : Execution.Runtime.ModuleInst} {outcome : Execution.Runtime.Result}
    (bounds : Lime1.Execution.InstantiationBounds before m)
    (h : Lime1.Execution.Instantiation src before m imports after module outcome) :
    ∃ M c c', decodeC b = some M ∧
      Execution.Core.Instantiate Lime1.Execution.coreProfile tgt before.toCore M
        (imports.map Execution.Runtime.ExternVal.toCore) c ∧
      Execution.Core.Steps Lime1.Execution.coreProfile tgt c c' ∧
      c'.code = outcome.toCore.toAdmin ∧
      Lime1.Execution.ToCore.Store.erase c'.store = after.toCore := by
  obtain ⟨c, c', hi, hs, hc, hst, -⟩ := Lime1.Execution.Instantiation.toCoreBinary hosts bounds h
  exact ⟨m.toCoreBinary, c, c', (square he h.1).2, hi, hs, hc, hst⟩

/-- **Diverging instantiation from the same bytes.** -/
theorem instDiv_bytes {src : Lime1.Execution.HostSemantics H}
    {tgt : Lime1.Execution.ToCore.CHostSemantics H} (hosts : Lime1.Execution.HostCompatible src tgt)
    {b : Bytes} {m : Lime1.Module} (he : Lime1.Binary.Encodes b m)
    (hv : Lime1.Validation.ModuleValid m)
    {before : Lime1.Execution.Store H} {imports : List Execution.Runtime.ExternVal}
    (bounds : Lime1.Execution.InstantiationBounds before m)
    (h : Lime1.Execution.InstantiationDiverges src before m imports) :
    ∃ M c, decodeC b = some M ∧
      Execution.Core.Instantiate Lime1.Execution.coreProfile tgt before.toCore M
        (imports.map Execution.Runtime.ExternVal.toCore) c ∧
      Execution.Core.Diverges Lime1.Execution.coreProfile tgt c := by
  obtain ⟨c, hi, hd⟩ := Lime1.Execution.InstantiationDiverges.toCoreBinary hosts bounds h
  exact ⟨m.toCoreBinary, c, (square he hv).2, hi, hd⟩

/-- **Valid 1.0 bytes are valid Lime1 bytes.** -/
theorem validL_of_validV1 {b : Bytes} (h : ValidV1 b) : ValidL b :=
  Silmaril.Proofs.Wasm.Models.Lime1Bin.validL_of_validV1 h

/-- Lime1 decodes 1.0 bytes to the Lime1 image. -/
theorem decodeL_of_v1 {b : Bytes} {m : V1.Module} (he : V1.Binary.Encodes b m) :
    decodeL b = some m.toLime :=
  Silmaril.Proofs.Wasm.Models.Lime1Bin.decodeL_of_v1 he

/-- **Valid 1.0 bytes are valid Core 3.0 bytes of `v30`.** -/
theorem validC_of_validV1 {b : Bytes} (h : ValidV1 b) : ValidC v30 b :=
  Silmaril.Proofs.Wasm.Models.Lime1Bin.validC_of_validV1 h

end Silmaril.Wasm.Models.Lime1Bin

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.Models.Lime1Bin.validC_of_validL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.Lime1Bin.validC_of_validL

/-- info: 'Silmaril.Wasm.Models.Lime1Bin.square_retype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.Lime1Bin.square_retype

/-- info: 'Silmaril.Wasm.Models.Lime1Bin.decodeC_ne_toCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.Lime1Bin.decodeC_ne_toCore

/-- info: 'Silmaril.Wasm.Models.Lime1Bin.witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.Lime1Bin.witness

/-- info: 'Silmaril.Wasm.Models.Lime1Bin.inst_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.Lime1Bin.inst_bytes

/-- info: 'Silmaril.Wasm.Models.Lime1Bin.validC_of_validV1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.Lime1Bin.validC_of_validV1
