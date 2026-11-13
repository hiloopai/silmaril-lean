module

public import Silmaril.Proofs.Wasm.Models.V10Lime1.Run
public import Silmaril.Proofs.Wasm.Models.V10Lime1.Dom
public import Silmaril.Proofs.Wasm.Models.V10Lime1.Valid
public import Silmaril.Wasm.Models.Lime1Bin.Thms
public import Silmaril.Wasm.Models.Realise.Defs

/-!
# `v10own → lime1own` and `v10Bin → lime1Bin`: Wasm 1.0 is a sub-language of Lime1

Over the copied lock-step simulation 1.0 → Lime1 (`V1.Execution.{Step,Steps,Diverges}.toLime`):

* `valCore_eq`: `v10own` reads values in Core through 2.0, `lime1own` directly; the two agree;
* `v10_lime1_valid`: a module of `v10own` has a valid Lime1 image (`ModuleValid.toLime`);
* `obs_sub`: the observations of `v10own` at `p` are observations of `lime1own` at `ptL p`
  (the Lime1 store with the gated transported host, `Defs`), for the same call;
* **`v10Lime1Emb H : (v10own H).Emb (lime1own H)`**, direction `sub`, with module map
  `V1.Module.toLime`, and its atlas transition `v10Lime1Trans`;
* `v10_lime1_valid_reflect_false` (refutation): validity is not reflected, so the embedding is
  not conservative (`not_conservative`): `V10.twoResults` is invalid in 1.0 (no multi-value),
  its Lime1 image is valid;
* **`v10BinLime1 H : (v10Bin H).Emb (lime1Bin H)`**: the binary front ends, **the identity on
  byte strings** (`Lime1Bin.validL_of_validV1`), with `v10Lime1Emb`'s point and call maps;
* `bin_square`: on the bytes of a 1.0 module, Lime1's decoding is the Lime1 image of 1.0's
  decoding, so `v10BinLime1` covers `v10Lime1Emb` along the decodings;
* `v10BinCore H : (v10Bin H).Emb (coreBin Profile.spec H v30)`: the composite with
  `Lime1Bin.lime1BinCore`, again the identity on byte strings (`v10BinCore_mod`).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V10Lime1

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime Silmaril.Wasm.Binary
open Silmaril.Wasm.Models Silmaril.Wasm.Atlas
open Silmaril.Wasm.Models.Lime1Bin

variable {H : Type}

/-- 1.0 values read in Core through 2.0 are their direct Core reading. -/
theorem valCore_eq (v : Value) : V10.valCore v = Value.toCore v := by
  rcases v with ⟨t, bits⟩
  cases t <;> rfl

/-- A module of `v10own` has a valid Lime1 image. -/
theorem v10_lime1_valid {m : Silmaril.Wasm.V1.Module} (h : (V10.v10own H).Valid m) :
    (Lime1Core.lime1own H).Valid m.toLime :=
  h.1.toLime

/-- **The observations of `v10own` are observations of `lime1own` at the image point.** -/
theorem obs_sub {p : V10.Pt H} (hp : V10.dom p) (c : V10.Call) :
    V10.obs p c ⊆ Lime1Core.obs (ptL p) c := by
  rintro _ ⟨ha, b, hb, rfl⟩
  refine ⟨by simpa [ptL, V10.limeStore, Store.mapCode] using ha, b,
    Silmaril.Proofs.Wasm.Models.V10Lime1.behaviours_sub hp c.1 c.2 hb, ?_⟩
  rw [show V10.valCore = Value.toCore from funext valCore_eq]

/-- **The embedding `v10own → lime1own`** (direction `sub`). -/
def v10Lime1Emb (H : Type) : (V10.v10own H).Emb (Lime1Core.lime1own H) where
  mod := Silmaril.Wasm.V1.Module.toLime
  valid _ h := v10_lime1_valid h
  pt := ptL
  call c := c
  readback := some
  dom _ hp := Silmaril.Proofs.Wasm.Models.V10Lime1.ptL_dom hp
  dir := .sub
  sat _ hp c := fun b hb => ⟨b, obs_sub hp c hb, rfl⟩

theorem v10Lime1Emb_dir (H : Type) : (v10Lime1Emb H).dir = .sub := rfl

/-- The atlas transition of `v10Lime1Emb`: universal sentences of `lime1own` are reflected into
`v10own`. -/
def v10Lime1Trans (H : Type) :
    Transition (V10.v10own H).chart ((Lime1Core.lime1own H).viewChart some) :=
  (v10Lime1Emb H).toTransition

/-- **Validity is not reflected from Lime1 to 1.0**: Lime1 has multi-value. -/
theorem v10_lime1_valid_reflect_false :
    ¬ ∀ m : Silmaril.Wasm.V1.Module, (Lime1Core.lime1own H).Valid m.toLime →
      (V10.v10own H).Valid m := fun h =>
  Silmaril.Proofs.Wasm.Models.V10.twoResults_invalid
    (h _ Silmaril.Proofs.Wasm.Models.V10Lime1.twoResults_toLime_valid).1

/-- So `v10Lime1Emb` is not conservative. -/
theorem not_conservative : ¬ (v10Lime1Emb H).Conservative := fun h =>
  v10_lime1_valid_reflect_false (H := H) h.reflect

/-- **The binary embedding `v10Bin → lime1Bin`: the identity on byte strings.** -/
def v10BinLime1 (H : Type) : (v10Bin H).Emb (lime1Bin H) where
  mod b := b
  valid _ h := validL_of_validV1 h
  pt := ptL
  call c := c
  readback := some
  dom _ hp := Silmaril.Proofs.Wasm.Models.V10Lime1.ptL_dom hp
  dir := .sub
  sat _ hp c := fun b hb => ⟨b, obs_sub hp c hb, rfl⟩

theorem v10BinLime1_mod (H : Type) (b : Bytes) : (v10BinLime1 H).mod b = b := rfl

/-- **The decoding square**: on the bytes of a 1.0 module, Lime1 decodes to the Lime1 image of
the 1.0 decoding, which is `v10Lime1Emb`'s module map. -/
theorem bin_square {b : Bytes} {m : Silmaril.Wasm.V1.Module} (he : V1.Binary.Encodes b m) :
    decodeL ((v10BinLime1 H).mod b) = (decodeV1 b).map (v10Lime1Emb H).mod := by
  rw [Silmaril.Proofs.Wasm.Models.Lime1Bin.decodeV1_eq he, v10BinLime1_mod, decodeL_of_v1 he]
  rfl

/-- **`v10Bin → coreBin v30`**: the composite with `lime1BinCore`. -/
def v10BinCore (H : Type) : (v10Bin H).Emb (coreBin Numerics.Profile.spec H v30) :=
  (v10BinLime1 H).comp (lime1BinCore H) (d := .sub) rfl

/-- It is the identity on byte strings too. -/
theorem v10BinCore_mod (H : Type) (b : Bytes) : (v10BinCore H).mod b = b := rfl

end Silmaril.Wasm.Models.V10Lime1

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.Models.V10Lime1.obs_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.V10Lime1.obs_sub

/-- info: 'Silmaril.Wasm.Models.V10Lime1.v10Lime1Emb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.V10Lime1.v10Lime1Emb

/-- info: 'Silmaril.Wasm.Models.V10Lime1.not_conservative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.V10Lime1.not_conservative

/-- info: 'Silmaril.Wasm.Models.V10Lime1.bin_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.V10Lime1.bin_square

/-- info: 'Silmaril.Wasm.Models.V10Lime1.v10BinCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.V10Lime1.v10BinCore
