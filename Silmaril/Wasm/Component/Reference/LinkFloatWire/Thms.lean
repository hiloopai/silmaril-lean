module

public import Silmaril.Wasm.Component.Reference.LinkFloatWire.Defs
public import Silmaril.Wasm.Component.Reference.Example.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LitmusLinkFloatWire

/-!
# Floats across the wiring of two linked components: the litmus

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LitmusLinkFloatWire`.

`Litmus.nanRbL` (the importer passes `f32.const nan:0x200001` to the exporter's
`g(x: f32) -> u32 = i32.reinterpret_f32 x`) satisfies every hypothesis of
`Linked2.sound_floatV` except `Linked2.ImportsFloatFree` (`Litmus.nanRbL_conds`), and:

* `Litmus.nanRb_ref`: over `core3 neverFail` with the deterministic first-alternative oracle,
  the reference machine returns the canonical NaN's bits `0x7fc00000` (the trampoline's
  `lift_flat` canonicalises; closed kernel evaluation of the copied drivers);
* `Litmus.nanRb_ir`: for every profile, the linked IR `nanRbL.toComp.den (impSem P)` plays `f()`
  answered with the raw bits `0x7fa00001` (it passes the float bit for bit);
* `Litmus.nanRb_floatWire`: all of the above together, with `canonBits ≠ nanBits`.

**What this does not show.** It is not a refutation of `Linked2.sound_floatV` without
`ImportsFloatFree`, for two reasons:

* the reference run is over the executable engine `core3 neverFail`, while `Linked2.sound` and
  `Linked2.sound_floatV` are stated over the relational engine `core3P P`; that the two engines
  have the same behaviours is not shown (`Reference.Thms`), and the drivers over `core3P P` are
  not kernel-evaluable (its status is classical);
* the IR is not shown to be functional here: that `nanRbL.toComp.den (impSem P)` has no play of
  `f()` answered with the canonical bits is not proved (it needs an inversion of the linked
  IR's denotation down to the importer's and exporter's Core runs).

Given both, the naive statement would fail: under `deterministic`, `Linked2.IRObsV` would
require the canonical-bits play.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Numerics (Profile)

namespace Litmus

/-- **The litmus meets every hypothesis of `Linked2.sound_floatV` but float-free imports**
(proved): both components are in the fragment and instantiate as the translations assume, the
importer is within the flat arities, the wiring is well typed and injective, the names avoid
the generated type names and both modules are in the split fragment; the importer's import `g`
carries an `f32`. -/
theorem nanRbL_conds :
    nanRbL.exp.Good ∧ nanRbL.exp.Inst ∧ nanRbL.imp.Good ∧ nanRbL.imp.Inst ∧
      nanRbL.imp.Arity ∧ nanRbL.WireTy ∧ nanRbL.NamesOk ∧ nanRbL.WireNodup ∧
      nanRbL.SplitOk ∧ ¬ nanRbL.ImportsFloatFree :=
  open Silmaril.Proofs.Wasm.Component.Reference.Litmus in
  ⟨nanRbS_good, nanRbS_inst, nanImpS_good, nanImpS_inst, nanImpS_arity, nanRbL_wireTy,
    nanRbL_namesOk, nanRbL_wireNodup, nanRbL_splitOk, nanRbL_not_importsFloatFree⟩

/-- **The reference machine canonicalises the NaN crossing the wiring** (proved, closed kernel
evaluation over `core3 neverFail`, deterministic oracle): `f()` returns the canonical NaN's
bits. -/
theorem nanRb_ref : Outcome.returns (some [toRefVal (.u32 canonBits)]) ∈
    exportBehaviours .deterministic (Host.ofEmbedder Core3Adder.emb) () nanRbL.toRef [] "f" [] :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.nanRb_ref

/-- **The linked IR passes the NaN's raw bits** (proved, every profile): the linked IR plays
`f()` answered with `0x7fa00001`. -/
theorem nanRb_ir (P : Profile) :
    ([.inr (.ask (⟨0, by decide⟩, .vals [])),
      .inr (.ans (m := (⟨0, by decide⟩, .vals [])) (some (.vals [.u32 nanBits])))] :
      List (Silmaril.Games.Move (nanRbL.toComp.imports.sig)
        (Silmaril.Wasm.Component.sigN nanRbL.toComp.exports.length))) ∈
      nanRbL.toComp.den (impSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.nanRb_ir P

/-- **A float across the wiring: the reference and the linked IR answer different bits**
(proved): the litmus meets every hypothesis of `Linked2.sound_floatV` but float-free imports;
the reference machine (over `core3 neverFail`, deterministic oracle) returns the canonical
NaN's bits, the linked IR at every profile has the play returning the raw bits, and the two
differ. Not shown: that the IR has no canonical-bits play, and the reference behaviour over
`core3P P` (see the module docstring). -/
theorem nanRb_floatWire (P : Profile) :
    (nanRbL.exp.Good ∧ nanRbL.exp.Inst ∧ nanRbL.imp.Good ∧ nanRbL.imp.Inst ∧
      nanRbL.imp.Arity ∧ nanRbL.WireTy ∧ nanRbL.NamesOk ∧ nanRbL.WireNodup ∧
      nanRbL.SplitOk ∧ ¬ nanRbL.ImportsFloatFree) ∧
    Outcome.returns (some [toRefVal (.u32 canonBits)]) ∈
      exportBehaviours .deterministic (Host.ofEmbedder Core3Adder.emb) () nanRbL.toRef [] "f"
        [] ∧
    ([.inr (.ask (⟨0, by decide⟩, .vals [])),
      .inr (.ans (m := (⟨0, by decide⟩, .vals [])) (some (.vals [.u32 nanBits])))] :
      List (Silmaril.Games.Move (nanRbL.toComp.imports.sig)
        (Silmaril.Wasm.Component.sigN nanRbL.toComp.exports.length))) ∈
      nanRbL.toComp.den (impSem P) ∧
    canonBits ≠ nanBits :=
  ⟨nanRbL_conds, nanRb_ref, nanRb_ir P, by decide⟩

end Litmus

end Silmaril.Wasm.Component.Reference
