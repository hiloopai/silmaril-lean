module

public import Silmaril.Wasm.Component.Lime1RefAll.Thms
import Silmaril.Proofs.Wasm.Component.Lime1Eng.Typed
import Silmaril.Proofs.Wasm.Component.Lime1Eng.Inst

/-!
# The two Lime1 engine facts

`Lime1RefAll.refToSpec_lime1_of_engine` reduces the corrected `RefToSpec lime1G`
(`Lime1Ref.RefToSpecLime1`) to the two frozen engine facts `Lime1RefE.Lime1TypedOk`
and `Lime1RefE.Lime1InstOk`. Proofs in `Silmaril.Proofs.Wasm.Component.Lime1Eng`.

* **`lime1Typed`** (proved): type soundness of Lime1 export calls on the Lime1 domain. It needs
  no Lime1 type soundness theorem: through the proved instantiation bridge
  (`Lime1Inst.instBridgeE`) a returned Lime1 run is a returned Core 3.0 run of the same export
  in a Core 3.0 instance of the module, whose results are typed by Core 3.0 type soundness.
* **`lime1Inst`** (proved): the Lime1 engine instantiates the module of every component in the
  Lime1 domain whose Core module has a Core 3.0 instance. The converse of the instantiation
  bridge, read off the Core 3.0 run: Core's `$evalglobals` evaluates the images of the global
  initializers, so Lime1 evaluates them (`evalConst_back`); Lime1 allocation of a valid module
  cannot fail otherwise; the Core allocation of the global-free residue is related to the Lime1
  allocation (`rel_of_prepare`), Core segment writes keep globals and table and memory sizes, so
  Core's successful segment run resolves every Lime1 segment (`elemList_back`,
  `dataList_back`; offsets are `i32` by Lime1 typing with globals); there is no start function,
  and the lookup of the exports by name succeeds (distinct export names).
* **`refToSpec_lime1`** (proved): **the corrected `RefToSpec lime1G` holds unconditionally**:
  on the Lime1 domain, every behaviour of the reference component machine over the Lime1 engine
  is an outcome of the Core 3.0 canonical-ABI specification at `Profile.spec`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Lime1Eng

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference

/-- **Typed results of Lime1 export calls** (`Lime1RefE.Lime1TypedOk`, proved). -/
theorem lime1Typed : Lime1RefE.Lime1TypedOk :=
  Silmaril.Proofs.Wasm.Component.Lime1Eng.lime1Typed_proof

/-- **The corrected `RefToSpec lime1G` from the instantiation fact alone.** -/
theorem refToSpec_lime1_of_inst (hI : Lime1RefE.Lime1InstOk) :
    Lime1Ref.RefToSpecLime1 :=
  Lime1RefAll.refToSpec_lime1_of_engine hI lime1Typed

/-- **The Lime1 engine instantiates every module of the Lime1 domain with a Core 3.0 instance**
(`Lime1RefE.Lime1InstOk`, proved). -/
theorem lime1Inst : Lime1RefE.Lime1InstOk :=
  Silmaril.Proofs.Wasm.Component.Lime1Eng.lime1Inst_proof

/-- **The corrected `RefToSpec lime1G`** (`Lime1Ref.RefToSpecLime1`), unconditionally. -/
theorem refToSpec_lime1 : Lime1Ref.RefToSpecLime1 :=
  Lime1RefAll.refToSpec_lime1_of_engine lime1Inst lime1Typed

/-- **The machine half for Lime1** (`Lime1Ref.RefToSpecELime1`), unconditionally. -/
theorem refToSpecE_lime1 : Lime1Ref.RefToSpecELime1 :=
  Lime1RefE.refToSpecE_lime1_of lime1Inst lime1Typed

/-- **Soundness of the IR for the reference machine over the Lime1 engine**, on the Lime1
domain, unconditionally. -/
theorem Simple.sound_lime1 (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple)
    (hD : Lime1Ref.Lime1Dom c) (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (Param.refHostE Silmaril.Wasm.Component.Engine.Lime1.lime1) ()
      (c.toRef.map Lime1Ref.ofCoreL) [] c.exports[j].name (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length)
      (c.toComp.den (modSem Silmaril.Wasm.Numerics.Profile.spec)) ⟨j, by simp [Simple.toComp]⟩ vs b :=
  Lime1Inst.Simple.sound_lime1_of_machine refToSpecE_lime1 prof c hD hc hf hi ha j vs hvs b hb

/-- info: 'Silmaril.Wasm.Component.Lime1Eng.lime1Typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lime1Typed

/-- info: 'Silmaril.Wasm.Component.Lime1Eng.lime1Inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lime1Inst

/-- info: 'Silmaril.Wasm.Component.Lime1Eng.refToSpec_lime1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refToSpec_lime1

/-- info: 'Silmaril.Wasm.Component.Lime1Eng.Simple.sound_lime1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Simple.sound_lime1

end Silmaril.Wasm.Component.Lime1Eng
