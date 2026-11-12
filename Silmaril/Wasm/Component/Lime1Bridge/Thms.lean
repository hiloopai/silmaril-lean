module

public import Silmaril.Proofs.Wasm.Component.Lime1Bridge.Erase

/-!
# The Lime1 instantiation bridge at the level of stores: theorems

Proofs in `Silmaril.Proofs.Wasm.Component.Lime1Bridge.Erase`; statements in `Defs`.

* **`behaviours_sub_erase`**: Lime1 behaviours, read in Core values, are Core 3.0 behaviours (at
  `Profile.spec`) in **every** Core store whose erasure is the image of the Lime1 store, not only
  in the image store itself (`Lime1Core.lime1_core_beh`);
* **`specSub_of_instBridgeE`**: the engine-run half of `Lime1Ref.RefToSpecLime1` follows
  from the store-level bridge `InstBridgeE`, which is about instantiation only;
* **`refToSpec_lime1_of_E`**: `RefToSpecLime1` (the corrected `RefToSpec lime1G`) follows
  from `RefToSpecELime1` and `InstBridgeE`; `Simple.sound_lime1_of_E`: soundness of
  the IR over `modSem Profile.spec` for the reference machine over the Lime1 engine, on the
  Lime1 domain, from the same two statements.

So the former `Task.instBridge`, whose behaviour inclusion between the image store and the Core
instance's store would need a simulation of Core by Core, is not needed and has been removed (round
2 cleanup): the two open halves are the machine half `RefToSpecELime1` and the
instantiation statement `InstBridgeE`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Lime1Bridge

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Lime1Ref
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component.Engine.Lime1 (lime1)

/-- **Lime1 behaviours are Core 3.0 behaviours in every store erasing to the image.** -/
theorem behaviours_sub_erase {H : Type} {s : Silmaril.Wasm.Models.V10.LStore H}
    {src : Silmaril.Wasm.Models.V10.LHost H} (hwf : Silmaril.Wasm.Lime1.Execution.StoreWF s)
    (hp : Silmaril.Wasm.Lime1.Execution.HostPreserves src)
    (hk : Silmaril.Wasm.Models.V10.HostKeepsL src) {S : Silmaril.Wasm.Execution.Core.Store H}
    (hS : Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase S = s.toCore)
    {a : Silmaril.Wasm.Execution.Runtime.FuncAddr} (ha : a.value < s.funcs.length)
    (vs : List Silmaril.Wasm.Execution.Runtime.Value) :
    Silmaril.Wasm.Behaviour.mapSet Silmaril.Wasm.Execution.Runtime.Value.toCore
        (Silmaril.Wasm.Models.Lime1Core.behavioursL src s a vs) ⊆
      Silmaril.Wasm.Execution.Core.behaviours Profile.spec
        (Silmaril.Wasm.Models.Lime1Core.liftHostC src) S a.value
        (vs.map Silmaril.Wasm.Execution.Runtime.Value.toCore) :=
  Silmaril.Proofs.Wasm.Component.Lime1Bridge.behaviours_sub_erase hwf
    (Silmaril.Wasm.Models.Lime1Core.liftHostC_compatible hp hk) hS ha vs

/-- **The engine-run half for Lime1, from the store-level bridge.** -/
theorem specSub_of_instBridgeE (hB : InstBridgeE) :
    SpecSubOn lime1 Lime1G.lime1G.emb Profile.spec Lime1Dom :=
  Silmaril.Proofs.Wasm.Component.Lime1Bridge.specSub_of_instBridgeE hB

/-- **The corrected `RefToSpec lime1G` from the machine half and the store-level bridge.** -/
theorem refToSpec_lime1_of_E (hR : RefToSpecELime1) (hB : InstBridgeE) :
    RefToSpecLime1 :=
  refToSpecOn_of_specE hR (specSub_of_instBridgeE hB)

/-- **Soundness of the IR for the reference machine over the Lime1 engine**, on the Lime1
domain, from the machine half and the store-level bridge. -/
theorem Simple.sound_lime1_of_E (hR : RefToSpecELime1) (hB : InstBridgeE)
    (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple) (hD : Lime1Dom c) (hc : c.Good)
    (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHostE lime1) () (c.toRef.map ofCoreL) []
      c.exports[j].name (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (modSem Profile.spec))
      ⟨j, by simp [Simple.toComp]⟩ vs b :=
  Lime1Ref.Simple.sound_lime1_of (refToSpec_lime1_of_E hR hB) prof c hD hc hf hi ha j vs hvs b hb

/-- info: 'Silmaril.Wasm.Component.Lime1Bridge.refToSpec_lime1_of_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refToSpec_lime1_of_E

end Silmaril.Wasm.Component.Lime1Bridge
