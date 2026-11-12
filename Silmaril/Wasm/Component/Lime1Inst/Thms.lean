module

public import Silmaril.Proofs.Wasm.Component.Lime1Inst.BridgeG

/-!
# The Lime1 instantiation bridge: theorems

Proofs in `Silmaril.Proofs.Wasm.Component.Lime1Inst.{Retract,Alloc,Prepare,Exports,Bridge,InitType,
CoreEval,Globals,Residue,BridgeG}`;
the statement `Lime1Bridge.InstBridgeE` is in `Silmaril.Wasm.Component.Lime1Bridge.Defs`.

* **`module_retract`**: the Lime1 decoder `Lime1.Module.ofCore?` is a retraction of
  `Lime1.Module.toCore` up to element-segment types: a decoding Core module is the image of its
  decoding once its element segments are typed `funcref` (`Lime1.Elem.ofCore?` also accepts the
  non-null `(ref func)`).
* **`prepare_coreP`**: the copied `Lime1.Execution.prepare_core` (Core `Instantiate` followed by
  the segment programs simulates Lime1 preparation) holds **at every profile** and for **every
  Core module decoding to the Lime1 module**, not only at `Profile.spec` for the image. This is
  the profile transfer of part (a): instead of transferring a run from `Profile.spec`, the run is
  built at the target profile, which needs no grow policy at all.
* **`instantiateDirect_core`** (part (a)): at the deterministic `profile o` the executable
  instantiation is complete, so `instantiateDirect?` of a global-free decoding module computes a
  Core store erasing to the prepared Lime1 store, with a `ModuleInstSim` frame.
* **`exportAddrs_eq`**, `exportFuncAddrs_of_exports` (part (b)): the engine's name-based
  `exportAddrs` are the function addresses of the module's function exports in export order
  (distinct export names, `Simple.Inst.names`), and `exportFuncAddrs` of the Core instance are
  their images, through `ModuleInstSim`.
* **`instBridgeE_noGlobals`**: `InstBridgeE` for the components whose Core module has no
  globals.
* **`instBridgeE`** (part (c)): **`InstBridgeE` holds**, globals included. `instantiateOnce?`
  is `$evalglobals` followed by the direct instantiation of the residue `Module.globalResidue`;
  the Lime1 side splits the same way (`prepare?_residue`), the two `$evalglobals` agree on
  typed initializers (`constExpr?_type`, `evalConst?_toCore`, `evalGlobals_core`), and
  `prepare_runP` relates the residue preparations without validity of the residue (the offsets
  are complete by validity of the module itself).
* **`specSub_lime1`**: the engine-run half `SpecSubOn lime1 lime1G.emb Profile.spec Lime1Dom`
  holds unconditionally; **`refToSpec_lime1_of_machine`**: `RefToSpecLime1` follows from
  the machine half `RefToSpecELime1` alone, and `Simple.sound_lime1_of_machine` gives IR
  soundness over `modSem Profile.spec` on the Lime1 domain from it.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Lime1Inst

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Lime1Ref Silmaril.Wasm.Component.Lime1Bridge
open Silmaril.Wasm.Component.Engine.Lime1 (lime1)

/-- The Core module with every element segment typed `funcref`. -/
abbrev funcrefElems := Silmaril.Proofs.Wasm.Component.Lime1Inst.funcrefElems

/-- **The Lime1 decoder is a retraction up to element types.** -/
theorem module_retract {M : Silmaril.Wasm.Module} {l : Silmaril.Wasm.Lime1.Module}
    (h : Silmaril.Wasm.Lime1.Module.ofCore? M = some l) : l.toCore = funcrefElems M :=
  Silmaril.Proofs.Wasm.Component.Lime1Inst.module_retract h

/-- **Lime1 preparation is Core instantiation followed by the segment programs, at every
profile and for every decoding Core module** `{m.toCore with elems := es}`. -/
theorem prepare_coreP {H : Type} {P : Silmaril.Wasm.Numerics.Profile}
    {tgt : Silmaril.Wasm.Lime1.Execution.ToCore.CHostSemantics H}
    {before : Silmaril.Wasm.Lime1.Execution.Store H} {m : Silmaril.Wasm.Lime1.Module}
    {imports : List Silmaril.Wasm.Execution.Runtime.ExternVal}
    {p : Silmaril.Wasm.Lime1.Execution.Prepared H} {es : List Silmaril.Wasm.Elem}
    (hes : es.map Silmaril.Proofs.Wasm.Component.Lime1Inst.funcrefElem = m.toCore.elems)
    (hvalid : ∃ xtE xtI, Silmaril.Wasm.Validation.ModuleOk { m.toCore with elems := es }
        ⟨xtI, xtE⟩ ∧
      List.Forall₂ (Silmaril.Wasm.Execution.Core.ExternAddrOk before.toCore)
        (imports.map Silmaril.Wasm.Execution.Runtime.ExternVal.toCore) xtI)
    (bounds : Silmaril.Wasm.Lime1.Execution.InstantiationBounds before m)
    (hv : Silmaril.Wasm.Lime1.Validation.ModuleValid m)
    (hp : Silmaril.Wasm.Lime1.Execution.prepare? before m imports = some p) :
    ∃ c S, Silmaril.Wasm.Execution.Core.Instantiate P tgt before.toCore
        { m.toCore with elems := es }
        (imports.map Silmaril.Wasm.Execution.Runtime.ExternVal.toCore) c ∧
      Silmaril.Wasm.Execution.Core.Steps P tgt c
        ⟨S, c.frame, Silmaril.Wasm.Lime1.Execution.startCode m.toCore⟩ ∧
      Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase S = p.store.toCore ∧
      Silmaril.Wasm.Lime1.Execution.ToCore.ModuleInstSim p.module c.frame.module ∧
      c.frame.locals = [] :=
  Silmaril.Proofs.Wasm.Component.Lime1Inst.prepare_coreP hes hvalid bounds hv hp

/-- **The executable instantiation of a global-free decoding module** (no imports, no start
function) computes a Core store erasing to the prepared Lime1 store. -/
theorem instantiateDirect_core {M : Silmaril.Wasm.Module} {l : Silmaril.Wasm.Lime1.Module}
    (hret : l.toCore = funcrefElems M) (hv : Silmaril.Wasm.Lime1.Validation.ModuleValid l)
    (hok : ∃ xtE, Silmaril.Wasm.Validation.ModuleOk M ⟨[], xtE⟩) (hst : M.start = none)
    (bounds : Silmaril.Wasm.Lime1.Execution.InstantiationBounds
      ({} : Silmaril.Wasm.Lime1.Execution.Store Nat) l)
    {p : Silmaril.Wasm.Lime1.Execution.Prepared Nat}
    (hp : Silmaril.Wasm.Lime1.Execution.prepare? {} l [] = some p) :
    ∃ (S : Silmaril.Wasm.Execution.Core.Store Nat) (F : Silmaril.Wasm.Execution.Core.Frame),
      Silmaril.Wasm.Execution.Core.instantiateDirect? (Silmaril.Wasm.Game.importStore []) M [] =
        some (S, F, none) ∧
      Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase S = p.store.toCore ∧
      Silmaril.Wasm.Lime1.Execution.ToCore.ModuleInstSim p.module F.module :=
  Silmaril.Proofs.Wasm.Component.Lime1Inst.instantiateDirect_core hret hv hok hst bounds hp

/-- **The engine's name-based export addresses are the function addresses in export order.** -/
theorem exportAddrs_eq {M : Silmaril.Wasm.Module} {l : Silmaril.Wasm.Lime1.Module}
    (hret : l.toCore = funcrefElems M) (hv : Silmaril.Wasm.Lime1.Validation.ModuleValid l)
    (hg : l.globals = []) {before : Silmaril.Wasm.Lime1.Execution.Store Nat}
    {p : Silmaril.Wasm.Lime1.Execution.Prepared Nat}
    {imports : List Silmaril.Wasm.Execution.Runtime.ExternVal}
    (hp : Silmaril.Wasm.Lime1.Execution.prepare? before l imports = some p) {exps : CoreIface}
    (hnames : funcExportNames M = exps.map (·.1)) {addrs : List lime1.FuncAddr}
    (ha : exportAddrs lime1 p.module exps = some addrs) :
    addrs = Silmaril.Proofs.Wasm.Component.Lime1Inst.funcAddrs p.module.exports :=
  Silmaril.Proofs.Wasm.Component.Lime1Inst.exportAddrs_eq hret hv hg hp hnames ha

/-- **`InstBridgeE` for global-free modules.** -/
theorem instBridgeE_noGlobals (c : Simple) (hD : Lime1Dom c) (hi : c.Inst)
    (hg : c.mod.mod.globals = []) (I : EInstance lime1)
    (hI : instOf lime1 (ofCoreL c.mod.mod) (CoreModule.imports c.mod) (CoreModule.exports c.mod) =
      some I) :
    ∃ I' : Silmaril.Wasm.Game.ScalarInstance, c.mod.IsInst I' ∧ InstSim I I' :=
  Silmaril.Proofs.Wasm.Component.Lime1Inst.instBridgeE_noGlobals c hD hi hg I hI

/-- info: 'Silmaril.Wasm.Component.Lime1Inst.instBridgeE_noGlobals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms instBridgeE_noGlobals

/-- **The Lime1 instantiation bridge** (`Lime1Bridge.InstBridgeE`, proved). -/
theorem instBridgeE : InstBridgeE :=
  Silmaril.Proofs.Wasm.Component.Lime1Inst.instBridgeE_proof

/-- **The engine-run half for Lime1**, unconditionally. -/
theorem specSub_lime1 :
    SpecSubOn lime1 Lime1G.lime1G.emb Silmaril.Wasm.Numerics.Profile.spec Lime1Dom :=
  specSub_of_instBridgeE instBridgeE

/-- **The corrected `RefToSpec lime1G` from the machine half alone.** -/
theorem refToSpec_lime1_of_machine (hR : RefToSpecELime1) : RefToSpecLime1 :=
  refToSpec_lime1_of_E hR instBridgeE

/-- **Soundness of the IR for the reference machine over the Lime1 engine**, on the Lime1
domain, from the machine half alone. -/
theorem Simple.sound_lime1_of_machine (hR : RefToSpecELime1)
    (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple) (hD : Lime1Dom c) (hc : c.Good)
    (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHostE lime1) () (c.toRef.map ofCoreL) []
      c.exports[j].name (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (modSem Silmaril.Wasm.Numerics.Profile.spec))
      ⟨j, by simp [Simple.toComp]⟩ vs b :=
  Simple.sound_lime1_of_E hR instBridgeE prof c hD hc hf hi ha j vs hvs b hb

/-- info: 'Silmaril.Wasm.Component.Lime1Inst.instBridgeE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms instBridgeE

/-- info: 'Silmaril.Wasm.Component.Lime1Inst.refToSpec_lime1_of_machine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refToSpec_lime1_of_machine

end Silmaril.Wasm.Component.Lime1Inst
