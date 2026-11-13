module

public import Silmaril.Wasm.Component.Lime1RT.Thms
public import Silmaril.Proofs.Wasm.Component.Lime1RT.Inst.Instance

/-!
# Core 3.0 restricted to Lime1 at runtime: Lime1 modules

`Lime1RT.core3LRG_sem_eq` assumes that the Core 3.0 instance store of the module is of `lime1`
(`Rt.StoreIn lime1`). This file discharges that hypothesis for every module of `lime1`:

* `Inst.prepareE?_funcs`: instantiation (`prepareE?`: `$evalglobals`, allocation of the global-free
  residue, direct segment initialisation) appends to the store's function instances exactly Wasm
  functions of the module. Constant evaluation (`evalGlobals?`, `evalExprs?`, `evalExprss?`) and
  the host-free segment-initialisation run keep the function instances; `$allocmodule` appends
  one instance per module function (`allocModule?_inv`);
* `Inst.instOf_storeIn`: the Core 3.0 engine instance of a module of `S` has a store of `S`
  (host allocation adds only host functions);
* **`core3LRG_sem_eq_of_inFeat`**: on every module of `lime1`, the game semantics of the runtime
  restriction `core3LRG P` is that of Core 3.0, with no further hypothesis.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Lime1RT

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Numerics (Profile)

/-- **The Core 3.0 instance of a module of `S` has a store of `S`.** -/
theorem instOf_storeIn {S : Silmaril.Wasm.Models.FeatureSet} (P : Profile)
    {m : Silmaril.Wasm.Module} (hm : Silmaril.Wasm.Models.Module.InFeat S m)
    {imps exps : CoreIface} {I : EInstance (core3P P)}
    (h : instOf (core3P P) m imps exps = some I) :
    Silmaril.Wasm.Models.Rt.StoreIn S (H := Nat) I.store :=
  Silmaril.Proofs.Wasm.Component.Lime1RT.Inst.instOf_storeIn P hm h

/-- **On every module of `lime1`, the runtime restriction to `lime1` is Core 3.0** at the game
level: `core3LRG_sem_eq` with its store hypothesis discharged. -/
theorem core3LRG_sem_eq_of_inFeat (P : Profile) (m : NumModule)
    (hm : Silmaril.Wasm.Models.Module.InFeat Silmaril.Wasm.Models.lime1 m.mod) :
    (core3LRG P).sem.sem m = (core3G P).sem.sem m :=
  core3LRG_sem_eq P m fun _ h => instOf_storeIn P hm h

/-! The axiom audit. -/

/--
info: 'Silmaril.Wasm.Component.Lime1RT.core3LRG_sem_eq_of_inFeat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms core3LRG_sem_eq_of_inFeat

end Silmaril.Wasm.Component.Lime1RT
