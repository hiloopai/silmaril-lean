module

public import Silmaril.Wasm.FnInst.Ground.Check.Defs
public import Silmaril.Wasm.Execution.Core.Sim.CodeRel

@[expose] public section

/-! # Linking `checkInst` sentences to the grounded bridges

`checkInst` (`Silmaril.Wasm.FnInst.Ground.Check`) reads wasm-check's statements
`ModRefines`/`ModEquiv`: invocations of export `j` in the **computed instance** `instOf m`
(`Silmaril.Wasm.Verify.instance?`: `instantiateOnce?` against fresh host functions, no start
function), under `Det.noHost`. The bridges (`gBaseSim`, `wDeferredSim`) give silmaril's
`Binaryen.ExportRefines`/`ExportEquiv`: every spec instantiation (`Instantiate`), from every
valid store and import list, under `closedHost`. The two hosts are the same function
(`fun _ _ _ _ => False`); the instances differ (`instantiateOnce?` allocates each global
once, the spec's `$instantiate` twice).

`InstRel BI m m'`: the computed instances of `m` and `m'` agree up to `FuncRel BI`-related
function bodies, with the same export addresses. Under it, the code simulations behind the
bridges give the `checkInst` sentences directly (`Silmaril.Wasm.FnInst.Ground.Link.Thms`).
-/

namespace Silmaril.Wasm.FnInst.Ground.Check

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.Verify (instOf)

/-- The computed instances agree up to related function bodies. -/
def InstRel (BI : List Instr → List Instr → Prop) (m m' : Module) : Prop :=
  StoreRel (FuncRel BI) (instOf m).store (instOf m').store ∧ (instOf m).addrs = (instOf m').addrs

end Silmaril.Wasm.FnInst.Ground.Check
