module

public import Silmaril.Wasm.Component.Lime1Ref.Defs

/-!
# The Lime1 instantiation bridge, restated at the level of stores

The former frozen target `Lime1Ref.Task.instBridge` (#816, removed in the round 2 cleanup; see
docs/projects/logic-inst.md) asked, for the Lime1 instance `I` of a component's module, for a
Core 3.0 instance `I'` such that every Core behaviour of calling an export in the **image store**
`I.store.toCore` is a Core behaviour in `I'.store`. That is a Core-to-Core inclusion of behaviours
between two different stores, so proving it would need a simulation of Core by Core.

The simulation actually used downstream is Lime1 → Core, and the copied Lime1 → Core relation
(`Lime1.Execution.Sim`) does not need the image store: it relates a Lime1 configuration to every
Core configuration whose **erasure** (`Lime1.Execution.ToCore.Store.erase`: segment instances
dropped, module instances erased) is the image. So the bridge can be stated about instantiation
alone:

* `InstSim I I'`: the Lime1 store of `I` is well formed (`Lime1.Execution.StoreWF`), the erasure
  of the Core store of `I'` is its image, and every export address of `I` is allocated and is the
  address of the same export in `I'`;
* **`InstBridgeE`** (frozen, open): every Lime1 instance of a module in the Lime1 domain has
  a Core 3.0 instance `I'` (`NumModule.IsInst`) with `InstSim I I'`.

`InstBridgeE` mentions no execution at all. It is what the copied
`Lime1.Execution.prepare_core` (`Silmaril/Raw/Wasm/Versions/Lime1/ToCore/Instantiation.lean`)
proves for the relational Core `Instantiate` followed by the segment run, under
`InstantiationBounds` (no globals, representable segments), with `ToCore.Store.erase S =
p.store.toCore`. What is missing is the passage from that relational instantiation to the
executable `instantiateOnce?` of `Silmaril.Wasm.Game.IsInstance`, and the globals case.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Lime1Bridge

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Lime1Ref
open Silmaril.Wasm.Component.Engine.Lime1 (lime1)

/-- **The store-level relation of a Lime1 instance and a Core 3.0 instance.** -/
def InstSim (I : EInstance lime1) (I' : Silmaril.Wasm.Game.ScalarInstance) : Prop :=
  Silmaril.Wasm.Lime1.Execution.StoreWF I.store ∧
    Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase I'.store = I.store.toCore ∧
    ∀ (k : Nat) (a : Silmaril.Wasm.Execution.Runtime.FuncAddr), I.addrs[k]? = some a →
      a.value < I.store.funcs.length ∧ I'.addrs.getD k 0 = a.value

/-- **The instantiation bridge at the level of stores** (proved: `Lime1Inst.instBridgeE`): the Lime1 instance of the module
of a component in the Lime1 domain is related by `InstSim` to a Core 3.0 instance of it. -/
def InstBridgeE : Prop :=
  ∀ c : Simple, Lime1Dom c → c.Good → c.Inst → ∀ I : EInstance lime1,
    instOf lime1 (ofCoreL c.mod.mod) (CoreModule.imports c.mod) (CoreModule.exports c.mod) =
      some I →
    ∃ I' : Silmaril.Wasm.Game.ScalarInstance, c.mod.IsInst I' ∧ InstSim I I'

end Silmaril.Wasm.Component.Lime1Bridge
