module

public import Silmaril.Raw.Wasm.SpecTec.Wasm.Binary.Agreement
public import Silmaril.Wasm.Versions.Thms
public import Silmaril.Raw.Wasm.SpecTec.Wasm.Binary.Bridge
public import Silmaril.Raw.Wasm.SpecTec.Wasm.Binary.BridgeInstantiation.Prepare
-- Hand copy: source namespaces kept, only import lines rewritten
-- (imports of other topics' Raw modules go through their public headers).

/-! # Instantiation of the binary-faithful image (`toCoreBinary`)

`Lime1.Execution.Instantiation.toCoreBinary` and `InstantiationDiverges.toCoreBinary`:
the instantiation half of the `toCore`/`toCoreBinary` bridge (validity is in
`Binary/Bridge.lean`).

`m.toCore` and `m.toCoreBinary` differ only in element-segment types
(`Module.toCore_eq_retype`). Rather than relating two Core runs step by step (which
would need the host semantics to be insensitive to element-instance types, since a
Core host call receives the whole store), the proof re-runs the instantiation
simulation of `Lime1/ToCore/Instantiation.lean` on `m.toCoreBinary`:

* validity: `Validation.ModuleValid.toCoreBinary_ok` (`Binary/Bridge.lean`);
* Core instantiation and the segment programs: `prepare_coreBinary`
  (`BridgeInstantiation/Prepare.lean`). The element types only reach the TYPE field
  of the allocated element instances, which `table.init`/`elem.drop` never read and
  `ToCore.Store.erase` forgets;
* the start function and the program run: `start_sim`, `Steps.toCore` and
  `Diverges.toCore` unchanged, since `startCode m.toCoreBinary = startCode m.toCore`
  and the simulation relation `Sim` erases element instances.
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1.Execution

open Silmaril.Wasm.Execution (Runtime.Result Runtime.ExternVal Runtime.ModuleInst)

variable {H : Type}

/-- `Instantiation.toCore` for the binary-faithful image: Lime1 instantiation is
simulated by Core instantiation of `m.toCoreBinary` followed by Core execution. -/
theorem Instantiation.toCoreBinary {src : HostSemantics H} {tgt : ToCore.CHostSemantics H}
    (hosts : HostCompatible src tgt) {before after : Store H} {m : Module}
    {imports : List Runtime.ExternVal} {module : Runtime.ModuleInst} {outcome : Runtime.Result}
    (bounds : InstantiationBounds before m)
    (h : Instantiation src before m imports after module outcome) :
    ∃ c c', Silmaril.Wasm.Execution.Core.Instantiate coreProfile tgt before.toCore
        m.toCoreBinary (imports.map Runtime.ExternVal.toCore) c ∧
      Silmaril.Wasm.Execution.Core.Steps coreProfile tgt c c' ∧
      c'.code = outcome.toCore.toAdmin ∧ ToCore.Store.erase c'.store = after.toCore ∧
      ToCore.ModuleInstSim module c.frame.module ∧ c'.frame.module = c.frame.module := by
  obtain ⟨hv, hi, p, hp, rfl, hrun⟩ := h
  obtain ⟨c, S, hinst, hsteps, hS, hF, hl⟩ := prepare_coreBinary (tgt := tgt) bounds hv hi hp
  obtain ⟨c₁, hsteps₁, hc₁, hsim₁⟩ := start_sim bounds hv hi hp hS hF hl
  obtain ⟨c', hsteps', hsim'⟩ := Steps.toCore hosts hrun hsim₁
  refine ⟨c, c', hinst, (hsteps.trans hsteps₁).trans hsteps', Sim.result hsim' rfl, ?_, hF, ?_⟩
  · obtain ⟨hn, -⟩ := hsim'
    rcases c' with ⟨cs, cf, cl⟩
    exact (ToCore.Config.norm_eq_toCore_iff.mp hn).1
  · rw [coreSteps_frame_module hsteps', hc₁]

/-- `InstantiationDiverges.toCore` for the binary-faithful image. -/
theorem InstantiationDiverges.toCoreBinary {src : HostSemantics H}
    {tgt : ToCore.CHostSemantics H} (hosts : HostCompatible src tgt) {before : Store H}
    {m : Module} {imports : List Runtime.ExternVal} (bounds : InstantiationBounds before m)
    (h : InstantiationDiverges src before m imports) :
    ∃ c, Silmaril.Wasm.Execution.Core.Instantiate coreProfile tgt before.toCore
        m.toCoreBinary (imports.map Runtime.ExternVal.toCore) c ∧
      Silmaril.Wasm.Execution.Core.Diverges coreProfile tgt c := by
  obtain ⟨hv, hi, p, hp, hdiv⟩ := h
  obtain ⟨c, S, hinst, hsteps, hS, hF, hl⟩ := prepare_coreBinary (tgt := tgt) bounds hv hi hp
  obtain ⟨c₁, hsteps₁, -, hsim₁⟩ := start_sim bounds hv hi hp hS hF hl
  exact ⟨c, hinst, InfiniteTrace.of_steps (hsteps.trans hsteps₁)
    (Diverges.toCore hosts hdiv hsim₁)⟩

end Silmaril.Wasm.Lime1.Execution
