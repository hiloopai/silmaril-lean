module

public import Silmaril.Wasm.Component.Lime1RefE.Defs
public import Silmaril.Wasm.Component.Lime1Inst.Thms
public import Silmaril.Proofs.Wasm.Component.Lime1Bridge.Erase
public import Silmaril.Proofs.Wasm.Component.Reference.CallTyping

/-!
# Typed results of Lime1 export calls

`Lime1RefE.Lime1TypedOk` asks for type soundness of Lime1 export calls on the Lime1 domain.
No Lime1 type soundness theorem is needed: by the instantiation bridge (`Lime1Inst.instBridgeE`)
the Lime1 instance is related by `InstSim` to a Core 3.0 instance `I'` of the module, so a
returned Lime1 run of an export is a returned Core 3.0 run of the same export in `I'`
(`Lime1Bridge.coreRun_of_engineE`, through the copied Lime1 → Core 3.0 simulation), whose
values have the export's result types by Core 3.0 type soundness
(`Reference.run_results_typed`).

* **`lime1Typed_proof`**: `Lime1RefE.Lime1TypedOk`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1Eng

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Lime1Ref
open Silmaril.Wasm.Numerics (Profile)

/-- **Typed results of Lime1 export calls** (`Lime1RefE.Lime1TypedOk`). -/
theorem lime1Typed_proof : Silmaril.Wasm.Component.Lime1RefE.Lime1TypedOk := by
  intro c hD hc hi I hI k nm ft hk a ha xs hxs s' t' ys run hst
  obtain ⟨I', hI', hsim⟩ := Silmaril.Wasm.Component.Lime1Inst.instBridgeE c hD hc hi I hI
  obtain ⟨c', res, run', hc', hr⟩ :=
    Silmaril.Proofs.Wasm.Component.Lime1Bridge.coreRun_of_engineE hsim ha xs run (r := some ys)
      (Or.inl ⟨ys, hst, rfl⟩)
  obtain ⟨hk', hget⟩ := List.getElem?_eq_some_iff.mp hk
  cases res with
  | values vs =>
    have hxs' : xs.map (·.type) = c.mod.exports[k].2.params := by rw [hget]; exact hxs
    have ht := Silmaril.Proofs.Wasm.Component.Reference.run_results_typed (P := Profile.spec) hI'
      hk' hxs' run' hc' hr.symm
    rw [hget] at ht
    exact ht
  | _ => simp at hr

end Silmaril.Proofs.Wasm.Component.Lime1Eng
