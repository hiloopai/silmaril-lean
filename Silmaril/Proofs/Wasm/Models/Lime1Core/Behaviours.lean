module

public import Silmaril.Proofs.Wasm.Models.Lime1Core.Host

/-!
# Lime1 behaviours are Core 3.0 behaviours

* `invoke_sim`: the Lime1 entry configuration of an allocated address in a well-formed store is
  simulated (`Sim` of the copied `Lime1/ToCore/Runtime.lean`) by Core's entry configuration on
  the image store;
* `behaviours_sub`: through the copied `Steps.toCore`, `Sim.result` and `Diverges.toCore`, the
  Lime1 behaviours, read in Core values, are Core behaviours at `Profile.spec`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.Lime1Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Models Silmaril.Wasm.Models.Lime1Core
open Silmaril.Wasm.Models.V10 (LStore LHost HostKeepsL)
open Silmaril.Wasm.Models.V2Core (CStore CHost)

variable {H : Type}

/-- The type of a translated function is the translated type. -/
theorem type_toCore :
    (Silmaril.Wasm.Execution.Core.FuncInst.type ∘
        (FuncInst.toCore : FuncInst Silmaril.Wasm.Lime1.Func H → _)) =
      fun fi => fi.type.toDefType := by
  funext fi
  cases fi <;> rfl

/-- The Core image of the Lime1 entry code is the Core entry code. -/
theorem invoke_code (s : LStore H) (a : FuncAddr) (vs : List Value) :
    Silmaril.Wasm.Lime1.Execution.Admin.listToCore s (invokeL s a vs).code =
      (Silmaril.Wasm.Execution.Core.invoke s.toCore a.value (vs.map Value.toCore)).code := by
  have hv := Silmaril.Wasm.Lime1.Execution.values_toCore s vs
  simp only [Silmaril.Wasm.Lime1.Execution.values] at hv
  simp [invokeL, Silmaril.Wasm.Execution.Core.invoke, Silmaril.Wasm.Lime1.Execution.values,
    Silmaril.Wasm.Lime1.Execution.listToCore_append, hv,
    Silmaril.Wasm.Execution.Runtime.Store.funcDefType,
    Silmaril.Wasm.Execution.Runtime.Store.toCore, type_toCore]

/-- Values and an allocated `invoke` are well formed. -/
theorem listWF_invoke (s : LStore H) (vs : List Value) {a : FuncAddr}
    (ha : a.value < s.funcs.length) :
    Silmaril.Wasm.Lime1.Execution.Admin.listWF s
      (Silmaril.Wasm.Lime1.Execution.values vs ++ [.invoke a]) := by
  induction vs with
  | nil =>
    simp only [Silmaril.Wasm.Lime1.Execution.values, List.map_nil, List.nil_append]
    exact ⟨ha, trivial⟩
  | cons v vs ih =>
    refine ⟨?_, ih⟩
    rcases v with ⟨_ | _, _⟩ <;> trivial

/-- **The entry configurations are simulated.** -/
theorem invoke_sim {s : LStore H} (hwf : Silmaril.Wasm.Lime1.Execution.StoreWF s)
    {a : FuncAddr} (ha : a.value < s.funcs.length) (vs : List Value) :
    Silmaril.Wasm.Lime1.Execution.Sim (invokeL s a vs)
      (Silmaril.Wasm.Execution.Core.invoke s.toCore a.value (vs.map Value.toCore)) := by
  refine ⟨?_, hwf, ?_, ?_⟩
  · rw [Silmaril.Wasm.Lime1.Execution.ToCore.Config.norm_eq_toCore_iff]
    refine ⟨Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase_toCore s, rfl, ?_⟩
    rw [← Silmaril.Wasm.Lime1.Execution.ToCore.Admin.normList_eq_map]
    show _ = Silmaril.Wasm.Lime1.Execution.Admin.listToCore s (invokeL s a vs).code
    rw [invoke_code]
    simp [Silmaril.Wasm.Execution.Core.invoke, Silmaril.Wasm.Execution.Core.vals,
      Silmaril.Wasm.Lime1.Execution.ToCore.Admin.normList_eq_map]
  · intro b hb
    cases hb
  · exact listWF_invoke s vs ha

/-- A Lime1 result read in Core values. -/
theorem result_toBehaviour (r : Result) :
    Behaviour.map Value.toCore r.toBehaviour = (Result.toCore r).toBehaviour := by
  cases r <;> rfl

/-- **Lime1 behaviours are Core 3.0 behaviours** of the image point with the induced host, at
`Profile.spec`. -/
theorem behaviours_sub {s : LStore H} {src : LHost H}
    (hwf : Silmaril.Wasm.Lime1.Execution.StoreWF s)
    (hosts : Silmaril.Wasm.Lime1.Execution.HostCompatible src (liftHostC src))
    {a : FuncAddr} (ha : a.value < s.funcs.length) (vs : List Value) :
    Behaviour.mapSet Value.toCore (behavioursL src s a vs) ⊆
      Silmaril.Wasm.Execution.Core.behaviours Silmaril.Wasm.Numerics.Profile.spec
        (liftHostC src) s.toCore a.value (vs.map Value.toCore) := by
  rintro _ ⟨b, ⟨c', r, hrun, hres, rfl⟩ | ⟨rfl, hdiv⟩, rfl⟩
  · obtain ⟨c₁, hrun₁, hs₁⟩ :=
      Silmaril.Wasm.Lime1.Execution.Steps.toCore hosts hrun (invoke_sim hwf ha vs)
    have hcode := Silmaril.Wasm.Lime1.Execution.Sim.result hs₁ hres
    have hmem := Silmaril.Wasm.Execution.Core.mem_behavioursOf hrun₁ hcode
    rwa [result_toBehaviour]
  · exact Or.inr ⟨rfl,
      Silmaril.Wasm.Lime1.Execution.Diverges.toCore hosts hdiv (invoke_sim hwf ha vs)⟩

end Silmaril.Proofs.Wasm.Models.Lime1Core
