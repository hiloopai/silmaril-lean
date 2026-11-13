module

public import Silmaril.Wasm.Models.V10Lime1.Defs

/-!
# Lime1 runs from well-formed stores never meet the gate

* `Step.gate`: a Lime1 step under `src` from a `ToV2.StoreWF` store is a step under `gate src`;
* `Steps.gate`, `Diverges.gate`: finite runs and infinite traces under `src` from a
  `ToV2.StoreWF` store are runs under `gate src`, when `src` preserves `ToV2.StoreWF`
  (the invariant is the copied `Step.configWF`);
* `invoke_toLime`: the Lime1 image of the 1.0 entry configuration is the Lime1 entry
  configuration of the image store;
* **`behaviours_sub`**: the 1.0 behaviours of a point are Lime1 behaviours of `ptL p`.

New proofs over the copied 1.0 → Lime1 simulation.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V10Lime1

open Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V10Lime1
open Silmaril.Wasm.Models.V10 (LStore LHost)

variable {H : Type}

/-- The constructors of a Lime1 step that do not consult the host: rebuild the step. -/
local macro "gate_step" : tactic => `(tactic|
  first
    | (apply Silmaril.Wasm.Lime1.Execution.Step.pure ; assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.localGet ; assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.localSet <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.globalGet <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.globalSet <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.call ; assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.callIndirect <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.callIndirectBounds <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.callIndirectNull <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.callIndirectType <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.invokeWasm <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.intLoad <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.intLoadTrap <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.floatLoad <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.floatLoadTrap <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.intStore <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.intStoreTrap <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.floatStore <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.floatStoreTrap <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.memorySize <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.memoryGrow <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.memoryCopy <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.memoryCopyTrap <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.memoryFill <;> assumption)
    | (apply Silmaril.Wasm.Lime1.Execution.Step.memoryFillTrap <;> assumption))

/-- A step from a well-formed store is a step under the gated host. -/
theorem Step.gate {src : LHost H} {a b : Silmaril.Wasm.Lime1.Execution.Config H}
    (h : Silmaril.Wasm.Lime1.Execution.Step src a b)
    (hwf : Silmaril.Wasm.Lime1.Execution.ToV2.StoreWF a.store) :
    Silmaril.Wasm.Lime1.Execution.Step (V10Lime1.gate src) a b := by
  induction h with
  | context _ vs tail ih => exact .context (ih hwf) vs tail
  | label _ n cont ih => exact .label (ih hwf) n cont
  | frame _ n outer ih => exact .frame (ih hwf) n outer
  | invokeHost s s' f a ft fn args r found arity behavior =>
    exact .invokeHost s s' f a ft fn args r found arity ⟨behavior, hwf⟩
  | invokeHostDiverges s f a ft fn args found arity behavior =>
    exact .invokeHostDiverges s f a ft fn args found arity ⟨behavior, hwf⟩
  | _ => gate_step

/-- Finite runs from a well-formed store are runs under the gated host, and stay well formed. -/
theorem Steps.gate {src : LHost H} (hp : Silmaril.Wasm.Lime1.Execution.ToV2.HostPreserves src)
    {a b : Silmaril.Wasm.Lime1.Execution.Config H}
    (h : Silmaril.Wasm.Lime1.Execution.Steps src a b)
    (hwf : Silmaril.Wasm.Lime1.Execution.ToV2.StoreWF a.store) :
    Silmaril.Wasm.Lime1.Execution.Steps (V10Lime1.gate src) a b ∧
      Silmaril.Wasm.Lime1.Execution.ToV2.StoreWF b.store := by
  induction h with
  | refl => exact ⟨.refl, hwf⟩
  | tail _ step ih =>
    obtain ⟨hrun, hmid⟩ := ih
    exact ⟨hrun.tail (Step.gate step hmid), Silmaril.Wasm.Lime1.Execution.Step.configWF hp step hmid⟩

/-- Infinite traces from a well-formed store are traces under the gated host. -/
theorem Diverges.gate {src : LHost H} (hp : Silmaril.Wasm.Lime1.Execution.ToV2.HostPreserves src)
    {a : Silmaril.Wasm.Lime1.Execution.Config H}
    (h : Silmaril.Wasm.Lime1.Execution.Diverges src a)
    (hwf : Silmaril.Wasm.Lime1.Execution.ToV2.StoreWF a.store) :
    Silmaril.Wasm.Lime1.Execution.Diverges (V10Lime1.gate src) a := by
  refine InfiniteTrace.coinduct
    (fun c => Silmaril.Wasm.Lime1.Execution.Diverges src c ∧
      Silmaril.Wasm.Lime1.Execution.ToV2.StoreWF c.store) ?_ ⟨h, hwf⟩
  rintro c ⟨hc, hcwf⟩
  obtain ⟨d, step, hd⟩ := hc.unfold
  exact ⟨d, Step.gate step hcwf, hd, Silmaril.Wasm.Lime1.Execution.Step.configWF hp step hcwf⟩

/-- The Lime1 image of the 1.0 entry configuration. -/
theorem invoke_toLime (s : V10.OStore H) (a : FuncAddr) (vs : List Value) :
    (Silmaril.Wasm.V1.Execution.invoke s a vs).toLime =
      Lime1Core.invokeL (s.mapCode Silmaril.Wasm.V1.Func.toLime) a vs := by
  simp [Silmaril.Wasm.V1.Execution.invoke, Lime1Core.invokeL,
    Silmaril.Wasm.V1.Execution.Config.toLime, AdminInstr.map]

/-- **The 1.0 behaviours of a point are Lime1 behaviours of its image.** -/
theorem behaviours_sub {p : V10.Pt H} (hp : V10.dom p) (a : FuncAddr) (vs : List Value) :
    Silmaril.Wasm.V1.Execution.behaviours p.2 p.1 a vs ⊆
      Lime1Core.behavioursL (ptL p).2 (ptL p).1 a vs := by
  have hcompat := Silmaril.Wasm.Execution.Runtime.HostSemantics.compatible_mapCode
    Silmaril.Wasm.V1.Func.toLime p.2
  have hwf : Silmaril.Wasm.Lime1.Execution.ToV2.StoreWF
      (Lime1Core.invokeL (V10.limeStore p) a vs).store := hp.1
  rintro _ (⟨c', r, hrun, hres, rfl⟩ | ⟨rfl, hdiv⟩)
  · have hrunL := Silmaril.Wasm.V1.Execution.Steps.toLime hcompat hrun
    rw [invoke_toLime] at hrunL
    refine Or.inl ⟨c'.toLime, r, (Steps.gate hp.2.1 hrunL hwf).1, ?_, rfl⟩
    simp [Silmaril.Wasm.V1.Execution.Config.toLime, hres]
  · have hdivL := Silmaril.Wasm.V1.Execution.Diverges.toLime hcompat hdiv
    rw [invoke_toLime] at hdivL
    exact Or.inr ⟨rfl, Diverges.gate hp.2.1 hdivL hwf⟩

end Silmaril.Proofs.Wasm.Models.V10Lime1
