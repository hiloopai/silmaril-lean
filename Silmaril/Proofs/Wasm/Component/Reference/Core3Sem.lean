module

public import Silmaril.Wasm.Component.Reference.Core3Sem.Defs
public import Silmaril.Wasm.Component.Semantics.Thms
import all Silmaril.Wasm.Component.Semantics.Thms
public import Silmaril.Wasm.Component.Pipeline.Thms
public import Silmaril.Wasm.Game.Strategy.Thms

/-!
# Core 3.0 instances as a core semantics: proofs

Monotonicity of `core3Sem` in the profile (from `ScalarInstance.strategy_mono`), its
consequences for component denotations (`denU_mono`), and the optimiser's soundness
(`optimizeComponent_sound'`) instantiated at `core3Sem P`.
-/

public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Game
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Config Step)

theorem core3Sem_le {P Q : Profile}
    (hPQ : ∀ c c' : Config Nat, Step P Silmaril.Wasm.SingleThreaded.Det.noHost c c' → Step Q Silmaril.Wasm.SingleThreaded.Det.noHost c c') :
    (core3Sem P).Le (core3Sem Q) := fun (m : NumInstance) =>
  Strategy.comp_mono le_rfl
    (Strategy.comp_mono (m.inst.strategy_mono hPQ m.inst.store) le_rfl)

theorem denU_core3Sem_le {P Q : Profile}
    (hPQ : ∀ c c' : Config Nat, Step P Silmaril.Wasm.SingleThreaded.Det.noHost c c' → Step Q Silmaril.Wasm.SingleThreaded.Det.noHost c c')
    (c : Comp NumInstance) : c.denU (core3Sem P) ≤ c.denU (core3Sem Q) :=
  denU_mono (core3Sem_le hPQ) c

theorem denU_core3Sem_profile_le_spec (o : Silmaril.Wasm.SingleThreaded.GrowOracle)
    (c : Comp NumInstance) :
    c.denU (core3Sem (Silmaril.Wasm.SingleThreaded.profile o)) ≤
      c.denU (core3Sem (Silmaril.Wasm.Numerics.Profile.spec false {})) :=
  denU_core3Sem_le (fun _ _ h => Silmaril.Wasm.Execution.Core.Step.deterministic_refines h) c

theorem optimizeComponent_sound_core3 (P : Profile) (c : Comp NumInstance) :
    (optimizeComponent c).denU (core3Sem P) = c.denU (core3Sem P) ∧
      (optimizeComponent c).imports.length = c.imports.length ∧
      (optimizeComponent c).exports.length = c.exports.length :=
  optimizeComponent_sound' (core3Sem P) c

end Silmaril.Proofs.Wasm.Component.Reference
