module

public import Silmaril.Wasm.Component.Reference.Core3Sem.Defs
public import Silmaril.Wasm.Component.Semantics.Thms
public import Silmaril.Wasm.Component.Pipeline.Defs
import Silmaril.Proofs.Wasm.Component.Reference.Core3Sem

/-!
# Core 3.0 instances as a core semantics: theorems

* `core3Sem_le`, `denU_core3Sem_le`: if every host-free Core step of profile `P` is one of
  `Q`, then `core3Sem P` refines `core3Sem Q`, and so does the denotation of every component
  over numeric Core 3.0 instances;
* `denU_core3Sem_profile_le_spec`: in particular a component's denotation at a deterministic
  profile `profile o` refines its denotation at the spec profile;
* `optimizeComponent_sound_core3`: the component optimiser preserves the denotation of every
  component over numeric Core 3.0 instances, at every profile.

Not shown: that `Comp.den (core3Sem P)` agrees with the reference machine
(`Silmaril.Wasm.Component.Reference.exportBehaviours` over `core3P P`) on components that both
can express; see `docs/projects/wasm-components.md`.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.Core3Sem`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Game
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Config Step)

/-- `core3Sem` is monotone in the profile. -/
theorem core3Sem_le {P Q : Profile}
    (hPQ : ∀ c c' : Config Nat,
      Silmaril.Games.Step P Silmaril.Wasm.SingleThreaded.Det.noHost c c' →
        Silmaril.Games.Step Q Silmaril.Wasm.SingleThreaded.Det.noHost c c') :
    (core3Sem P).Le (core3Sem Q) :=
  Silmaril.Proofs.Wasm.Component.Reference.core3Sem_le hPQ

/-- Component denotations over Core 3.0 instances are monotone in the profile. -/
theorem denU_core3Sem_le {P Q : Profile}
    (hPQ : ∀ c c' : Config Nat,
      Silmaril.Games.Step P Silmaril.Wasm.SingleThreaded.Det.noHost c c' →
        Silmaril.Games.Step Q Silmaril.Wasm.SingleThreaded.Det.noHost c c')
    (c : Comp NumInstance) : c.denU (core3Sem P) ≤ c.denU (core3Sem Q) :=
  Silmaril.Proofs.Wasm.Component.Reference.denU_core3Sem_le hPQ c

/-- At a deterministic profile, a component's denotation refines the spec-profile one. -/
theorem denU_core3Sem_profile_le_spec (o : Silmaril.Wasm.SingleThreaded.GrowOracle)
    (c : Comp NumInstance) :
    c.denU (core3Sem (Silmaril.Wasm.SingleThreaded.profile o)) ≤
      c.denU (core3Sem (Silmaril.Wasm.Numerics.Profile.spec false {})) :=
  Silmaril.Proofs.Wasm.Component.Reference.denU_core3Sem_profile_le_spec o c

/-- The component optimiser is sound for components over Core 3.0 instances, at every
profile. -/
theorem optimizeComponent_sound_core3 (P : Profile) (c : Comp NumInstance) :
    (optimizeComponent c).denU (core3Sem P) = c.denU (core3Sem P) ∧
      (optimizeComponent c).imports.length = c.imports.length ∧
      (optimizeComponent c).exports.length = c.exports.length :=
  Silmaril.Proofs.Wasm.Component.Reference.optimizeComponent_sound_core3 P c

end Silmaril.Wasm.Component.Reference
