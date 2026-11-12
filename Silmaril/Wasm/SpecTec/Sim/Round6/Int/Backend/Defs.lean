module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Defs

/-!
# SpecTec ↔ Core 3.0, round 6, integration (pass 2): the restricted target

Pass 2 of round 6 (`docs/projects/spectec/README.md`) proved the transfer
half of `Target.OpenR Int.backend` and the cast half only from `Reading.RefOkBB`, which is false.
This topic states what is proved instead:

* `NoCastReach P host c`: no Core configuration reachable from `c` has a cast redex.
* `wholeStepValidRNC Rd`: `Round6.Task.wholeStepValidR Rd` with `¬ Target.CastRedex c.code`
  added to the hypotheses of both halves. Not a frozen `Task`: it is proved at `Int.backend`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Int

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)

variable {H : Type}

/-- **No Core configuration reachable from `c` has a cast redex** (`Target.CastRedex`): casts
may occur in the code, but none is ever the next instruction to execute. -/
def NoCastReach (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  ∀ c', Steps P host c c' → ¬ Target.CastRedex c'.code

/-- **`Round6.Task.wholeStepValidR` away from cast redexes**: the same statement with
`¬ Target.CastRedex c.code` added to the hypotheses of both halves. Implied by the full target
(`wholeStepValidRNC_of_wholeStepValidR`), proved at the backend reading
(`wholeStepValidRNC_backend`). -/
def wholeStepValidRNC (Rd : Target.Reading) : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host →
      ∀ (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
        (∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → Round5.Target.BoundedSel c →
          ¬ Target.CastRedex c.code →
          (∀ c₁, Step (Profile.spec nd r) host c c₁ → Round5.Target.BoundedSel c₁) →
          Step (Profile.spec nd r) host c c' →
          ∃ c'', Step (Profile.spec nd r) host c c'' ∧
            ((∀ c₃, Step (Profile.spec nd r) host c c₃ → c₃ = c') → c'' = c') ∧
            ∃ d', Bwd.ConfigEq c'' d' ∧ Rd.step B (configV hn c) (configV hn d')) ∧
        (∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
          Round5.Target.BoundedSel c → ¬ Target.CastRedex c.code → Rd.step B (configV hn c) w →
          ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step (Profile.spec nd r) host c c')

end Silmaril.Wasm.SpecTec.Sim.Round6.Int
