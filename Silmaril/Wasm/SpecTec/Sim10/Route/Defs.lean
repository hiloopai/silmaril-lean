module

public import Silmaril.Wasm.SpecTec.Sim20.Route.Defs
public import Silmaril.Wasm.SpecTec.Sim20.StepFix.Defs
public import Silmaril.Wasm.Versions.Thms

/-!
# The 1.0 composite routes, as statements

`Sim20.Task.composite20` takes a V2 step through a translation into Core 3.0 (Track E's
obligation) and then into the wasm-3.0 script. The 1.0 routes have the same shape. A V1
step goes through the copied 1.0 → Lime1 → 2.0 simulation (`V1.Execution.Step.toV2`, a non-empty run
of V2 steps along `Lime1.Execution.ToV2.Sim`, at `v2Profile = Profile.spec`), and then:

* **`Task.composite10`, 1.0 → the 2.0 script.** Each V2 step goes to the wasm-2.0 script. The
  2.0 forward half is proved only on fragments (`Sim20.Whole.wholeStepCtxS20` and its siblings), so
  it is a hypothesis of the statement (`Fwd20`), as Track E's obligation is for `composite20`. The
  2.0 script is the one with the `Step` erratum (`Sim20.StepFix.simEnv20S`): without it the forward
  half is refuted below the top of the code (`Sim20.Whole.not_fwd_noCtxt`).
* **`Task.composite10T`, 1.0 → the 3.0 script, with a non-empty run.** Each V2 step goes through
  the copied V2 → Core 3.0 simulation (`V2.Execution.Step.toCore`, relation `V2.Execution.Sim`),
  then through Round 6 along `SimRel` (`Sim20.stepsT_sim`). This needs no hypothesis beyond
  `composite20`'s `RunGood` at the Core image. `Sim20.composite10_steps` already gave the
  possibly-empty (`RSteps`) form for 1.0 runs.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Lime1.Execution (v2Profile)
open Silmaril.Wasm.SpecTec.Sim (HostFinite)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

variable {H : Type}

/-- **The 2.0 forward obligation** on a set `Good` of V2 configurations: every V2 step from a good
configuration is a non-empty run of the corrected wasm-2.0 script between the images. -/
def Fwd20 (hn : H → String) (host20 : V2.Execution.HostSemantics H) (B : Builtins)
    (Good : V2.Execution.Config H → Prop) : Prop :=
  ∀ c c', Good c → V2.Execution.Step v2Profile host20 c c' →
    Relation.TransGen (SStepB (Sim20.StepFix.simEnv20S B)) (Sim20.configV hn c)
      (Sim20.configV hn c')

/-- Every V2 configuration reachable from `c` is good. -/
def RunGood20 (host20 : V2.Execution.HostSemantics H) (Good : V2.Execution.Config H → Prop)
    (c : V2.Execution.Config H) : Prop :=
  ∀ c₁, V2.Execution.Steps v2Profile host20 c c₁ → Good c₁

/-- **The 1.0 → 2.0-script composite route** (frozen; proved in `Sim10.Route.Thms`): given the
2.0 forward obligation on `Good`, every V1 step from a configuration simulated by a V2
configuration all of whose successors are good is matched by a non-empty run of the corrected
wasm-2.0 script between the images, ending at a V2 configuration that simulates the V1
successor. -/
def Task.composite10 : Prop :=
  ∀ (H : Type) (hn : H → String) (src : V1.Execution.HostSemantics H)
    (tgt : V2.Execution.HostSemantics H) (B : Builtins) (Good : V2.Execution.Config H → Prop),
    Lime1.Execution.ToV2.HostCompatible (src.mapCode V1.Func.toLime) tgt → Fwd20 hn tgt B Good →
    ∀ (a b : V1.Execution.Config H) (c : V2.Execution.Config H), V1.Execution.Step src a b →
      Lime1.Execution.ToV2.Sim a.toLime c → RunGood20 tgt Good c →
      ∃ c', Lime1.Execution.ToV2.Sim b.toLime c' ∧
        Relation.TransGen (SStepB (Sim20.StepFix.simEnv20S B)) (Sim20.configV hn c)
          (Sim20.configV hn c')

/-- **The 1.0 → 3.0-script composite route, non-empty** (frozen; proved in `Sim10.Route.Thms`):
there are builtins `B` such that every V1 step, from a configuration simulated through 2.0 by a
Core configuration that only reaches good configurations, is matched, up to `Bwd.ConfigEq`, by a
non-empty run of wasm-3.0 backend steps from the Core image. -/
def Task.composite10T : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : Execution.Core.HostSemantics H), HostFinite host → Execution.Core.HostOk host →
      ∀ (src : V1.Execution.HostSemantics H) (tgt : V2.Execution.HostSemantics H),
        Lime1.Execution.ToV2.HostCompatible (src.mapCode V1.Func.toLime) tgt →
        V2.Execution.HostCompatible tgt host →
        ∃ B : Builtins, ∀ (a b : V1.Execution.Config H) (e : V2.Execution.Config H)
          (c : Execution.Core.Config H), V1.Execution.Step src a b →
          Lime1.Execution.ToV2.Sim a.toLime e → V2.Execution.Sim e c →
          Sim20.RunGood Profile.spec host c →
          ∃ e' c' d, Lime1.Execution.ToV2.Sim b.toLime e' ∧ V2.Execution.Sim e' c' ∧
            Sim.Bwd.ConfigEq c' d ∧
            Relation.TransGen (Sim.Round6.Int.backend.step B) (Sim.configV hn c)
              (Sim.configV hn d)

end Silmaril.Wasm.SpecTec.Sim10
