module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int2.Defs

/-!
# SpecTec ↔ Core 3.0, round 5, track multi (pass 4): definitions

Pass 4 proves pass 2's two hypotheses of the backward multi-step relation for every `B`
(`Round5.Multi.succTyped`, `Round5.Multi.witnessBnd`). This header restates, additively, the
composable one-step simulations without them:

* `MultiOk3`: for every injective encoding, finite `HostOk` host and `Profile.spec nd r`, some
  `B` makes both `Multi.FwdRel` and `Multi.BwdRel` hold. Pass 2's `Multi.MultiOk` and
  `Int2.MultiOk2` assume `SuccTyped` (and `WitnessBnd`) for the backward relation; both imply
  `MultiOk3` (`Round5.Multi.multiOk3_of_multiOk2`, `Round5.Multi.multiOk3_of_multiOk`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Multi

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)

/-- **The composable one-step simulations for the restated target**, with no hypothesis on the
backward relation. -/
def MultiOk3 : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host →
      ∀ (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
        FwdRel B hn (Profile.spec nd r) host ∧ BwdRel B hn (Profile.spec nd r) host

end Silmaril.Wasm.SpecTec.Sim.Round5.Multi
