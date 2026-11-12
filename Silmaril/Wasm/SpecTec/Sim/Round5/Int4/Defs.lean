module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Defs

/-!
# SpecTec ↔ Core 3.0, round 5, pass-4 integration: definitions

Track multi (pass 4) proves the two backward multi-step hypotheses `Multi.SuccTyped` and
`Int2.WitnessBnd` for every `B`; track target (pass 4) restates the composable one-step
simulations on `FloatMissel`-free runs as `Target.MultiSel`, still carrying those hypotheses on
its backward half. This header states, additively, `MultiSel` without them:

* `MultiSel3`: for every injective encoding, finite `HostOk` host and `Profile.spec nd r`, some
  `B` makes both `Target.FwdRelSel` and `Target.BwdRelSel` hold.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Int4

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)

/-- **The composable one-step simulations on `FloatMissel`-free runs**, with no hypothesis on
the backward relation (`Target.MultiSel` without `SuccTyped`, `WitnessBnd`). -/
def MultiSel3 : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host →
      ∀ (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
        Target.FwdRelSel B hn (Profile.spec nd r) host ∧
          Target.BwdRelSel B hn (Profile.spec nd r) host

end Silmaril.Wasm.SpecTec.Sim.Round5.Int4
