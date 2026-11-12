module

public import Silmaril.Wasm.SpecTec.Sim.FwdMem.Thms
public import Silmaril.Wasm.SpecTec.Sim.RefOk.Thms

/-!
# SpecTec ↔ Core 3.0, round 3 integration: what is left open

After the seven round-3 tracks, `Integrate.Task.wholeStepBounded` reduces, for the concrete
`B := Prims.builtins (Profile.spec nd r) hn host`, to `Round3.Open hn host nd r`:

* `Prims.HostRespects hn host` (a hypothesis on the host);
* `RefOk.ResidueCore`: `Prims.TypeTyping`, the typing of value-type lists and `RefOkBridge`
  (what is left of round 2's `Integrate.Residue`);
* `Aggregates.AggTypes` (what is left of round 2's `Integrate.Extra`);
* `Integrate.RemainingW`: the backward rules no lemma dispatches yet (what is left of
  `Integrate.BwdOpen`);
* the forward direction outside the round-3 fragment `FwdMem.Covered3 true`.

`ResidueCore` and `AggTypes` are refuted as stated, so `Open` is
uninhabited (`Round3.not_open`): the reduction `Round3.wholeStepBounded_of_open` is vacuous. The
target itself is false (`Round3.not_wholeStepBounded`, `Proofs/.../Round3/Refute.lean`); see
`docs/projects/spectec/README.md`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round3

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

/-- **What round 3 leaves open of `Integrate.Task.wholeStepBounded`**, for the concrete `B` at
the profile `Profile.spec nd r`, the encoding `hn` and the host `host`. -/
def Open {H : Type} (hn : H → String) (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice) :
    Prop :=
  Prims.HostRespects hn host ∧
  RefOk.ResidueCore (simEnv (Prims.builtins (Profile.spec nd r) hn host)) ∧
  Aggregates.AggTypes (simEnv (Prims.builtins (Profile.spec nd r) hn host)) ∧
  Integrate.RemainingW (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn
    (Profile.spec nd r) host ∧
  (∀ c c' : Config H, ¬ FwdMem.Covered3 true c → Integrate.StoreOk c.store →
    Typed (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn c →
    Typed (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn c' →
    Step (Profile.spec nd r) host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧
      SStep (simEnv (Prims.builtins (Profile.spec nd r) hn host)) (configV hn c) (configV hn d'))

end Silmaril.Wasm.SpecTec.Sim.Round3
