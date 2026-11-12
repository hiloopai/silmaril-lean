module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.BwdWitness10T
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.ResCore10

/-!
# The backward half with stores along V1 runs (track v10)

`GoodV1` now follows from Core typing and V1's `StoreOk10` along V1 runs (`goodV1_steps'`), and
the backward half in `simEnv10T` needs only `GoodV1` (`wholeStepBwd10S`). Together:

* **`bwd10S_steps`**: from a `CoreTyped10` configuration whose store has no host function and
  satisfies `StoreOk10`, at every configuration a V1 run reaches, every step of the corrected
  1.0 script from its image is the image of a V1 step. Stores may occur in the code and in the
  stored functions.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Config HostSemantics Step Steps)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.Valid (CoreTyped10 goodV1_steps')

variable {H : Type}

/-- **The backward half with stores, along V1 runs from a Core-typed configuration.** -/
theorem bwd10S_steps {hn : H → String} {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    {c d : Config H} (h : Steps host c d) (hnh : NoHost10 c.store) (hs : StoreOk10 c.store)
    (hc : CoreTyped10 c) {w : Value}
    (hw : SStepB (simEnv10T (fwdB10 nd r)) (configV hn d) w) :
    ∃ d', w = configV hn d' ∧ Step host d d' :=
  wholeStepBwd10S (goodV1_steps' h hnh hs hc) hw

end Silmaril.Wasm.SpecTec.Sim10.Whole
