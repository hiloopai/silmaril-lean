module

public import Silmaril.Wasm.Execution.Core.Step

/-!
# SpecTec ↔ Core 3.0, round 7: a run-domain witness with exports (round 5, pass 2)

Round 5, pass 1 left open a concrete point of `Atlas.SpecTecR7Runs.RunDomDetE` whose module
instance exports a name and which takes a step. The candidate is round 5's `expNopCfg` (`nop` in
a frame over a module exporting global `0` as `"g"`). What was missing is an inversion of `nop`
for an arbitrary host: Silmaril's `Step.head_inv` is stated for the empty host `noHost`.

This header fixes the one notion the inversion needs:

* `callFreeA`, `callFreeL`: code with no `call_ref` instruction (`Admin.IsCallRef`) at any depth.
  Only the two host-call rules of `Step` read the host, and both fire at a `call_ref`; so on
  call-free code a step for any host is a step for `noHost` (`Round7.NopEx.step_noHost_of_callFree`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NopEx

open Silmaril.Wasm.Execution.Core

mutual
/-- No `call_ref` inside an administrative instruction, at any depth. -/
def callFreeA : Admin → Bool
  | .plain (.callRef _) => false
  | .callRefType _ => false
  | .label _ _ body => callFreeL body
  | .handler _ _ body => callFreeL body
  | .frame _ _ body => callFreeL body
  | _ => true

/-- No `call_ref` in a sequence of administrative instructions, at any depth. -/
def callFreeL : List Admin → Bool
  | [] => true
  | a :: l => callFreeA a && callFreeL l
end

end Silmaril.Wasm.SpecTec.Sim.Round7.NopEx
