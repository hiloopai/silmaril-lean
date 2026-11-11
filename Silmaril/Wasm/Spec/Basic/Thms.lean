module

public import Silmaril.Wasm.Spec.Basic.Defs
public import Silmaril.Proofs.Wasm.Spec.Basic.Basic

@[expose] public section

/-!
# The simple specification logics: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Basic.Basic`.

* `activeExport_concat`: the pending export after one more event.
* `NeverCall.holds_of_prefix`, `CallPre.holds_of_prefix`, `NeverCallFrom.holds_of_prefix`,
  `RetPost.holds_of_prefix`: the simple properties are safety properties (prefix closed);
  `ofTrace_sat_prefixesOf_iff`: on the prefixes of one trace, such a property holds iff it holds
  of the trace (used by the litmus tests).
* **Closed-world grounding** (every profile `P`): `retPost_closed_world`: if a Wasm program
  satisfies the return postcondition `Q` of export `j` in `inst (retPost …) (wasmSem P)`, every
  terminating Core behaviour of a call of `j` against any stateful, nondeterministic host machine
  satisfies `Q` (via adequacy M2 for stateful hosts); `retPost_behaviours`: the same for the
  Core behaviours `behaviours P (hostOf X.imports K)` under a stateless host.
-/
