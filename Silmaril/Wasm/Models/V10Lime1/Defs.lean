module

public import Silmaril.Wasm.Models.Lime1Core.Defs

/-!
# The point map of `v10own → lime1own`

`v10own`'s points are 1.0 stores and hosts; `lime1own`'s are Lime1 stores and hosts. The copied
lock-step simulation `V1.Execution.Step.toLime` (`Silmaril/Raw/Wasm/Versions/Lime1/Execution/FromV1`)
maps a 1.0 run to the Lime1 run of the transported host `limeHost p`. The domains do not match
directly: `v10own` asks the host to preserve the 2.0 simulation's well-formedness
(`ToV2.StoreWF`, page-aligned memories with 32-bit limits), `lime1own` asks it to preserve the
Core simulation's (`Lime1.Execution.StoreWF`) on *every* store that satisfies the latter, which
a host of `v10own` need not do on stores that are not `ToV2.StoreWF`.

* `gate src`: the Lime1 host that answers as `src` does, but only on `ToV2.StoreWF` stores;
* `ptL p`: the point map, the Lime1 store of `p` and the gated transported host.

Every store a Lime1 run reaches from a `ToV2.StoreWF` store is `ToV2.StoreWF` (the copied
`Step.configWF`), so a run never meets the gate.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V10Lime1

open Silmaril.Wasm
open Silmaril.Wasm.Models.V10 (LStore LHost)

/-- **The gated host**: `src` on stores well formed for the 2.0 simulation, nothing elsewhere. -/
def gate {H : Type} (src : LHost H) : LHost H := fun h s vs out =>
  src h s vs out ∧ Silmaril.Wasm.Lime1.Execution.ToV2.StoreWF s

/-- **The point map `v10own → lime1own`**: the Lime1 store and the gated transported host. -/
def ptL {H : Type} (p : V10.Pt H) : Lime1Core.Pt H := (V10.limeStore p, gate (V10.limeHost p))

end Silmaril.Wasm.Models.V10Lime1
