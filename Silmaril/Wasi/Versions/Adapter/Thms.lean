module

public import Silmaril.Wasi.Versions.Adapter.Defs
public import Silmaril.Proofs.Wasi.Versions.Adapter.Main

@[expose] public section

/-!
# Preview1 over 0.2: theorems (header)

PROVED (proofs in `Silmaril.Proofs.Wasi.Versions.Adapter.*`, namespace
`Silmaril.Wasi.Versions.Adapter`). The adapter slice `adapter` (a stateful component importing
WASI 0.2.12 and exporting preview1, transcribed from wasmtime's preview1 adapter) is an
**implementation morphism** from preview1 to 0.2:

* **`adapter_sat`**: `(agP p2Th (retG P1.th)).holds adapter`: under the 0.2 theory `p2Th`
  (typing of the imports' answers, the monotonic clock), every return of the adapter satisfies
  the preview1 theory `P1.th` (typing, bounds, monotonic clock, descriptors).
* **`adapter_model`**: for every host `η` (over any lower interface) satisfying `p2Th`,
  `link η adapter` is a host satisfying `P1.th`: a model of the preview1 theory.
* `adapter_loose`: in particular over the loose host of `p2Th`.

The proof is the invariant method for stateful components (`Silmaril.Wasi.Versions.Stateful`),
with the invariant `J`: the preview1 clock state is behind the 0.2 clock state (`clockLe`) and
the descriptor invariant `FdInv` (the descriptors the preview1 theory knows to be open are
open in the adapter's table, those it knows to be closed are closed, and the free list lists
closed entries). Per function: `wp_fdWrite`, `wp_fdRead`, `wp_fdClose`, `wp_pathOpen`,
`wp_clockTimeGet`, `wp_clockResGet`, `wp_randomGet`, `wp_argsGet`, `wp_environGet`,
`wp_procExit`; the clock: `wp_clockTimeGet_clock`, `wp_body_clock`.
-/

namespace Silmaril.Wasi.Versions.Adapter

open Silmaril.Games Silmaril.Wasi

/-- The adapter over the loose host of the 0.2 theory is a preview1 host. -/
theorem adapter_loose {Y : Sig.{0}} :
    (hostSat P1.th.Accepts).holds (link (loose (Y := Y) (I := imports) p2Th) adapter) :=
  adapter_model (Silmaril.Wasi.loose_sat p2Th)

end Silmaril.Wasi.Versions.Adapter
