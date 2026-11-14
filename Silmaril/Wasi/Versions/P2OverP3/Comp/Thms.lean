module

public import Silmaril.Wasi.Versions.P2OverP3.Comp.Defs
public import Silmaril.Proofs.Wasi.Versions.P2OverP3.Sat

@[expose] public section

/-!
# WASI 0.2 over 0.3: the composite is a model of the loose 0.2 theory (header)

PROVED (proofs in `Silmaril.Proofs.Wasi.Versions.P2OverP3.*`), for every buffer size `cap`:

* **`p2OverP3_sat`**: `(agP clockTh3 (retG (p2Th .loose))).holds (p2OverP3 cap)`. Under the
  WASI 0.3 clock theory on the host's answers, every return of the component satisfies the
  **loose** WASI 0.2 theory `p2Th .loose` (`wasi:io` loose, the monotonic clock, the result
  types of `wasi:cli`/`wasi:clocks`, the filesystem typing). The proof is the invariant method
  of `Silmaril.Wasi.Versions.Stateful` (`wpInv`): the `wasi:io` state of the 0.2 theory is the
  component's own record of its answers, and the 0.2 clock is behind the 0.3 clock.
* **`p2OverP3_model`**: an implementation morphism. For every host `η` (over any lower
  interface) satisfying the WASI 0.3 clock theory, `link η (p2OverP3 cap)` is a host satisfying
  the loose WASI 0.2 theory. `p2OverP3_model_p3`: in particular for every host of the WASI 0.3
  theory `p3Th = typed3 ⊗ clockTh3 ⊗ stdoutTh3`; `p2OverP3_loose`: over its loose host.

What the proof uses of the 0.3 host: only `clockTh3` (for `monotonic-clock.now`). The loose
`wasi:io` theory constrains the 0.2 answers through the component's own bookkeeping (closed
streams, permits, result types, `poll` indices), so it holds whatever the 0.3 streams do; the
typing of the forwarded `wasi:cli`/`wasi:clocks` answers comes from lifting at the WIT type
(`cliFix`), not from `typed3`. The **strict** theory fails
(`Silmaril.Wasi.Versions.P2OverP3.Sep.Thms`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P2
open Silmaril.Wasi.Versions.P3 (clockTh3)

/-- **WASI 0.2 over 0.3 is an implementation morphism** from the loose WASI 0.2 theory to the
WASI 0.3 clock theory. -/
theorem p2OverP3_model (cap : Nat) {Y : Sig.{0}} {η : Host Y imp3}
    (hη : (hostSat clockTh3.Accepts).holds η) :
    (hostSat (p2Th .loose).Accepts).holds (link η (p2OverP3 cap)) :=
  link_model (p2OverP3_sat cap) hη

/-- A host of the WASI 0.3 theory satisfies its clock theory. -/
theorem clock_of_p3 {Y : Sig.{0}} {η : Host Y imp3} (hη : (hostSat p3Th.Accepts).holds η) :
    (hostSat clockTh3.Accepts).holds η := fun s hs =>
  ((Protocol.accepts_prod_iff _ _ _).1 ((Protocol.accepts_prod_iff _ _ _).1 (hη s hs)).2).1

/-- **Over every host of the WASI 0.3 theory**, the composite is a model of the loose WASI 0.2
theory. -/
theorem p2OverP3_model_p3 (cap : Nat) {Y : Sig.{0}} {η : Host Y imp3}
    (hη : (hostSat p3Th.Accepts).holds η) :
    (hostSat (p2Th .loose).Accepts).holds (link η (p2OverP3 cap)) :=
  p2OverP3_model cap (clock_of_p3 hη)

/-- Over the loose host of the WASI 0.3 theory. -/
theorem p2OverP3_loose (cap : Nat) {Y : Sig.{0}} :
    (hostSat (p2Th .loose).Accepts).holds (link (loose (Y := Y) (I := imp3) p3Th) (p2OverP3 cap)) :=
  p2OverP3_model_p3 cap (loose_sat p3Th)

end Silmaril.Wasi.Versions.P2OverP3
