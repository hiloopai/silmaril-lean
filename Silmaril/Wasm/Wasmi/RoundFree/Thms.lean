module

public import Silmaril.Wasm.Wasmi.RoundFree.Defs
public import Silmaril.Wasm.Wasmi.Observed.Thms
public import Silmaril.Proofs.Wasm.Wasmi.RoundFree.Equal

/-!
# The wasmi 0.40.0 model is Core 3.0 on code without rounding operators

Proofs in `Silmaril.Proofs.Wasm.Wasmi.RoundFree.{Preserve,Equal}`.

At **every** profile `P` (the statement does not depend on the NaN policy or on any other part
of the profile):

* `step_iff`: from code without scalar rounding operators (`rfAs`), a step of the wasmi 0.40.0
  model is exactly a Core 3.0 step;
* `step_free`: a Core 3.0 step keeps a `Free` configuration free, under a host that keeps
  stores free (`HostKeeps`; every host over `Empty`, `hostKeeps_empty`);
* `behaviours_eq`, **`obs_eq`**: the model and Core 3.0 have the same observations (finite
  results and divergence) from a free configuration, and on every call at a point whose store
  has no rounding operator in any Wasm function;
* `three_agree`: at a point whose store is free and has no instance of wasmi 2.0.0's fused
  pattern (`Wasmi.StorePatFree`), Core 3.0, wasmi 0.40.0 and wasmi 2.0.0 have the same
  observations;
* `repro_obs`: on issue #2046 the wasmi 0.40.0 model returns `7` and **has no other
  observation** (the reproducer has no rounding operator, and Core returns exactly `7`).

The condition is on scalar `ceil`, `floor`, `trunc`, `nearest` only, as is the model's quirk:
the vector rounding operators are not flagged (wasmi 0.40.0 has no SIMD support; the model does
not change them).
-/

@[expose] public section

namespace Silmaril.Wasm.Wasmi.RoundFree

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas

variable {H : Type}

/-- **A step of the wasmi 0.40.0 model from code without rounding operators is a Core step.** -/
theorem step_iff (P : Profile) (host : HostSemantics H) {c c' : Config H}
    (hc : rfAs c.code = true) : Observed.Step P host c c' ↔ Execution.Core.Step P host c c' :=
  Silmaril.Proofs.Wasm.Wasmi.RoundFree.step_iff hc

/-- **Core 3.0 steps keep configurations free of rounding operators.** -/
theorem step_free (P : Profile) {host : HostSemantics H} (hh : HostKeeps host) {c c' : Config H}
    (h : Execution.Core.Step P host c c') (hc : Free c) : Free c' :=
  Silmaril.Proofs.Wasm.Wasmi.RoundFree.step_free hh h hc

/-- Every host over `Empty` keeps stores free (it has no host functions). -/
theorem hostKeeps_empty (host : HostSemantics Empty) : HostKeeps host :=
  Silmaril.Proofs.Wasm.Wasmi.RoundFree.hostKeeps_empty host

/-- **The wasmi 0.40.0 model equals Core 3.0 from a free configuration.** -/
theorem behaviours_eq (P : Profile) {host : HostSemantics H} (hh : HostKeeps host)
    {c : Config H} (hc : Free c) :
    Variant.behavioursR (Observed.Step P host) c = behavioursOf P host c :=
  Silmaril.Proofs.Wasm.Wasmi.RoundFree.behaviours_eq hh hc

/-- **The wasmi 0.40.0 model equals Core 3.0 on every call of a store without rounding
operators**, at every profile. -/
theorem obs_eq (P : Profile) {x : Core.Pt H} (hs : StoreFree x.1) (hh : HostKeeps x.2)
    (c : Core.Call) : Observed.obs P x c = Core.obs P x c :=
  Silmaril.Proofs.Wasm.Wasmi.RoundFree.obs_eq P hs hh c

/-- **Core 3.0, wasmi 0.40.0 and wasmi 2.0.0 agree** at a point whose store has neither a
rounding operator nor wasmi 2.0.0's fused pattern. -/
theorem three_agree (P : Profile) {x : Core.Pt H} (hs : StoreFree x.1)
    (hp : Wasmi.StorePatFree x.1) (hh : HostKeeps x.2) (c : Core.Call) :
    Observed.obs P x c = Core.obs P x c ∧ Wasmi.obs P x c = Core.obs P x c :=
  ⟨obs_eq P hs hh c, Wasmi.obs_of_patFree P hp c⟩

/-- The reproducer of issue #2046 has no rounding operator. -/
theorem repro_free : StoreFree Wasmi.reproStore := by
  rw [Silmaril.Proofs.Wasm.Wasmi.RoundFree.storeFree_iff]; decide +kernel

/-- **On issue #2046 the wasmi 0.40.0 model returns `7` and nothing else**, at every profile. -/
theorem repro_obs (P : Profile) :
    Observed.obs P Wasmi.reproPt Wasmi.reproCall = {.returns [Val.i32 7]} := by
  rw [obs_eq P repro_free (hostKeeps_empty _), Wasmi.core_f]

end Silmaril.Wasm.Wasmi.RoundFree
