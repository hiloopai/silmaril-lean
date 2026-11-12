module

public import Silmaril.Wasm.Wasmi.Gaps.Defs
public import Silmaril.Wasm.Wasmi.Observed.Thms
public import Silmaril.Proofs.Wasm.Wasmi.Gaps.Witness

/-!
# The known version gaps between wasmi 2.0.0 and Core 3.0

Proofs in `Silmaril.Proofs.Wasm.Wasmi.Gaps.Witness`. For each of the seven gap classes `k`
(`Gap`, the classes of every module of the vendored testsuite that the probe saw wasmi 2.0.0
refuse):

* `core_instantiates`: Core 3.0 instantiates `witness k` at every profile and host;
* `wasmi_refuses`: the model of wasmi 2.0.0's instantiation refuses it;
* `isolated`: `witness k` has the gap `k` and no other;
* `control`: the control module has no gap, and wasmi's instantiation is the spec's allocation
  on it.

`instantiate_sound`: whenever the model of wasmi 2.0.0 instantiates a module, the result is
the spec's allocation. So these gaps only remove instances, and the runtime results of the
existing models are unaffected: **`LooseAll` still admits Core, wasmi 0.40.0 and wasmi 2.0.0**
(`looseAll_admits`, wasmi 2.0.0 for hosts parametric in function code).

`known_gaps`: the known version gaps between wasmi 2.0.0 and Core, with witnesses: the seven
instantiation gaps, and the select fusion of issue #2046 at run time (`Wasmi.core_f`,
`Wasmi.wasmi_f`). The signalling-NaN quirk is not one of them: wasmi 2.0.0 quiets the NaN (the
probe of `docs/projects/wasm-wasi.md`, track wasmi). Gaps the vendored testsuite does not exercise
(other GC or exception-handling forms, a full wasmi 2.0.0 harness column) are not covered.
-/

@[expose] public section

namespace Silmaril.Wasm.Wasmi.Gaps

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas Silmaril.Wasm.Execution.Core.Sim

variable {H : Type}

/-- **Core 3.0 instantiates every witness**, at every profile and host. -/
theorem core_instantiates {k : Gap} (hk : k ∈ allGaps) (P : Profile) (host : HostSemantics Empty) :
    ∃ c : Config Empty, Instantiate P host ({} : Store Empty) (witness k) [] c :=
  Silmaril.Proofs.Wasm.Wasmi.Gaps.core_instantiates hk P host

/-- **The model of wasmi 2.0.0 refuses every witness.** -/
theorem wasmi_refuses {k : Gap} (hk : k ∈ allGaps) :
    instantiate200? ({} : Store Empty) (witness k) = none :=
  Silmaril.Proofs.Wasm.Wasmi.Gaps.wasmi_refuses hk

/-- **Each witness has exactly its own gap.** -/
theorem isolated {k k' : Gap} (hk : k ∈ allGaps) (hk' : k' ∈ allGaps) :
    hasGap k' (witness k) = true ↔ k' = k :=
  Silmaril.Proofs.Wasm.Wasmi.Gaps.isolated hk hk'

/-- **The control module has no gap**, and wasmi's instantiation is the spec's allocation. -/
theorem control :
    refuses controlMod = false ∧
      instantiate200? ({} : Store Empty) controlMod = prepare? evalConst? {} controlMod [] :=
  Silmaril.Proofs.Wasm.Wasmi.Gaps.control

/-- **What wasmi 2.0.0 instantiates is the spec's allocation.** -/
theorem instantiate_sound {s : Store Empty} {m : Module} {p : Config Empty × Option FuncIdx}
    (h : instantiate200? s m = some p) : prepare? evalConst? s m [] = some p :=
  Silmaril.Proofs.Wasm.Wasmi.Gaps.instantiate_sound h

/-- **`LooseAll` admits Core, wasmi 0.40.0 and wasmi 2.0.0** (the last for hosts parametric in
function code). -/
theorem looseAll_admits (P : Profile) {x : Core.Pt H} (hh : HostParametric x.2) (c : Core.Call) :
    Core.obs P x c ⊆ Observed.LooseAll.obs P x c ∧
      Observed.obs P x c ⊆ Observed.LooseAll.obs P x c ∧
      Wasmi.obs P x c ⊆ Observed.LooseAll.obs P x c :=
  ⟨Observed.LooseAll.core_le P x c, Observed.LooseAll.wasmi040_le P x c,
    Observed.LooseAll.wasmi200_le P hh c⟩

/-- **The known version gaps between wasmi 2.0.0 and Core 3.0, with witnesses**: seven modules
Core instantiates and wasmi 2.0.0 refuses, and the issue-#2046 call on which Core returns only
`7` and wasmi 2.0.0 only `5`. -/
theorem known_gaps (P : Profile) (host : HostSemantics Empty) :
    (∀ k ∈ allGaps, (∃ c : Config Empty, Instantiate P host ({} : Store Empty) (witness k) [] c) ∧
      instantiate200? ({} : Store Empty) (witness k) = none) ∧
    Core.obs P Wasmi.reproPt Wasmi.reproCall = {.returns [Val.i32 7]} ∧
      Wasmi.obs P Wasmi.reproPt Wasmi.reproCall = {.returns [Val.i32 5]} :=
  ⟨fun _ hk => ⟨core_instantiates hk P host, wasmi_refuses hk⟩, Wasmi.core_f P, Wasmi.wasmi_f P⟩

end Silmaril.Wasm.Wasmi.Gaps
