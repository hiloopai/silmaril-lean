module

public import Silmaril.Wasm.Wasmi.LooseW.Defs
public import Silmaril.Wasm.Wasmi.Fusion.Thms
public import Silmaril.Wasm.Wasmi.Observed.Thms
public import Silmaril.Proofs.Wasm.Wasmi.LooseW.Sim

/-!
# A loose model for the wider select fusion: theorems

`Silmaril.Wasm.Wasmi.Fusion` showed that the model `fuse` of wasmi 2.0.0's issue #2046 is
incomplete (`model_blind`) and that `fuseW` has exactly the probe's observations on the four
probed bodies (`wider_variants`, `wider_repro`). `LooseAll` admits only `fuse`. Here:

* `LooseW.wasmiW_le`: **every observation of the wider model `obsW` is a `LooseW`
  observation**, for hosts parametric in function code. The proof is a stuttering simulation
  (`Silmaril.Proofs.Wasm.Wasmi.LooseW.behaviours_subset`): the `eqz` shape has three source
  instructions against four translated ones, so after a `trap` the source may run out of
  instructions to discard first, and then it waits;
* `LooseW.core_le`, `LooseW.wasmi_le`: Core and the narrow model `fuse` refine `LooseW` too;
* `LooseAllW`: Core 3.0 plus `selectEitherW` and `roundNaN`. **Core, wasmi 0.40.0
  (`Observed.obs`), wasmi 2.0.0 as `fuse` (`Wasmi.obs`) and wasmi 2.0.0 as `fuseW` (`obsW`)
  all refine it** (`core_le`, `wasmi040_le`, `wasmi200_le`, `wasmi200W_le`), and `LooseAll`'s
  observations are among its observations (`looseAll_le`). `transfer` moves a universal
  sentence of `LooseAllW` to all four;
* `probes`: on the reproducer and the three probed variants, `LooseAllW` has both the spec's
  result and the result the harness observes on wasmi 2.0.0, which `LooseAll` was not shown to
  have.

As before, `fuseW` is fitted to the probes, not derived from wasmi's translator. New theorems.
-/

@[expose] public section

namespace Silmaril.Wasm.Wasmi.LooseW

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Atlas Silmaril.Wasm.Wasmi.Fusion
open Silmaril.Proofs.Wasm.Wasmi.Observed (loose_mono_quirk)

variable {H : Type}

/-- **Core refines `LooseW`.** -/
theorem core_le (P : Profile) (x : Core.Pt H) (c : Core.Call) : Core.obs P x c ⊆ obs P x c :=
  Variant.loose_mono _ _ _

/-- **The wider model refines `LooseW`**, for hosts parametric in function code. -/
theorem wasmiW_le (P : Profile) {x : Core.Pt H} (hh : HostParametric x.2) (c : Core.Call) :
    obsW P x c ⊆ obs P x c :=
  Silmaril.Proofs.Wasm.Wasmi.LooseW.behaviours_subset (hh.respects (fun fi => FuncRel.refl fi))
    x.1 c.1 c.2

/-- `selectEither` is `selectEitherW` at the reported shape. -/
theorem quirk_of_loose {c c' : Config H} (h : Wasmi.Loose.Quirk c c') : Quirk c c' := by
  cases h with
  | selectEither b hv => exact Quirk.selectEither .ne0 b hv

/-- The loose relation of `fuse` is contained in `LooseW`'s. -/
theorem step_of_loose {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Wasmi.Loose.Step P host c c') : Step P host c c' :=
  loose_mono_quirk (fun _ _ => quirk_of_loose) h

/-- **The narrow model `fuse` refines `LooseW`**, for hosts parametric in function code. -/
theorem wasmi_le (P : Profile) {x : Core.Pt H} (hh : HostParametric x.2) (c : Core.Call) :
    Wasmi.obs P x c ⊆ obs P x c :=
  (Wasmi.Loose.wasmi_le P hh c).trans (Variant.behavioursR_mono (fun _ _ => step_of_loose) _)

namespace LooseAllW

/-- **Core refines `LooseAllW`.** -/
theorem core_le (P : Profile) (x : Core.Pt H) (c : Core.Call) : Core.obs P x c ⊆ obs P x c :=
  Variant.loose_mono _ _ _

/-- `LooseW` is contained in `LooseAllW`. -/
theorem step_of_w {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : LooseW.Step P host c c') : Step P host c c' :=
  loose_mono_quirk (fun _ _ => AnyQuirkW.select) h

/-- `LooseAll` is contained in `LooseAllW`. -/
theorem step_of_all {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Observed.LooseAll.Step P host c c') : Step P host c c' :=
  loose_mono_quirk (fun _ _ q => by
    cases q with
    | select q => exact AnyQuirkW.select (quirk_of_loose q)
    | round q => exact AnyQuirkW.round q) h

/-- **`LooseAll`'s observations are `LooseAllW` observations.** -/
theorem looseAll_le (P : Profile) (x : Core.Pt H) (c : Core.Call) :
    Observed.LooseAll.obs P x c ⊆ obs P x c :=
  Variant.behavioursR_mono (fun _ _ => step_of_all) _

/-- **wasmi 0.40.0 refines `LooseAllW`**, at every point. -/
theorem wasmi040_le (P : Profile) (x : Core.Pt H) (c : Core.Call) :
    Observed.obs P x c ⊆ obs P x c :=
  (Observed.LooseAll.wasmi040_le P x c).trans (looseAll_le P x c)

/-- **wasmi 2.0.0 as `fuse` refines `LooseAllW`**, for hosts parametric in function code. -/
theorem wasmi200_le (P : Profile) {x : Core.Pt H} (hh : HostParametric x.2) (c : Core.Call) :
    Wasmi.obs P x c ⊆ obs P x c :=
  (Observed.LooseAll.wasmi200_le P hh c).trans (looseAll_le P x c)

/-- **wasmi 2.0.0 as `fuseW` refines `LooseAllW`**, for hosts parametric in function code. -/
theorem wasmi200W_le (P : Profile) {x : Core.Pt H} (hh : HostParametric x.2) (c : Core.Call) :
    obsW P x c ⊆ obs P x c :=
  (wasmiW_le P hh c).trans (Variant.behavioursR_mono (fun _ _ => step_of_w) _)

/-- **Transfer**: a universal sentence of `LooseAllW` holds for Core, wasmi 0.40.0 and (for
hosts parametric in function code) both models of wasmi 2.0.0. -/
theorem transfer (P : Profile) {x : Core.Pt H} {φ : BSen Core.Call (Behaviour Val)}
    (h : φ.Sat (obs P x)) (hu : φ.Universal) (hh : HostParametric x.2) :
    φ.Sat (Core.obs P x) ∧ φ.Sat (Observed.obs P x) ∧ φ.Sat (Wasmi.obs P x) ∧
      φ.Sat (obsW P x) :=
  ⟨BSen.sat_of_subset_univ (core_le P x) hu h, BSen.sat_of_subset_univ (wasmi040_le P x) hu h,
    BSen.sat_of_subset_univ (wasmi200_le P hh) hu h,
    BSen.sat_of_subset_univ (wasmi200W_le P hh) hu h⟩

/-- The probe modules have no host functions. -/
theorem ptOf_hostParametric (body : List Instr) : HostParametric (ptOf body).2 :=
  fun _ _ _ _ _ _ _ _ h => h.elim

/-- **`LooseAllW` has the spec's and the probe's results on all four probed bodies**: `7` and
`5` on the reproducer and on `b != 0`, `5` and `7` on `0 == b` and on `eqz b`. -/
theorem probes (P : Profile) :
    (Behaviour.returns [Val.i32 7] ∈ obs P reproPt reproCall ∧
      Behaviour.returns [Val.i32 5] ∈ obs P reproPt reproCall) ∧
    (Behaviour.returns [Val.i32 7] ∈ obs P (ptOf swapBody) reproCall ∧
      Behaviour.returns [Val.i32 5] ∈ obs P (ptOf swapBody) reproCall) ∧
    (Behaviour.returns [Val.i32 5] ∈ obs P (ptOf eqBody) reproCall ∧
      Behaviour.returns [Val.i32 7] ∈ obs P (ptOf eqBody) reproCall) ∧
    (Behaviour.returns [Val.i32 5] ∈ obs P (ptOf eqzBody) reproCall ∧
      Behaviour.returns [Val.i32 7] ∈ obs P (ptOf eqzBody) reproCall) := by
  obtain ⟨c₁, c₂, c₃⟩ := core_variants P
  obtain ⟨w₁, w₂, w₃⟩ := wider_variants P
  refine ⟨⟨core_le P _ _ (by rw [Wasmi.core_f]; rfl),
      wasmi200W_le P Wasmi.repro_hostParametric _ (by rw [wider_repro]; rfl)⟩,
    ⟨core_le P _ _ (by rw [c₁]; rfl), wasmi200W_le P (ptOf_hostParametric _) _ (by rw [w₁]; rfl)⟩,
    ⟨core_le P _ _ (by rw [c₂]; rfl), wasmi200W_le P (ptOf_hostParametric _) _ (by rw [w₂]; rfl)⟩,
    ⟨core_le P _ _ (by rw [c₃]; rfl), wasmi200W_le P (ptOf_hostParametric _) _ (by rw [w₃]; rfl)⟩⟩

end LooseAllW

end Silmaril.Wasm.Wasmi.LooseW

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.Wasmi.LooseW.wasmiW_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Wasmi.LooseW.wasmiW_le

/-- info: 'Silmaril.Wasm.Wasmi.LooseW.LooseAllW.transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Wasmi.LooseW.LooseAllW.transfer

/-- info: 'Silmaril.Wasm.Wasmi.LooseW.LooseAllW.probes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Wasmi.LooseW.LooseAllW.probes
