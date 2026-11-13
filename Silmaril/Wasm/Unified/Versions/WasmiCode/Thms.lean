module

public import Silmaril.Wasm.Unified.Versions.Thms
public import Silmaril.Wasm.Wasmi.Thms

/-!
# wasmi refines the loose model at the code level

The code-level counterpart of `Silmaril.Wasm.Atlas.Wasmi.toLooseUniv`, which closes the frozen
target `Task.wasmi_refines_loose` of `Silmaril.Wasm.Unified.Versions.Thms`.

* `wasmi_code_le`: running the translated code `fuse is` from the translated store
  `fuseStore s` with Core 3.0 reduction has only behaviours of running `is` from `s` with the
  loose reduction, for a host parametric in function code. The proof is the lock-step simulation
  of `Silmaril.Wasm.Wasmi` (`sim_main`, through its header `Silmaril.Wasm.Wasmi.Thms`), started from
  the code-level configurations instead of an invocation: the start configurations are related
  because `fuse is` is related to `is` (`fuse_rel`) and the stores are related
  (`storeRel_fuseStore`);
* `wasmiR_refines_looseR`: **the wasmi model refines the loose model** over the 3.0 signature;
* **`wasmi_refines_loose`**: `Task.wasmi_refines_loose` holds;
* `wasmi_presentsLE`: hence the Atlas transition wasmi → loose (`Wasmi.toLooseUniv`) is presented
  up to refinement by the inclusion `nWasmi ⊆ sig30`, at points whose host is parametric.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.Atlas Silmaril.Wasm.Models Silmaril.Wasm.Wasmi Silmaril.Proofs.Wasm.Wasmi
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **wasmi's code-level behaviours are loose behaviours.** -/
theorem wasmi_code_le (P : Profile) {host : HostSemantics H} (hh : HostParametric host)
    (s : Store H) (f : Frame) (is : List Instr) (vs : UIn) :
    Variant.behavioursR (Step P host) (cfgOf (fuseStore s) f (fuse is) vs) ⊆
      Variant.behavioursR (Loose.Step P host) (cfgOf s f is vs) := by
  have hhost : HostRespects FR host := hh.respects (fun fi => FuncRel.refl fi)
  refine Variant.behavioursR_subset_of_sim (Rel := SimR) ?_ ?_ ?_
  · intro c c' d hs hr
    obtain ⟨sL, g, wL⟩ := c
    obtain ⟨sL', g', wL'⟩ := c'
    obtain ⟨sR, g₀, R⟩ := d
    obtain ⟨hfg, hst, hw⟩ := hr
    dsimp only at hfg hst hw
    subst hfg
    obtain ⟨sR', R', hl, hst', hr'⟩ := sim_main hhost _ (Nat.lt_succ_self _) hs hst hw
    exact ⟨⟨sR', g', R'⟩, hl, rfl, hst', hr'⟩
  · intro c d r hr hc
    have h := hr.2.2
    rw [hc] at h
    exact h.result_inv
  · exact ⟨rfl, storeRel_fuseStore s, LRel.vals_append vs (LRel.src (fuse_rel is))⟩

/-- **The wasmi model refines the loose model** (3.0 signature). -/
theorem wasmiR_refines_looseR (P : Profile) {host : HostSemantics H} (hh : HostParametric host)
    (s : Store H) (f : Frame) (okc : List Instr → Prop) :
    Refines (wasmiR P host s f okc) (looseR P host s f okc) := by
  rintro ⟨c, vs⟩ b ⟨hok, is, hD, hc, hb⟩
  exact ⟨hok, is, hD, hc, wasmi_code_le P hh s f is vs hb⟩

/-- **`Task.wasmi_refines_loose` holds.** -/
theorem wasmi_refines_loose : Task.wasmi_refines_loose := by
  intro H P f okc x hh
  exact (wasmiR_refines_looseR P hh x.1 f okc).reduct (FSig.incl (nsig_sub30 wasmi200))

/-- **wasmi → loose is presented up to refinement** on points with a parametric host. -/
theorem wasmi_presentsLE (P : Profile) (f : Frame) (okc : List Instr → Prop) (x : Core.Pt H)
    (hx : Wasmi.Dom x) :
    Refines ((pWasmi P f okc).model x)
      (((pLoose P f okc).model ((Wasmi.toLooseUniv P H).pt x)).reduct
        (FSig.incl (nsig_sub30 wasmi200))) :=
  wasmi_refines_loose H P f okc x hx.2

end Silmaril.Wasm.Unified.Versions
