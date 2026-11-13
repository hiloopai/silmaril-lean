module

public import Silmaril.Raw.Wasm.Unified.Own.Coh
public import Silmaril.Wasm.Models.V2Core.Thms

/-!
# 2.0 code runs are Core 3.0 code runs (unrefined)

* `listToCore_plain`: 2.0 code translating to `is` has the Core image `is.map plainOrNull`;
* `sim_code20`: the 2.0 configuration running code `js` on 2.0 arguments, in a well-formed store
  with a Core image and a frame whose module names allocated functions, is simulated (the copied
  `V2.Execution.Sim`) by the Core configuration running the translated code on the translated
  arguments, in the image store and frame;
* `codeSim20`: hence the code-level simulation `CodeSim` of `Silmaril.Wasm.Unified.Versions.Own`,
  at every profile.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.Unified.Own

open Silmaril.Wasm Silmaril.Wasm.Models
open Silmaril.Wasm.Unified.Versions Silmaril.Wasm.Unified.Versions.Own Silmaril.Wasm.Unified.Core30
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- The Core image of translated 2.0 code. -/
theorem listToCore_plain (s : V2Core.VStore H) {js : List V2.Instr} {is : List Instr}
    (h : syn20.Tr js is) :
    V2.Execution.Admin.listToCore s (js.map .plain) =
      some (is.map V2.Execution.ToCore.plainOrNull) := by
  induction h with
  | nil => rfl
  | cons hj _ ih =>
    rw [List.map_cons, V2.Execution.Admin.listToCore_cons, V2.Execution.Admin.plain_toCore, ih]
    rw [show V2.Instr.toCore _ = some _ from hj]
    rfl

/-- Normalising translated code is `plainOrNull`. -/
theorem map_norm_expression (m : V2.Execution.ToCore.CModuleInst) {js : List V2.Instr}
    {is : List Instr} (h : syn20.Tr js is) :
    (Silmaril.Wasm.Execution.Core.expression is).map (V2.Execution.ToCore.Admin.norm m) =
      is.map V2.Execution.ToCore.plainOrNull := by
  induction h with
  | nil => rfl
  | cons hj _ ih =>
    simp only [Silmaril.Wasm.Execution.Core.expression, List.map_cons, List.map_map] at ih ⊢
    rw [V2.Execution.ToCore.Admin.norm_plain,
      V2.Execution.ToCore.normPlain_eq_plainOrNull m (V2.Execution.Instr.toCore_ne_callRef hj)]
    exact congrArg _ ih

/-- 2.0 values and plain code are well formed. -/
theorem listWF_code (s : V2Core.VStore H) (ws : List V2.Execution.Val) (js : List V2.Instr) :
    V2.Execution.Admin.listWF s (V2.Execution.vals ws ++ js.map .plain) := by
  induction ws with
  | nil =>
    induction js with
    | nil => trivial
    | cons j js ih => exact ⟨trivial, ih⟩
  | cons w ws ih =>
    refine ⟨?_, ih⟩
    rcases w with ⟨⟨_ | _⟩, _⟩ | _ | (_ | _ | _) <;> trivial

/-- **2.0 code runs are simulated by Core code runs.** -/
theorem sim_code20 {s : V2Core.VStore H} {X : V2Core.CStore H} (hwf : V2.Execution.StoreWF s)
    (hX : V2.Execution.Store.toCore s = some X) {f : V2.Execution.Frame}
    (hm : V2.Execution.ModWF s f.module) (ws : List V2.Execution.Val) {js : List V2.Instr}
    {is : List Instr} (h : syn20.Tr js is) :
    V2.Execution.Sim ⟨s, f, V2.Execution.vals ws ++ js.map .plain⟩
      (cfgOf X f.toCore is (ws.map V2.Execution.Val.toCore)) := by
  refine ⟨?_, hwf, hm, listWF_code s ws js⟩
  simp only [V2.Execution.Config.toCore, V2.Execution.ToCore.Config.norm, cfgOf]
  rw [hX, Option.bind_some, V2.Execution.ToCoreSim.listToCore_vals_append s ws (listToCore_plain s h),
    Option.map_some, V2.Execution.ToCore.Admin.normList_eq_map, List.map_append,
    V2.Execution.ToCoreSim.map_norm_cvals, map_norm_expression _ h,
    Silmaril.Proofs.Wasm.Models.V2Core.erase_of_toCore hX, V2.Execution.Frame.erase_toCore]

/-- **The code-level simulation of 2.0**, at every profile. -/
theorem codeSim20 (P : Profile) {okJ : List V2.Instr → Prop} {okc : List Instr → Prop}
    (hok : ∀ js is, syn20.Tr js is → okJ js → okc is) {host : V2Core.VHost H}
    {s : V2Core.VStore H} {X : V2Core.CStore H} {f : V2.Execution.Frame}
    (hwf : V2.Execution.StoreWF s) (hX : V2.Execution.Store.toCore s = some X)
    (hm : V2.Execution.ModWF s f.module) (hp : V2.Execution.HostPreserves host)
    (hk : V2Core.HostKeepsV host) :
    CodeSim syn20 okJ (beh20 P host s f) P (V2Core.liftHost host) X f.toCore okc := by
  intro js is htr hokJ
  refine ⟨hok js is htr hokJ, fun vs b hb => ?_⟩
  obtain ⟨ws, rfl, hb⟩ := hb
  exact Silmaril.Proofs.Wasm.Models.V2Core.behavioursOf_sub (V2Core.liftHost_compatible hp hk)
    (sim_code20 hwf hX hm ws htr) hb

end Silmaril.Raw.Wasm.Unified.Own
