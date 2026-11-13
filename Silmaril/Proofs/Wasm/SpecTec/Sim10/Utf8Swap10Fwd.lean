module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Swap10Typ

/-!
# The 1.0 forward theorem at non-empty export names, from the involution leaf

The 2.0 assembly (`Sim20.Utf8Swap.fwdU20_of_swapStep20`) for V1, under round 4's invariants:

* `typedV_rep_sim10`, `typedV_rep_U10`: a re-encoding is an `exportinst*` of `simEnv10T` (its one
  export is checked by evaluation, `typedV_exp0_10T`) and of `utf8Env10T`;
  `typedV_exports_U10`: so are the exports of a `moduleinst` of `utf8Env10T`.
* `swapS10_fuel`: the exchange of one configuration loses a bounded amount of fuel.
* **`stepFwd10U_of_swapStep10`**: given the leaf `Task.swapStep10`, every V1 step from a
  configuration typed in `utf8Env10T (fwdB10 nd r)` that satisfies round 4's other invariants is a
  step of `utf8Env10T` between the images. The re-encoded configuration is typed in `simEnv10T`
  (`typed10_exp10`), satisfies the invariants and steps (`step_exp10`), so round 4's
  `Whole.wholeStepFwd10T_one` applies; the step moves to `utf8Env10T` and back along the leaf.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step)
open Silmaril.Wasm.Execution.Runtime (Frame ModuleInst FuncInst ExportInst)
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10 (GSetOk Typed10 configV moduleInstV)
open Silmaril.Wasm.SpecTec.Sim10.Whole (Plain10 MemsAligned10 NoHost10 fwdB10)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.Utf8Fix (utf8Env10T sstepB_utf8_10T bytesB10_utf8)
open Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10 (ModsQ10 ModOk10 modsQ10_step modsQ10_of_typed
  noHost10_of_typedU stepFwd10U_typed)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Swap (exportsT swapV uniform_fuel)

variable {H : Type} {hn : H → String}

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 4000000 in
/-- **The export `"" ↦ FUNC 0` is an `exportinst`** of `simEnv10T B` (checked by evaluation). -/
theorem typedV_exp0_10T (B : Builtins) : TypedV (simEnv10T B) (.varT "exportinst" [])
    (.struct [("NAME", Sim20.nameV exp010.name), ("ADDR", Sim10.externAddrV exp010.value)]) :=
  Sim20.Whole.typedV_of_empty20 ⟨100, by with_unfolding_all rfl⟩

/-- **A re-encoding is an `exportinst*` of `simEnv10T B`.** -/
theorem typedV_rep_sim10 (B : Builtins) (k : Nat) :
    TypedV (simEnv10T B) exportsT (expV10 (List.replicate k exp010)) :=
  Sim.typedV_list_iff.2 fun u hu => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
    obtain rfl := List.eq_of_mem_replicate hx
    exact typedV_exp0_10T B

/-- **A re-encoding is an `exportinst*` of `utf8Env10T B`.** -/
theorem typedV_rep_U10 {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none) (k : Nat) :
    TypedV (utf8Env10T B) exportsT (expV10 (List.replicate k exp010)) :=
  Sim20.Utf8Mono.typedV_ext (Sim10.Utf8Fix.envExt10T B hB) (typedV_rep_sim10 B k)

/-- **The exports of a `moduleinst` of `utf8Env10T B` are an `exportinst*` there.** -/
theorem typedV_exports_U10 {B : Builtins} {m : ModuleInst} (h : ModOk10 B m) :
    TypedV (utf8Env10T B) exportsT (expV10 m.exports) := by
  have hmod := (Utf8Strip10.sameTyps_utf8 B "moduleinst").trans Utf8Strip10.findTyp_moduleinst10T
  have hF := Sim20.Whole.hasTypFields_of_closed hmod h
  obtain ⟨-, hF⟩ := Sim20.Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Sim20.Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Sim20.Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Sim20.Whole.hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := Sim20.Whole.hasTypFields_cons_nil_iff.1 hF
  exact Sim20.Whole.typedV_list_of_empty20 (Sim20.Whole.hasTypFields_cons_nil_iff.1 hF).1

/-- The values `swapS10 (expsV10 c)` exchanges are `exportinst*`s of `utf8Env10T B`. -/
theorem swapS10_pairs_typed {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none) {c : Config H}
    (hc : Typed10 (utf8Env10T B) hn c) :
    ∀ x ∈ expsV10 c ++ (expsV10 c).map (encV10 (expsV10 c)),
      HasTyp (utf8Env10T B) VarEnv.empty exportsT x := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨m, hmm, rfl⟩ := List.mem_map.1 hx
    exact typedV_exports_U10 (mem_mods10 (modsQ10_of_typed hc) m hmm) _ ⟨rfl, rfl, rfl⟩
  · obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx
    exact typedV_rep_U10 hB _ _ ⟨rfl, rfl, rfl⟩

/-- **`swapS10 (expsV10 c)` loses a bounded amount of fuel on `exportinst*`.** -/
theorem swapS10_fuel {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none) {c : Config H}
    (hc : Typed10 (utf8Env10T B) hn c) : ∃ K, ∀ n u,
      hasTyp n (utf8Env10T B) VarEnv.empty exportsT u = .ok true →
      hasTyp (n + K) (utf8Env10T B) VarEnv.empty exportsT (swapS10 (expsV10 c) u) = .ok true := by
  obtain ⟨K, hK⟩ := uniform_fuel _ (swapS10_pairs_typed hB hc)
  refine ⟨K, fun n u hu => ?_⟩
  rcases swapS10_cases (expsV10 c) u with hx | he
  · exact ((monoTypAt_of_le (Nat.le_add_left K n)).typ _ _ _ _).ok (hK _ hx)
  · rw [he]
    exact ((monoTypAt_of_le (Nat.le_add_right n K)).typ _ _ _ _).ok hu

/-- **The 1.0 forward step at non-empty export names, from the involution leaf.** -/
theorem stepFwd10U_of_swapStep10 (hL : Task.swapStep10) {host : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {c c' : Config H} (hc : Typed10 (utf8Env10T (fwdB10 nd r)) hn c)
    (hpl : Plain10 c.code) (hg : GSetOk c.store c.frame c.code) (hal : MemsAligned10 c.store)
    (h : Step host c c') :
    SStepB (utf8Env10T (fwdB10 nd r)) (configV hn c) (configV hn c') := by
  have hB := bytesB10_utf8 (Silmaril.Wasm.Numerics.Profile.spec nd r)
  have hnh := noHost10_of_typedU hB hc
  have hnh' := noHost10_of_typedU hB (stepFwd10U_typed hc hpl hg hal h)
  let S := expsV10 c
  have hm : ModsQ10 (fun m => expV10 m.exports ∈ S) c :=
    modsQ10_mono (fun m hm => List.mem_map_of_mem (f := fun m => expV10 m.exports) hm)
      (modsQ10_mods10 c)
  have hm' : ModsQ10 (fun m => expV10 m.exports ∈ S) c' := modsQ10_step h hnh hm
  have hs := typed10_exp10 (F := encExp10 S) hB (fun _ => typedV_rep_sim10 _ _) hc
  obtain ⟨-, hf⟩ := Whole.wholeStepFwd10T_one hs (plain10_exp hpl) (gSetOk_exp10 hg)
    (memsAligned10_exp hal) (step_exp10 h hnh)
  obtain ⟨K, hK⟩ := swapS10_fuel hB hc
  have hS := hL nd r (swapS10 S) (swapS10_swapS10 S) K hK _ _ (sstepB_utf8_10T hB hf)
  rwa [swapV_configV_exp10 (modsQ10_mono (fun _ h => swapS10_expV_enc h) hm) hnh,
    swapV_configV_exp10 (modsQ10_mono (fun _ h => swapS10_expV_enc h) hm') hnh'] at hS

end Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10
