module

public import Silmaril.Raw.Wasm.Unified.Own.Coh
public import Silmaril.Wasm.Models.Lime1Core.Thms
public import Silmaril.Wasm.Models.V10.Thms

/-!
# Lime1 and 1.0 code runs are Core 3.0 code runs (unrefined)

* `sim_code`: the Lime1 configuration running code `js` on own arguments, in a well-formed store
  and a frame whose module names allocated functions, is simulated (`Lime1.Execution.Sim`) by the
  Core configuration running the translated code on the translated arguments, in the image store
  and frame;
* `behL_sub_of_sim`: behaviours along any `Sim` (as `Lime1Core.behaviours_sub` at `$invoke`);
* `codeSimL`: hence the code-level simulation `CodeSim` of `Silmaril.Wasm.Unified.Versions.Own`;
* `beh10_sub_behL`, `codeSim10`: 1.0 code runs are Lime1 runs of the translated code (the copied
  lock-step `Steps.toLime`, `Diverges.toLime`), hence Core runs.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.Unified.Own

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime Silmaril.Wasm.Models
open Silmaril.Wasm.Unified.Versions Silmaril.Wasm.Unified.Versions.Own Silmaril.Wasm.Unified.Core30
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- Source instructions are well formed. -/
theorem listWF_of_source (s : V10.LStore H) :
    (l : List Lime1.Execution.Admin) → (∀ a ∈ l, ∃ i, a = .source i) →
      Lime1.Execution.Admin.listWF s l
  | [], _ => trivial
  | a :: l, h => by
    obtain ⟨i, rfl⟩ := h a (List.mem_cons_self ..)
    exact ⟨trivial, listWF_of_source s l fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

/-- Values and source code are source instructions. -/
theorem source_code (ws : List Value) (js : List Lime1.Instr) :
    ∀ a ∈ Lime1.Execution.values ws ++ Lime1.Execution.expression js, ∃ i, a = .source i := by
  intro a ha
  rcases List.mem_append.1 ha with h | h
  · obtain ⟨⟨t, bits⟩, -, rfl⟩ := List.mem_map.1 h
    cases t
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
    exact ⟨i, rfl⟩

/-- **Lime1 code runs are simulated by Core code runs.** -/
theorem sim_code {s : V10.LStore H} (hwf : Lime1.Execution.StoreWF s) {f : Frame}
    (hm : Lime1.Execution.ModWF s f.module) (ws : List Value) (js : List Lime1.Instr) :
    Lime1.Execution.Sim ⟨s, f, Lime1.Execution.values ws ++ Lime1.Execution.expression js⟩
      (cfgOf s.toCore f.toCore (js.map Lime1.Instr.toCore) (ws.map Value.toCore)) := by
  have h := Lime1.Execution.Sim.refl_toCore
    (⟨s, f, Lime1.Execution.values ws ++ Lime1.Execution.expression js⟩ :
      Lime1.Execution.Config H)
    ⟨hwf, hm, listWF_of_source s _ (source_code ws js)⟩
  have e : (⟨s, f, Lime1.Execution.values ws ++ Lime1.Execution.expression js⟩ :
      Lime1.Execution.Config H).toCore =
      cfgOf s.toCore f.toCore (js.map Lime1.Instr.toCore) (ws.map Value.toCore) := by
    simp only [Silmaril.Wasm.Execution.Runtime.Config.toCore, cfgOf,
      Lime1.Execution.listToCore_append, Lime1.Execution.values_toCore,
      Lime1.Execution.expression_toCore]
  rwa [e] at h

/-- A Lime1 result read in Core values. -/
theorem result_toBehaviour (r : Result) :
    Behaviour.map Value.toCore r.toBehaviour = (Result.toCore r).toBehaviour := by
  cases r <;> rfl

/-- **Behaviours along a Lime1 simulation.** -/
theorem behL_sub_of_sim {src : V10.LHost H} {tgt : V2Core.CHost H}
    (hosts : Lime1.Execution.HostCompatible src tgt) {a : Lime1.Execution.Config H}
    {c : Silmaril.Wasm.Execution.Core.Config H} (hs : Lime1.Execution.Sim a c) :
    Behaviour.mapSet Value.toCore (Lime1Core.behavioursOfL src a) ⊆
      Silmaril.Wasm.Execution.Core.behavioursOf Profile.spec tgt c := by
  rintro _ ⟨b, ⟨c', r, hrun, hres, rfl⟩ | ⟨rfl, hdiv⟩, rfl⟩
  · obtain ⟨c₁, hrun₁, hs₁⟩ := Lime1.Execution.Steps.toCore hosts hrun hs
    have hcode := Lime1.Execution.Sim.result hs₁ hres
    have hmem := Silmaril.Wasm.Execution.Core.mem_behavioursOf hrun₁ hcode
    rwa [result_toBehaviour]
  · exact Or.inr ⟨rfl, Lime1.Execution.Diverges.toCore hosts hdiv hs⟩

/-- **The code-level simulation of Lime1.** -/
theorem codeSimL {okJ : List Lime1.Instr → Prop} {okc : List Instr → Prop}
    (hok : ∀ js, okJ js → okc (js.map Lime1.Instr.toCore)) {host : V10.LHost H}
    {s : V10.LStore H} {f : Frame} (hwf : Lime1.Execution.StoreWF s)
    (hm : Lime1.Execution.ModWF s f.module) (hp : Lime1.Execution.HostPreserves host)
    (hk : V10.HostKeepsL host) :
    CodeSim synL okJ (behL host s f) Profile.spec (Lime1Core.liftHostC host) s.toCore f.toCore
      okc := by
  intro js is htr hokJ
  obtain rfl := eq_map_of_tr (L := synL) (g := Lime1.Instr.toCore) (fun _ => rfl) htr
  refine ⟨hok js hokJ, fun vs b hb => ?_⟩
  obtain ⟨ws, rfl, hb⟩ := hb
  exact behL_sub_of_sim (Lime1Core.liftHostC_compatible hp hk) (sim_code hwf hm ws js) hb

theorem codeToLime_values (ws : List Value) :
    V1.Execution.codeToLime (V1.Execution.values ws) = Lime1.Execution.values ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [V1.Execution.values, List.map_cons, V1.Execution.codeToLime_cons,
      V1.Execution.map_value] at ih ⊢
    rw [ih]
    rfl

theorem codeToLime_expression (js : List V1.Instr) :
    V1.Execution.codeToLime (V1.Execution.expression js) =
      Lime1.Execution.expression (js.map V1.Instr.toLime) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [V1.Execution.expression, List.map_cons, V1.Execution.codeToLime_cons] at ih ⊢
    rw [ih]
    rfl

/-- The Lime1 image of a 1.0 code configuration. -/
theorem toLime_code (s : V10.OStore H) (f : Frame) (ws : List Value) (js : List V1.Instr) :
    V1.Execution.Config.toLime
      (⟨s, f, V1.Execution.values ws ++ V1.Execution.expression js⟩ : V1.Execution.Config H) =
      ⟨s.mapCode V1.Func.toLime, f,
        Lime1.Execution.values ws ++ Lime1.Execution.expression (js.map V1.Instr.toLime)⟩ := by
  simp only [V1.Execution.Config.toLime, V1.Execution.codeToLime_append, codeToLime_values,
    codeToLime_expression]

/-- **1.0 behaviours are Lime1 behaviours** of the transported configuration. -/
theorem beh10_sub_behL (host : V10.OHost H) (c : V1.Execution.Config H) :
    V1.Execution.behavioursOf host c ⊆
      Lime1Core.behavioursOfL (host.mapCode V1.Func.toLime) c.toLime := by
  have hosts := HostSemantics.compatible_mapCode V1.Func.toLime host
  rintro _ (⟨c', r, hrun, hres, rfl⟩ | ⟨rfl, hdiv⟩)
  · refine Or.inl ⟨c'.toLime, r, V1.Execution.Steps.toLime hosts hrun, ?_, rfl⟩
    simp [V1.Execution.Config.toLime, hres]
  · exact Or.inr ⟨rfl, V1.Execution.Diverges.toLime hosts hdiv⟩

/-- **The code-level simulation of 1.0**, through Lime1. -/
theorem codeSim10 {okJ : List V1.Instr → Prop} {okc : List Instr → Prop}
    (hok : ∀ js, okJ js → okc (js.map fun j => j.toLime.toCore)) {host : V10.OHost H}
    {s : V10.OStore H} {f : Frame}
    (hwf : Lime1.Execution.StoreWF (s.mapCode V1.Func.toLime))
    (hm : Lime1.Execution.ModWF (s.mapCode V1.Func.toLime) f.module)
    (hp : Lime1.Execution.HostPreserves (host.mapCode V1.Func.toLime))
    (hk : V10.HostKeepsL (host.mapCode V1.Func.toLime)) :
    CodeSim syn10 okJ (beh10 host s f) Profile.spec
      (Lime1Core.liftHostC (host.mapCode V1.Func.toLime)) (s.mapCode V1.Func.toLime).toCore
      f.toCore okc := by
  intro js is htr hokJ
  obtain rfl := eq_map_of_tr (L := syn10) (g := fun j => j.toLime.toCore) (fun _ => rfl) htr
  refine ⟨hok js hokJ, fun vs b hb => ?_⟩
  obtain ⟨ws, rfl, b', hb', rfl⟩ := hb
  have hL := beh10_sub_behL host _ hb'
  erw [toLime_code] at hL
  have hc := behL_sub_of_sim (Lime1Core.liftHostC_compatible hp hk)
    (sim_code hwf hm ws (js.map V1.Instr.toLime)) ⟨b', hL, rfl⟩
  have e : List.map (fun j : V1.Instr => j.toLime.toCore) js =
      (js.map V1.Instr.toLime).map Lime1.Instr.toCore := (List.map_map ..).symm
  show _ ∈ behCode _ _ _ _ (List.map (fun j : V1.Instr => j.toLime.toCore) js) _
  rw [e]
  exact hc

end Silmaril.Raw.Wasm.Unified.Own
