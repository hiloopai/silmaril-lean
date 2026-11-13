module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.HostMods.Mods
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostMods.Assemble
public import Silmaril.Wasm.Atlas.SpecTecR7Runs.Defs

/-!
# REI without `HostExportParam`: `StripInj` and `NamesBnd` along every run

For a host that invents no module, a Core step introduces no module instance
(`mods_step_sub`, unrefined). Both `StripInj` and `NamesBnd` speak only of the module instances
of a configuration, so both pass to every successor, deterministic or not:

* `stripInj_step`, `namesBnd_step`, and `modsLe_steps` along runs;
* `reachE_of_stripInj`: **`ReachE` from `StripInj` and `NamesBnd` at the source**, given round 6's
  `Round6.MemSimd.BoundedSelE` (bounded, no float-selection code) at every reachable
  configuration. This replaces `reachE_of_detM`'s determinism hypothesis;
* `runDomE_of_stripInj`: the same for `Atlas.SpecTecR7Runs.RunDomE`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HostMods

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim.Round7.Runs (ReachE)

variable {H : Type}

/-- **`StripInj` passes to every successor**, for a host that invents no module. -/
theorem stripInj_step {P : Profile} {host : HostSemantics H} (hm : HostModsSub host)
    {c c' : Config H} (hi : StripInj c) (hs : Step P host c c') : StripInj c' :=
  fun m₁ h₁ m₂ h₂ he => hi m₁ (mods_step_sub hm hs m₁ h₁) m₂ (mods_step_sub hm hs m₂ h₂) he

/-- `ModsLe` along runs. -/
theorem modsLe_steps {P : Profile} {host : HostSemantics H} (hm : HostModsSub host)
    {c c' : Config H} (hs : Steps P host c c') : ModsLe c' c := by
  induction hs with
  | refl => exact fun _ h => h
  | tail _ h₂ ih => exact fun m hm' => ih m (mods_step_sub hm h₂ m hm')

mutual
theorem adminNB_of : ∀ a : Admin, (∀ m ∈ modsAdmin a, ModNamesBnd m) → AdminNB a
  | .label _ _ body, h => adminsNB_of body h
  | .handler _ _ body, h => adminsNB_of body h
  | .frame _ f body, h => by
      simp only [modsAdmin, List.mem_cons, forall_eq_or_imp] at h
      exact ⟨h.1, adminsNB_of body h.2⟩
  | .plain _, _ => trivial
  | .ref _, _ => trivial
  | .callRefType _, _ => trivial
  | .returnCallRefType _, _ => trivial
  | .trap, _ => trivial

theorem adminsNB_of : ∀ l : List Admin, (∀ m ∈ modsAdmins l, ModNamesBnd m) → AdminsNB l
  | [], _ => trivial
  | a :: l, h => by
      simp only [modsAdmins, List.mem_append] at h
      exact ⟨adminNB_of a fun m hm => h m (.inl hm), adminsNB_of l fun m hm => h m (.inr hm)⟩
end

/-- **`NamesBnd` is a property of the module instances.** -/
theorem namesBnd_iff {c : Config H} : NamesBnd c ↔ ∀ m ∈ mods c, ModNamesBnd m := by
  obtain ⟨s, f, is⟩ := c
  refine ⟨fun h m hm => ?_, fun h => ⟨fun fi hfi => h _ (mem_mods_store hfi),
    h _ (mem_mods.2 (.inr (.inl rfl))), adminsNB_of is fun m hm => h m (mem_mods.2 (.inr (.inr hm)))⟩⟩
  rcases mem_mods.1 hm with hm | rfl | hm
  · obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 hm
    exact h.store fi hfi
  · exact h.frame
  · exact EraseDer.modsAdmins_nb is h.code m hm

/-- **`NamesBnd` passes along runs**, for a host that invents no module. -/
theorem namesBnd_steps {P : Profile} {host : HostSemantics H} (hm : HostModsSub host)
    {c c' : Config H} (hn : NamesBnd c) (hs : Steps P host c c') : NamesBnd c' :=
  namesBnd_iff.2 fun m hm' => namesBnd_iff.1 hn m (modsLe_steps hm hs m hm')

/-- **`StripInj` passes along runs**, for a host that invents no module. -/
theorem stripInj_steps {P : Profile} {host : HostSemantics H} (hm : HostModsSub host)
    {c c' : Config H} (hi : StripInj c) (hs : Steps P host c c') : StripInj c' :=
  fun m₁ h₁ m₂ h₂ he => hi m₁ (modsLe_steps hm hs m₁ h₁) m₂ (modsLe_steps hm hs m₂ h₂) he

/-- **`ReachE` from the source**: `StripInj` and `NamesBnd` at the source, and round 6's
selection bounds at every reachable configuration, for a host that invents no module. -/
theorem reachE_of_stripInj {P : Profile} {host : HostSemantics H} (hm : HostModsSub host)
    {c₀ : Config H} (hi : StripInj c₀) (hn : NamesBnd c₀)
    (hb : ∀ c, Steps P host c₀ c → Round6.MemSimd.BoundedSelE c) : ReachE P host c₀ :=
  fun c hc => ⟨⟨hb c hc, namesBnd_steps hm hn hc⟩, stripInj_steps hm hi hc⟩

/-- **`RunDomE` from the source**, for a host that invents no module. -/
theorem runDomE_of_stripInj {P : Profile} {host : HostSemantics H} (hm : HostModsSub host)
    {c₀ : Config H} {ts : List CValType} (hok : ConfigOk c₀ ts) (hi : StripInj c₀)
    (hn : NamesBnd c₀) (hb : ∀ c, Steps P host c₀ c → Round6.MemSimd.BoundedSelE c) :
    Atlas.SpecTecR7Runs.RunDomE P host c₀ :=
  ⟨⟨ts, hok⟩, reachE_of_stripInj hm hi hn hb⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.HostMods
