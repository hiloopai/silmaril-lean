module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.HostMods.Step
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.Thms

/-!
# REI without `HostExportParam`: the host hypotheses

* `hostModsSub_of_param`: `HostFinite` and `HostExportParam` give `HostModsSub`
  (`Round7.Swap.host_mods_sub`).
* `allIn_outcomeV_of_mods`: `Round7.Swap.allIn_outcomeV_of_host` from `HostModsSub` alone.
* `hostModMapAt_of_fix`: a rewriting that fixes every module of the calling store is a
  `HostModMapAt` there, for a host that invents no module.
* `hostModMapAt_unstrip`: un-stripping along `c` at the stripped store of `c`, for an export-blind
  host that invents no module, under `StripInj c`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HostMods

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap

variable {H : Type}

/-- **A finite, export-parametric host invents no module.** -/
theorem hostModsSub_of_param {host : HostSemantics H} (hf : HostFinite host)
    (hp : HostExportParam host) : HostModsSub host :=
  fun _ _ _ _ _ ho => host_mods_sub hf hp ho

/-- **The outcomes of a host that invents no module stay in `AllIn Q`**, when the module records
of the calling store satisfy `Q`. -/
theorem allIn_outcomeV_of_mods {Q : Value → Prop} (hn : H → String) {host : HostSemantics H}
    (hm : HostModsSub host) {h : H} {s : Store H} {vs : List Val}
    {o : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result}
    (hs : ∀ fi ∈ s.funcs, Q (moduleInstToValue CT fi.module)) (ho : host h s vs o) :
    AllIn Q (outcomeV hn o) := by
  cases o with
  | diverged => simp [outcomeV, AllIns]
  | returned s' r =>
    have hs' : ∀ fi ∈ s'.funcs, Q (moduleInstToValue CT fi.module) := by
      intro fi hfi
      obtain ⟨fi₁, hfi₁, he⟩ := List.mem_map.1 (hm h s s' vs r ho fi hfi)
      rw [← he]
      exact hs fi₁ hfi₁
    simp only [outcomeV, AllIn_case, AllIn_tuple, AllIns_cons, AllIns_nil, and_true]
    exact ⟨allIn_storeV hn hs', allIn_of_nxB Q _ (nxB_resultV r)⟩

/-- `mapStore μ` is the identity on a store whose modules `μ` fixes. -/
theorem mapStore_id_of {μ : ModuleInst → ModuleInst} {s : Store H}
    (h : ∀ fi ∈ s.funcs, μ fi.module = fi.module) : mapStore μ s = s := by
  have hF : s.funcs.map (mapFI μ) = s.funcs := by
    refine (List.map_congr_left fun fi hfi => ?_).trans (List.map_id s.funcs)
    simp only [mapFI, id_eq, h fi hfi]
  simp only [mapStore, hF]

/-- `mapOutcome μ` is the identity on an outcome whose modules `μ` fixes. -/
theorem mapOutcome_id_of {μ : ModuleInst → ModuleInst}
    {o : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result}
    (h : ∀ s' r, o = .returned s' r → ∀ fi ∈ s'.funcs, μ fi.module = fi.module) :
    mapOutcome μ o = o := by
  cases o with
  | diverged => rfl
  | returned s' r => simp only [mapOutcome, mapStore_id_of (h s' r rfl)]

/-- **A rewriting that fixes the calling store's modules is a `HostModMapAt` there**, for a host
that invents no module. -/
theorem hostModMapAt_of_fix {host : HostSemantics H} (hm : HostModsSub host)
    {μ : ModuleInst → ModuleInst} {s : Store H} (hfix : ∀ fi ∈ s.funcs, μ fi.module = fi.module) :
    HostModMapAt host μ s := by
  intro h vs o ho
  rw [mapStore_id_of hfix]
  refine (mapOutcome_id_of fun s' r he fi hfi => ?_).symm ▸ ho
  subst he
  obtain ⟨fi₁, hfi₁, he₁⟩ := List.mem_map.1 (hm h s s' vs r ho fi hfi)
  rw [← he₁]
  exact hfix fi₁ hfi₁

theorem mapOutcome_comp (μ ν : ModuleInst → ModuleInst)
    (o : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result) :
    mapOutcome μ (mapOutcome ν o) = mapOutcome (μ ∘ ν) o := by
  cases o with
  | diverged => rfl
  | returned s r =>
    simp only [mapOutcome, mapStore, List.map_map]
    rfl

theorem mapOutcome_stripModule (o : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result) :
    mapOutcome stripModule o = stripOutcome o := by
  cases o <;> rfl

/-- The store's modules are modules of the configuration. -/
theorem mem_mods_store {c : Config H} {fi : FuncInst H} (hfi : fi ∈ c.store.funcs) :
    fi.module ∈ mods c :=
  List.mem_append_left _ (List.mem_map_of_mem hfi)

/-- **Un-stripping along `c` at the stripped store of `c`**, under `StripInj c`, for an
export-blind host that invents no module. -/
theorem hostModMapAt_unstrip {host : HostSemantics H} (hm : HostModsSub host)
    (hb : HostExportBlind host) {c : Config H} (hinj : StripInj c) :
    HostModMapAt host (unstrip c) (stripStore c.store) := by
  intro h vs o' ho'
  obtain ⟨o, ho, rfl⟩ := hb.2 h c.store vs o' ho'
  have hfix : ∀ fi ∈ c.store.funcs, (unstrip c ∘ stripModule) fi.module = fi.module :=
    fun fi hfi => unstrip_strip hinj (mem_mods_store hfi)
  have hs : mapStore (unstrip c) (stripStore c.store) = c.store := by
    rw [← EraseDer.mapStore_stripModule]
    simp only [mapStore, List.map_map]
    exact mapStore_id_of hfix
  rw [hs, ← mapOutcome_stripModule, mapOutcome_comp]
  have := hostModMapAt_of_fix hm hfix h vs o ho
  rwa [mapStore_id_of hfix] at this
