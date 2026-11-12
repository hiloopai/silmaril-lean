module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Runs.Assemble

/-!
# Round 7, runs: `StripInj` along deterministic Core steps

`ReachE` asks for `StripInj` at every reachable configuration. Along deterministic steps it is
inherited from the source, for an export-parametric host:

* `mods_sub_of_det`: if `c` has exactly one successor `c'`, every module instance of `c'` is one
  of `c`. The proof does not inspect Core's rules. The export-only rewriting `bump c` fixes the
  modules of `c` and changes every other module (it adds an export). By `Round7.step_mapConfig`
  it sends the step `c → c'` to a step `c → mapConfig (bump c) c'`, so determinism gives
  `mapConfig (bump c) c' = c'`, and `bump c` fixes every module of `c'` (`fix_of_mapConfig_id`).
* `stripInj_of_det`: hence `StripInj c → StripInj c'`.
* `reachE_of_det`: on a source all of whose reachable configurations have at most one Core
  successor, `ReachE` follows from `StripInj` at the source and `BoundedSelE` everywhere.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Runs

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-! ## A rewriting fixes exactly the modules it leaves in place -/

/-- A map that fixes a list fixes its members. -/
theorem map_fix {α : Type} {f : α → α} : ∀ {l : List α}, l.map f = l → ∀ a ∈ l, f a = a
  | [], _ => fun _ ha => absurd ha List.not_mem_nil
  | b :: l, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      intro a ha
      rcases List.mem_cons.1 ha with rfl | ha
      · exact h.1
      · exact map_fix h.2 a ha

section
variable {μ : ModuleInst → ModuleInst}

mutual
theorem fix_of_mapAdmin : ∀ a : Admin, mapAdmin μ a = a → ∀ m ∈ modsAdmin a, μ m = m
  | .label n cont body, h => by
      simp only [mapAdmin, Admin.label.injEq, true_and] at h
      exact fix_of_mapAdmins body h
  | .handler n cs body, h => by
      simp only [mapAdmin, Admin.handler.injEq, true_and] at h
      exact fix_of_mapAdmins body h
  | .frame n f body, h => by
      simp only [mapAdmin, mapFrame, Admin.frame.injEq, true_and] at h
      intro m hm
      simp only [modsAdmin, List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact congrArg Frame.module h.1
      · exact fix_of_mapAdmins body h.2 m hm
  | .plain _, _ => fun _ hm => by simp [modsAdmin] at hm
  | .ref _, _ => fun _ hm => by simp [modsAdmin] at hm
  | .callRefType _, _ => fun _ hm => by simp [modsAdmin] at hm
  | .returnCallRefType _, _ => fun _ hm => by simp [modsAdmin] at hm
  | .trap, _ => fun _ hm => by simp [modsAdmin] at hm

theorem fix_of_mapAdmins : ∀ l : List Admin, mapAdmins μ l = l → ∀ m ∈ modsAdmins l, μ m = m
  | [], _ => fun _ hm => by simp [modsAdmins] at hm
  | a :: l, h => by
      simp only [mapAdmins, List.cons.injEq] at h
      intro m hm
      simp only [modsAdmins, List.mem_append] at hm
      rcases hm with hm | hm
      · exact fix_of_mapAdmin a h.1 m hm
      · exact fix_of_mapAdmins l h.2 m hm
end

/-- **If `mapConfig μ` fixes `c`, `μ` fixes every module of `c`.** -/
theorem fix_of_mapConfig_id {c : Config H} (h : mapConfig μ c = c) : ∀ m ∈ mods c, μ m = m := by
  obtain ⟨s, f, is⟩ := c
  simp only [mapConfig, Config.mk.injEq] at h
  obtain ⟨hs, hf, hc⟩ := h
  intro m hm
  simp only [mods, List.mem_append, List.mem_map, List.mem_cons] at hm
  rcases hm with ⟨fi, hfi, rfl⟩ | rfl | hm
  · have hF : s.funcs.map (mapFI μ) = s.funcs := congrArg Store.funcs hs
    exact congrArg FuncInst.module (map_fix hF fi hfi)
  · exact congrArg Frame.module hf
  · exact fix_of_mapAdmins is hc m hm

end

/-! ## The rewriting that moves every module outside `c` -/

/-- An export added to modules outside `c`. -/
def extraExport : ExportInst := ⟨"", .func 0⟩

/-- **Fix the modules of `c`, add an export to every other module.** -/
noncomputable def bump (c : Config H) (m : ModuleInst) : ModuleInst :=
  open Classical in
  if m ∈ mods c then m else { m with exports := extraExport :: m.exports }

theorem exportOnly_bump (c : Config H) : ExportOnly (bump c) := by
  intro m
  unfold bump
  split <;> rfl

theorem mem_of_bump_eq {c : Config H} {m : ModuleInst} (h : bump c m = m) : m ∈ mods c := by
  unfold bump at h
  split at h
  · assumption
  · have := congrArg (fun m : ModuleInst => m.exports.length) h
    simp at this

/-- **A configuration's only successor has no new module instances**, for an export-parametric
host. -/
theorem mods_sub_of_det {P : Profile} {host : HostSemantics H} (hp : HostExportParam host)
    {c c' : Config H} (hs : Step P host c c') (hu : ∀ c₃, Step P host c c₃ → c₃ = c') :
    ∀ m ∈ mods c', m ∈ mods c := by
  have hst := step_mapConfig (exportOnly_bump c) (hp _ (exportOnly_bump c)) hs
  rw [mapConfig_id_of _ fun m hm => by unfold bump; simp [hm]] at hst
  have hfix := fix_of_mapConfig_id (hu _ hst)
  exact fun m hm => mem_of_bump_eq (hfix m hm)

/-- **`StripInj` passes to the only successor.** -/
theorem stripInj_of_det {P : Profile} {host : HostSemantics H} (hp : HostExportParam host)
    {c c' : Config H} (hi : StripInj c) (hs : Step P host c c')
    (hu : ∀ c₃, Step P host c c₃ → c₃ = c') : StripInj c' :=
  fun m₁ h₁ m₂ h₂ he =>
    hi m₁ (mods_sub_of_det hp hs hu m₁ h₁) m₂ (mods_sub_of_det hp hs hu m₂ h₂) he

/-- **`ReachE` on deterministic sources** from `StripInj` at the source alone. -/
theorem reachE_of_det {P : Profile} {host : HostSemantics H} (hp : HostExportParam host)
    {c₀ : Config H} (hi : StripInj c₀)
    (hb : ∀ c, Steps P host c₀ c → BoundedSelE c)
    (hd : ∀ c, Steps P host c₀ c → ∀ c₁ c₂, Step P host c c₁ → Step P host c c₂ → c₁ = c₂) :
    ReachE P host c₀ := by
  intro c hc
  refine ⟨hb c hc, ?_⟩
  induction hc with
  | refl => exact hi
  | @tail c₁ c₂ h₁ h₂ ih =>
    exact stripInj_of_det hp ih h₂ fun c₃ h₃ => hd c₁ h₁ c₃ c₂ h₃ h₂

/-! ## Round 6's domain is inside round 7's -/

mutual
theorem exports_of_adminNE : ∀ a : Admin, Round5.Pos.AdminNE a →
    (∀ m ∈ modsAdmin a, m.exports = []) ∧ AdminNB a
  | .label _ _ body, h => exports_of_adminsNE body h
  | .handler _ _ body, h => exports_of_adminsNE body h
  | .frame _ f body, h => by
      obtain ⟨h₁, h₂⟩ := exports_of_adminsNE body h.2
      refine ⟨fun m hm => ?_, fun e he => absurd (h.1 ▸ he) List.not_mem_nil, h₂⟩
      rcases List.mem_cons.1 hm with rfl | hm
      · exact h.1
      · exact h₁ m hm
  | .plain _, _ => ⟨fun _ hm => absurd hm List.not_mem_nil, trivial⟩
  | .ref _, _ => ⟨fun _ hm => absurd hm List.not_mem_nil, trivial⟩
  | .callRefType _, _ => ⟨fun _ hm => absurd hm List.not_mem_nil, trivial⟩
  | .returnCallRefType _, _ => ⟨fun _ hm => absurd hm List.not_mem_nil, trivial⟩
  | .trap, _ => ⟨fun _ hm => absurd hm List.not_mem_nil, trivial⟩

theorem exports_of_adminsNE : ∀ l : List Admin, Round5.Pos.AdminsNE l →
    (∀ m ∈ modsAdmins l, m.exports = []) ∧ AdminsNB l
  | [], _ => ⟨fun _ hm => absurd hm List.not_mem_nil, trivial⟩
  | a :: l, h => by
      obtain ⟨ha₁, ha₂⟩ := exports_of_adminNE a h.1
      obtain ⟨hl₁, hl₂⟩ := exports_of_adminsNE l h.2
      refine ⟨fun m hm => ?_, ha₂, hl₂⟩
      rcases List.mem_append.1 hm with hm | hm
      · exact ha₁ m hm
      · exact hl₁ m hm
end

/-- **An export-free configuration has no module with exports.** -/
theorem exports_of_noExports {c : Config H} (h : Round5.Pos.NoExports c) :
    ∀ m ∈ mods c, m.exports = [] := by
  intro m hm
  simp only [mods, List.mem_append, List.mem_map, List.mem_cons] at hm
  rcases hm with ⟨fi, hfi, rfl⟩ | rfl | hm
  · exact h.store fi hfi
  · exact h.frame
  · exact (exports_of_adminsNE c.code h.code).1 m hm

/-- **Round 6's selection bounds give round 7's**, and `StripInj`. -/
theorem boundedSelE_of_boundedSel {c : Config H} (h : Round5.Target.BoundedSel c) :
    BoundedSelE c ∧ StripInj c := by
  have hex := exports_of_noExports h.1.2
  refine ⟨⟨⟨h.1.1, h.2⟩, ⟨fun fi _ e he => ?_, fun e he => ?_,
    (exports_of_adminsNE c.code h.1.2.code).2⟩⟩, stripInj_of_stripped fun m hm => ?_⟩
  · exact absurd (h.1.2.store fi ‹_› ▸ he) List.not_mem_nil
  · exact absurd (h.1.2.frame ▸ he) List.not_mem_nil
  · obtain ⟨⟩ := m
    simp only [stripModule, ModuleInst.mk.injEq, true_and]
    exact (hex _ hm).symm

/-- **`ReachE` from round 6's `BoundedReachSel`**: runs at the round-7 reading cover round 6's
run domain. -/
theorem reachE_of_boundedReachSel {P : Profile} {host : HostSemantics H} {c : Config H}
    (h : Round5.Target.BoundedReachSel P host c) : ReachE P host c :=
  fun c' hc' => boundedSelE_of_boundedSel (h c' hc')

end Silmaril.Wasm.SpecTec.Sim.Round7.Runs
