module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.REGap.Host
public import Silmaril.Wasm.SpecTec.Sim.Round7.NopEx.Thms
public import Silmaril.Wasm.Execution.Core.Exec.SegmentInitLoops

/-!
# REH gaps: a valid configuration without `StripInj` (proofs)

`collideCfg` runs, inside round 5's exporting frame (`ConfigOk.exportModule`, which exports
global `0` as `"g"`), an empty frame of the same module with its exports removed. It is valid,
in `BoundedSelE`, and steps to round 5's `expDoneCfg`. Its two module instances differ only in
their export lists, so `StripInj` fails.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.REGap

open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round5.Pos (expDoneCfg)
open Silmaril.Wasm.SingleThreaded.Det (Head famOf_of_shape ParametricStep.shape NumericStep.shape
  VectorStep.shape VariableStep.shape TableStep.shape MemoryStep.shape RefStep.shape
  AggregateStep.shape)

variable {H : Type}

/-- Round 5's exporting module with its exports removed. -/
def collideModule : ModuleInst := stripModule ConfigOk.exportModule

/-- **An empty frame of `collideModule` inside the frame of `ConfigOk.exportModule`.** -/
def collideCfg : Config H :=
  ⟨ConfigOk.exportStore, ⟨[], ConfigOk.exportModule⟩, [.frame 0 ⟨[], collideModule⟩ []]⟩

theorem configOk_collide : ConfigOk (collideCfg (H := H)) [] := by
  obtain ⟨C, hC⟩ := ConfigOk.moduleInstOk_exportModule (H := H)
  have hf : FrameOk (ConfigOk.exportStore (H := H)) ⟨[], collideModule⟩
      { C with locals := C.locals ++ [] } :=
    ⟨C, [], moduleInstOk_stripAt hC, .nil, rfl⟩
  exact ⟨_, ⟨ConfigOk.coreStoreOk_exportStore, C, [], hC, .nil, rfl⟩,
    .single (.frame hf rfl .nil (fun _ h => absurd h List.not_mem_nil))⟩

theorem boundedSelE_collide : BoundedSelE (collideCfg (H := H)) := by
  have hb : Round4.ModuleBnd collideModule := moduleBnd_strip Round5.Pos.moduleBnd_exportModule
  refine ⟨⟨⟨Round5.Pos.storeOk_exportStore, Round5.Pos.storeBnd_exportStore,
    Round5.Pos.moduleBnd_exportModule, ⟨hb, trivial⟩, trivial⟩, ⟨?_, ⟨trivial, trivial⟩⟩⟩,
    NopEx.namesBnd_exp ⟨⟨fun _ h => absurd h List.not_mem_nil, trivial⟩, trivial⟩⟩
  simp [Round5.Target.StoreSel, collideCfg, ConfigOk.exportStore]

theorem collideModule_ne : ConfigOk.exportModule ≠ collideModule :=
  stripModule_ne (by simp [ConfigOk.exportModule])

/-- **`collideCfg` fails `StripInj`**: its frame's module and the inner frame's module differ
only in their export lists. -/
theorem not_stripInj_collide : ¬ StripInj (collideCfg (H := H)) := fun hi =>
  collideModule_ne (hi _ (by simp [mods, collideCfg, ConfigOk.exportStore]) _
    (by simp [mods, collideCfg, ConfigOk.exportStore, modsAdmins, modsAdmin]) rfl)

/-- **`collideCfg` steps to `expDoneCfg`**, for every profile and host (`frame-vals`). -/
theorem step_collide (P : Profile) (host : HostSemantics H) :
    Step P host (collideCfg (H := H)) expDoneCfg :=
  Step.frameVals (vs := []) rfl

/-- **`expDoneCfg` is the only successor of `collideCfg`**, for every profile and host. The code
is call-free, so the step is host-free (`NopEx.step_noHost_of_callFree`) and a head step at the
frame (`Step.head_inv`). Of the head rules at a frame, only `frame-vals` matches an empty body. -/
theorem step_collide_inv {P : Profile} {host : HostSemantics H} {c : Config H}
    (hs : Step P host (collideCfg (H := H)) c) : c = expDoneCfg := by
  have h₀ := NopEx.step_noHost_of_callFree hs rfl
  obtain ⟨pre, args, c₀, hpa, hH, rfl⟩ :=
    Step.head_inv (ws := []) (rest := []) h₀ rfl (by simp) (by simp)
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hpa.symm
  cases hH with
  | parametric hp => exact absurd (famOf_of_shape (ParametricStep.shape hp)).2 (by decide)
  | numeric hp => exact absurd (famOf_of_shape (NumericStep.shape hp)).2 (by decide)
  | vector hp => exact absurd (famOf_of_shape (VectorStep.shape hp)).2 (by decide)
  | «variable» hp => exact absurd (famOf_of_shape (VariableStep.shape hp)).2 (by decide)
  | table hp => exact absurd (famOf_of_shape (TableStep.shape hp)).2 (by decide)
  | memory hp => exact absurd (famOf_of_shape (MemoryStep.shape hp)).2 (by decide)
  | reference hp => exact absurd (famOf_of_shape (RefStep.shape hp)).2 (by decide)
  | aggregate hp => exact absurd (famOf_of_shape (AggregateStep.shape hp)).2 (by decide)
  | ctxtFrame hp => exact absurd hp (Step.not_vals (vs := []))
  | frameVals hb hn =>
    obtain rfl : _ = [] := by simpa using hb.symm
    rfl
  | returnCallRefFrameNull hb => simp at hb
  | returnCallRefFrameAddr hb => simp at hb
  | returnFrame hb => simp at hb
  | callRefFunc _ hc => exact hc.elim

/-- **Every successor of `collideCfg` is in `BoundedSelE`**, so `collideCfg` is in the domain of
both halves of `Round7.Task.wholeStepValidREH`. -/
theorem succ_boundedSelE_collide {P : Profile} {host : HostSemantics H} {c : Config H}
    (h : Step P host (collideCfg (H := H)) c) : BoundedSelE c :=
  step_collide_inv h ▸ NopEx.boundedSelE_expDone

end Silmaril.Wasm.SpecTec.Sim.Round7.REGap
