module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Pos.Guard

/-!
# Round 5: `PosTyping` is uninhabited and `Round4.Task.wholeStepValid` is false

The witness is `expNopCfg`: `nop` in a frame over `ConfigOk.exportModule` (one global, exported
as `"g"`), on `ConfigOk.exportStore`. It is valid (`ConfigOk`, as track configok's
`exportConfig`) and bounded, and Core steps from it to the empty code. Its frame is not typed in
any `simEnv B` (`Utf8.lean`: `$utf8("g")` never evaluates), so:

* `not_posTyping`: `Round4.PosTyping B hn` fails at its `moduleinst` field, for every `B`, `hn`;
* `not_typed_expNopCfg`: `ConfigOk ∧ Bounded` does not give `Typed`;
* `not_wholeStepValid`: SpecTec cannot step from its image (`not_sstep_of_frame`), so the forward
  conjunct of the frozen round-4 target fails, for every `B`, at the injective `hnU`, the finite
  host `divHost` and every profile;
* `not_wholeStepValid_hostOk`: the same with the target restricted to `HostOk` hosts
  (`divHost` is `HostOk`): restricting hosts does not repair the target.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Pos

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

variable {H : Type}

/-- `nop` in a frame over the exporting module. -/
def expNopCfg : Config H := ⟨ConfigOk.exportStore, ⟨[], ConfigOk.exportModule⟩, [.plain .nop]⟩

/-- Its successor. -/
def expDoneCfg : Config H := ⟨ConfigOk.exportStore, ⟨[], ConfigOk.exportModule⟩, []⟩

theorem configOk_expNopCfg : ConfigOk (expNopCfg (H := H)) [] := by
  obtain ⟨C, hC⟩ := ConfigOk.moduleInstOk_exportModule (H := H)
  exact ⟨_, ⟨ConfigOk.coreStoreOk_exportStore, C, [], hC, .nil, rfl⟩,
    .single (.plain (.parametric .nop))⟩

theorem moduleBnd_exportModule : Round4.ModuleBnd ConfigOk.exportModule :=
  ⟨by simp [ConfigOk.exportModule], by simp [ConfigOk.exportModule]; decide⟩

/-- The exporting store is bounded. -/
theorem storeBnd_exportStore : Round4.StoreBnd (ConfigOk.exportStore (H := H)) :=
  ⟨by simp [ConfigOk.exportStore],
    by
      simp only [ConfigOk.exportStore, List.mem_singleton]
      rintro _ rfl
      rfl,
    by simp [ConfigOk.exportStore], by simp [ConfigOk.exportStore],
    by simp [ConfigOk.exportStore], by simp [ConfigOk.exportStore],
    by simp [ConfigOk.exportStore]⟩

theorem storeOk_exportStore : Integrate.StoreOk (ConfigOk.exportStore (H := H)) :=
  ⟨⟨by simp [ConfigOk.exportStore], by simp [ConfigOk.exportStore]⟩,
    ⟨by simp [ConfigOk.exportStore], by simp [ConfigOk.exportStore],
      by simp [ConfigOk.exportStore]⟩,
    by simp [ConfigOk.exportStore]⟩

theorem bounded_expNopCfg : Round4.Bounded (expNopCfg (H := H)) :=
  ⟨storeOk_exportStore, storeBnd_exportStore, moduleBnd_exportModule,
    by simp [expNopCfg, Round4.AdminsBnd, Round4.AdminBnd, Round4.instrBnd]⟩

theorem bounded_expDoneCfg : Round4.Bounded (expDoneCfg (H := H)) :=
  ⟨storeOk_exportStore, storeBnd_exportStore, moduleBnd_exportModule, trivial⟩

theorem step_expNopCfg (P : Profile) (host : HostSemantics H) :
    Step P host (expNopCfg (H := H)) expDoneCfg := .parametric .nop

/-- The exporting module is not a typed `moduleinst`. -/
theorem not_typedV_exportModule (B : Builtins) :
    ¬ TypedV (simEnv B) (.varT "moduleinst" [])
      (Silmaril.SpecTec.Equiv.RuntimeBridge.moduleInstToValue CT ConfigOk.exportModule) :=
  not_typedV_moduleinst_of_export B _ ⟨"g", .global 0⟩ (by simp [ConfigOk.exportModule]) 'g' rfl

/-- **`Round4.PosTyping` is uninhabited**, for every `B` and encoding. -/
theorem not_posTyping (B : Builtins) (hn : H → String) : ¬ Round4.PosTyping B hn := fun K => by
  obtain ⟨C, hC⟩ := ConfigOk.moduleInstOk_exportModule (H := H)
  exact not_typedV_exportModule B (K.moduleinst _ _ _ hC moduleBnd_exportModule)

/-- The frame over the exporting module is not a typed `frame`. -/
theorem not_typedV_frame_export (B : Builtins) :
    ¬ TypedV (simEnv B) frameT (frameV ⟨[], ConfigOk.exportModule⟩) := by
  intro h
  have hF := ConfigOk.hasTypFields_of_closedStruct ConfigOk.valsOnly_empty Typing.findTyp_frame
    (h _ ConfigOk.valsOnly_empty)
  simp only [List.forall₂_cons, ConfigOk.fieldTyp] at hF
  exact not_typedV_exportModule B (Typing.typedV_of_hasTyp ConfigOk.valsOnly_empty hF.2.1)

/-- **A valid, bounded configuration that is not `Typed`**, in any `simEnv B`. -/
theorem not_typed_expNopCfg (B : Builtins) (hn : H → String) :
    ¬ Typed (simEnv B) hn (expNopCfg (H := H)) := fun h =>
  not_typedV_frame_export B
    (((Typing.typingFacts_simEnv B hn).state _ _).1
      (((Typing.typingFacts_simEnv B hn).config _).1 h).1).2

/-- **SpecTec does not step from the image of `expNopCfg`**, in any `simEnv B`. -/
theorem not_sstep_expNopCfg (B : Builtins) (hn : H → String) (w : Value) :
    ¬ SStep (simEnv B) (configV hn (expNopCfg (H := H))) w :=
  not_sstep_of_frame (not_typedV_frame_export B) w

/-- The host whose every call diverges. -/
def divHost : HostSemantics Unit := fun _ _ _ o => o = .diverged

theorem hostFinite_divHost : HostFinite divHost :=
  fun _ _ _ => ⟨[.diverged], fun _ => by simp [divHost]⟩

theorem hostOk_divHost : HostOk divHost := fun _ _ _ _ _ _ _ _ _ _ _ =>
  ⟨⟨_, rfl⟩, fun out h => by cases h; trivial⟩

/-- **The forward one-step simulation fails at `expNopCfg`**, for every `B`. -/
theorem not_forward_expNopCfg (B : Builtins) (P : Profile) (host : HostSemantics H)
    (hn : H → String) :
    ¬ ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → Round4.Bounded c →
      Round4.Bounded c' → Step P host c c' →
      ∃ d', Bwd.ConfigEq c' d' ∧ SStep (simEnv B) (configV hn c) (configV hn d') := fun h => by
  obtain ⟨d', -, hs⟩ := h expNopCfg expDoneCfg [] configOk_expNopCfg bounded_expNopCfg
    bounded_expDoneCfg (step_expNopCfg P host)
  exact not_sstep_expNopCfg B hn _ hs

/-- **`Round4.Task.wholeStepValid` is false.** -/
theorem not_wholeStepValid : ¬ Round4.Task.wholeStepValid := fun h => by
  obtain ⟨B, hf, -⟩ := h Unit hnU hnU_injective divHost hostFinite_divHost false {}
  exact not_forward_expNopCfg B _ divHost hnU hf

/-- **The round-4 target restricted to `HostOk` hosts is false too**: the failure is not a
host's. -/
theorem not_wholeStepValid_hostOk :
    ¬ ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins, Round4.OneStep B hn (Profile.spec nd r) host :=
  fun h => by
    obtain ⟨B, hf, -⟩ := h Unit hnU hnU_injective divHost hostFinite_divHost hostOk_divHost false {}
    exact not_forward_expNopCfg B _ divHost hnU hf

end Silmaril.Wasm.SpecTec.Sim.Round5.Pos
