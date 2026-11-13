module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.SegRun
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateComplete
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# Validated modules have constant segment offsets

`offsetsConst_of_moduleOk`: the offsets of the active element and data segments of a valid
module consist of constant instructions (`ElemModeOk`/`DataModeOk` require `ExprOkConst`), so
validated modules satisfy the hypothesis `OffsetsConst` of the segment-initialisation run.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core

theorem forall₂_exists_of_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ a ∈ l, ∃ b, R a b
  | _, _, .nil, _, ha => absurd ha List.not_mem_nil
  | _, _, .cons hr hs, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact ⟨_, hr⟩
    · exact forall₂_exists_of_mem hs a ha'

/-- **Validated modules have constant active-segment offsets.** -/
theorem offsetsConst_of_moduleOk {m : Module} {mt : CModuleType} (h : ModuleOk m mt) :
    OffsetsConst m := by
  cases h with
  | mk _ _ _ _ _ _ _ _ _ hdata helems _ _ _ =>
    refine ⟨fun e he y off hmode i hi => ?_, fun d hd y off hmode i hi => ?_⟩
    · obtain ⟨rt, -, -, -, hm⟩ := forall₂_exists_of_mem helems e he
      rw [hmode] at hm
      cases hm with
      | active _ _ ho => exact (ho.const i hi).isConstI
    · have hm : DataModeOk _ d.mode := hdata d hd
      rw [hmode] at hm
      cases hm with
      | active _ ho => exact (ho.const i hi).isConstI

/-- `validate?` gives constant active-segment offsets. -/
theorem offsetsConst_of_validate {m : Module} {mt : CModuleType} (h : validate? m = some mt) :
    OffsetsConst m :=
  offsetsConst_of_moduleOk (validate?_sound h)

end Silmaril.Proofs.Wasm.Game.SpecGlobals
