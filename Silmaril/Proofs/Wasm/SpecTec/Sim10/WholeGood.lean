module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.WholeBwd

/-!
# The invariant `GoodV1` of the 1.0 backward target

`cfgInv_goodV1`: `GoodV1` (named resources exist, `StoreOk10`, `SelOk`, `GSetOk`) passes to label and frame
bodies and to infixes, so the recursion of `WholeBwd` runs under it, and
`wholeStepBwd10_of_parts` reduces `Task.wholeStepBwd10` to the per-rule obligations
`BwdParts10 GoodV1` at the spec's builtins.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)

variable {H : Type}

/-- `ResOkL10` holds element by element. -/
theorem resOkL10_iff {s : Store H} {f : Frame} :
    ∀ {l : List Admin}, ResOkL10 s f l ↔ ∀ a ∈ l, ResOkA10 s f a
  | [] => by simp [ResOkL10]
  | a :: l => by simp [ResOkL10, resOkL10_iff (l := l)]

/-- `Active` is inherited by a code sequence from any infix of it. -/
theorem _root_.Silmaril.Wasm.SpecTec.Sim10.Active.of_mid {l₁ l l₂ w : List Admin} (h : Active l w) :
    Active (l₁ ++ l ++ l₂) w := by
  induction h with
  | @piece m₁ w m₂ =>
    have e : l₁ ++ (m₁ ++ w ++ m₂) ++ l₂ = (l₁ ++ m₁) ++ w ++ (m₂ ++ l₂) := by
      simp only [List.append_assoc]
    rw [e]
    exact .piece
  | label hm hb _ => exact .label (List.mem_append_left _ (List.mem_append_right _ hm)) hb
  | frame hm hb _ => exact .frame (List.mem_append_left _ (List.mem_append_right _ hm)) hb

/-- `ActiveF` is inherited by a code sequence from any infix of it. -/
theorem _root_.Silmaril.Wasm.SpecTec.Sim10.ActiveF.of_mid {f f' : Frame} {l₁ l l₂ w : List Admin}
    (h : ActiveF f l f' w) : ActiveF f (l₁ ++ l ++ l₂) f' w := by
  induction h with
  | @piece f m₁ w m₂ =>
    have e : l₁ ++ (m₁ ++ w ++ m₂) ++ l₂ = (l₁ ++ m₁) ++ w ++ (m₂ ++ l₂) := by
      simp only [List.append_assoc]
    rw [e]
    exact .piece
  | label hm hb _ => exact .label (List.mem_append_left _ (List.mem_append_right _ hm)) hb
  | frame hm hb _ => exact .frame (List.mem_append_left _ (List.mem_append_right _ hm)) hb

/-- **`GoodV1` passes to label and frame bodies and to infixes.** -/
theorem cfgInv_goodV1 : CfgInv10 (GoodV1 (H := H)) where
  label _ _ _ _ _ h := ⟨by simpa [ResOkL10, ResOkA10] using h.1, h.2.1,
    fun a b c hw => h.2.2.1 a b c (.label (.head _) hw),
    fun f' v x a g hw => h.2.2.2 f' v x a g (.label (.head _) hw)⟩
  frame _ _ _ _ _ h := ⟨by simpa [ResOkL10, ResOkA10] using h.1, h.2.1,
    fun a b c hw => h.2.2.1 a b c (.frame (.head _) hw),
    fun f' v x a g hw => h.2.2.2 f' v x a g (.frame (.head _) hw)⟩
  mid _ _ _ _ _ h := ⟨resOkL10_iff.2 fun a ha =>
      resOkL10_iff.1 h.1 a (List.mem_append_left _ (List.mem_append_right _ ha)), h.2.1,
    fun a b c hw => h.2.2.1 a b c hw.of_mid, fun f' v x a g hw => h.2.2.2 f' v x a g hw.of_mid⟩

/-- **`Task.wholeStepBwd10` from the per-rule obligations at the spec's builtins.** The five
structural rules of 1.0's `Step` are discharged for every configuration. -/
theorem wholeStepBwd10_of_parts
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice),
        BwdParts10 GoodV1 (Sim.Floats.floatIntB (Profile.spec nd r)) hn host) :
    Task.wholeStepBwd10 := fun H hn hinj host nd r c w _ hg hs =>
  backward10_of_parts (h H hn hinj host nd r) cfgInv_goodV1 c w hg hs

end Silmaril.Wasm.SpecTec.Sim10.Whole
