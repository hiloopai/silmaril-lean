module

public import Silmaril.Proofs.Wasm.Models.FXPresI.Step

/-!
# `CtI` is preserved by Core steps: the induction

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPresI

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres Silmaril.Wasm.Models.FXPresI
open Silmaril.Proofs.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {m₀ : ModuleInst} {ι : CValType → FTy} {nt : TypeIdx → FTy}

/-- A rule whose left-hand side has an instruction outside the fragment. -/
macro "absurdI" : tactic =>
  `(tactic| exact keeps_absurd (by simp [okB, vals, throwing, constI32, Val.i32, Val.toAdmin]))

/-- `ctxt-instrs`. -/
theorem keeps_seq {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (ih : Keeps m₀ ι nt ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Keeps m₀ ι nt ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  intro _ _ _ _ _ ht
  simp only [List.map_append] at ht
  obtain ⟨m₁, m₂, h₁, h₂, h₃⟩ := TL.split3 ht
  obtain ⟨hs, hf, h₂'⟩ := ih h₂
  refine ⟨hs, hf, ?_⟩
  simpa only [List.map_append] using TL.append3 h₁ h₂' h₃

/-- `throw_ref-instrs`. -/
theorem keeps_throw {s : Store H} {f : Frame} {vs : List Val} {a : Nat} {rest : List Admin} :
    Keeps m₀ ι nt ⟨s, f, vals vs ++ throwing a ++ rest⟩ ⟨s, f, throwing a⟩ := by
  refine keeps_code fun ht => ?_
  simp only [List.map_append] at ht
  obtain ⟨m₁, m₂, -, h₂, -⟩ := TL.split3 ht
  obtain ⟨pre, i₀, o₀, hc, -, -⟩ := TL.invI (by rfl) (by simp [IsCtl]) h₂
  cases hc with
  | refExn ha => exact TL.throwingI ha

theorem keeps_parametric {s : Store H} {f : Frame} {is is' : List Admin}
    (h : ParametricStep is is') : Keeps m₀ ι nt ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  cases h with
  | unreachable => exact keeps_trap
  | nop => exact keeps_nop
  | drop v => exact keeps_drop v
  | selectTrue => absurdI
  | selectFalse => absurdI

theorem keeps_numeric {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (h : NumericStep P is is') : Keeps m₀ ι nt ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  cases h with
  | intUnOp => exact keeps_un (fun h => by cases h; simp) rfl (by simp [IsCtl]) .intConst
  | intBinOp => exact keeps_bin (fun h => by cases h; simp) rfl (by simp [IsCtl]) .intConst
  | intBinOpTrap => exact keeps_trap
  | intTestOp => exact keeps_un (fun h => by cases h; simp) rfl (by simp [IsCtl]) .intConst
  | intRelOp => exact keeps_bin (fun h => by cases h; simp) rfl (by simp [IsCtl]) .intConst
  | floatUnOp => absurdI
  | floatBinOp => absurdI
  | floatRelOp => absurdI
  | convert => absurdI
  | convertTrap => absurdI

/-- **A Core step on `TL`-typed Core code keeps the store, the frame and the type.** -/
theorem stepI {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : Step P host c c') :
    Keeps m₀ ι nt c c' := by
  induction h with
  | parametric h => exact keeps_parametric h
  | numeric h => exact keeps_numeric h
  | vector h => cases h <;> absurdI
  | «variable» h => cases h <;> absurdI
  | table h => cases h <;> absurdI
  | memory h => cases h <;> absurdI
  | reference h => cases h <;> absurdI
  | aggregate h => cases h <;> absurdI
  | ctxtInstrs _ _ ih => exact keeps_seq ih
  | trapInstrs => exact keeps_trap
  | throwRefInstrs => exact keeps_throw
  | callRefFunc => exact keeps_absurd ⟨_, List.mem_append_right _ List.mem_cons_self, rfl⟩
  | callRefHost => exact keeps_absurd ⟨_, List.mem_append_right _ List.mem_cons_self, rfl⟩
  | callRefHostDiv => exact keeps_absurd ⟨_, List.mem_append_right _ List.mem_cons_self, rfl⟩
  | _ => absurdI

end Silmaril.Proofs.Wasm.Models.FXPresI
