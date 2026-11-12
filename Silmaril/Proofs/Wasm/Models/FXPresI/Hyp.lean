module

public import Silmaril.Proofs.Wasm.Models.FXPresI.Main

/-!
# `CoreHyp` for `envI`

`coreHypI`: the environment `envI m₀ ι nt` (Core part `CtI`, extension `ExtI`) satisfies
`FXPres.CoreHyp` for every profile, host and FX function table. Core preservation is `stepI`;
`cont.new` and FX calls are vacuous, because `CtI` types no function reference.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPresI

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres Silmaril.Wasm.Models.FXPresI
open Silmaril.Proofs.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {m₀ : ModuleInst} {ι : CValType → FTy} {nt : TypeIdx → FTy}

theorem extI_trans {s₁ s₂ s₃ : Store H} (h₁ : ExtI s₁ s₂) (h₂ : ExtI s₂ s₃) : ExtI s₁ s₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem ctI_mono {s s' : Store H} {a : Admin} {i o : List FTy} (he : ExtI s s')
    (h : CtI s a i o) : CtI s' a i o := by
  cases h with
  | refExn ha => exact .refExn (Nat.lt_of_lt_of_le ha he.2.length_le)
  | intConst => exact .intConst
  | intUnOp => exact .intUnOp
  | intBinOp => exact .intBinOp
  | intTestOp => exact .intTestOp
  | intRelOp => exact .intRelOp
  | nop => exact .nop
  | drop => exact .drop
  | unreachable => exact .unreachable
  | trap => exact .trap
  | throwRef => exact .throwRef

theorem ctI_throwRef {s : Store H} {i o : List FTy} (h : CtI s (.plain .throwRef) i o) :
    ∃ x, (∃ i₁, i = i₁ ++ [x]) ∧ ∀ i' o', CtI s (.plain .throwRef) (i' ++ [x]) o' := by
  cases h with
  | throwRef => exact ⟨exnTy, ⟨_, rfl⟩, fun _ _ => .throwRef⟩

theorem ctI_drop {s : Store H} {i o : List FTy} (h : CtI s (.plain .drop) i o) :
    ∃ x, i = [x] ∧ o = [] := by
  cases h with
  | drop => exact ⟨_, rfl, rfl⟩

theorem ctI_noFunc {s : Store H} {a : Nat} {i o : List FTy} (h : CtI s (.ref (.func a)) i o) :
    False := by
  cases h

/-- **`envI` satisfies `CoreHyp`**, for every profile, host and FX function table. -/
theorem coreHypI {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX} :
    CoreHyp (envI m₀ ι nt) P host fx where
  ext_refl _ := ⟨rfl, List.prefix_refl _⟩
  ext_trans := extI_trans
  ct_mono := ctI_mono
  tags_mono he h := he.1 ▸ h
  val := ctI_val
  trap _ _ _ := .trap
  throwRef := ctI_throwRef
  drop := ctI_drop
  core hs _ ht := by
    obtain ⟨hs', hf', ht'⟩ := stepI hs ht
    cases hs'
    cases hf'
    exact ⟨⟨rfl, List.prefix_refl _⟩, by assumption, ht'⟩
  exn s e _ _ _ :=
    ⟨⟨rfl, List.prefix_append _ _⟩, TL.throwingI (by simp [Store.addExn])⟩
  new _ h := (ctI_noFunc h).elim
  invoke _ _ _ _ h := (ctI_noFunc h).elim

end Silmaril.Proofs.Wasm.Models.FXPresI
