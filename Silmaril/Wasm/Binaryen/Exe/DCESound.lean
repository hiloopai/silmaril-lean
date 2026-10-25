module

public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.Pass.DCECheck

@[expose] public section

/-! # Soundness of the DCE stage

The executable checked DCE (`Exe/DCEExe.lean`) is `Binaryen.dceChecked`
(`Pass/DCECheck.lean`), and `dce_stageOk` is its stage contract, the theorem of the
DeadCodeElimination row of `PassRegistry.lean`. A leaf file, imported by
`Exe/PipelineSound.lean`.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen Execution.Core Numerics Validation ModuleWf

mutual
theorem Dce.dceE_eq : ∀ e : BExpr, Dce.dceE e = Binaryen.dceE e
  | .op i args => by simp only [Dce.dceE, Binaryen.dceE, Dce.dceL_eq args]
  | .block bt b => by simp only [Dce.dceE, Binaryen.dceE, Dce.dceL_eq b]
  | .loop bt b => by simp only [Dce.dceE, Binaryen.dceE, Dce.dceL_eq b]
  | .if_ bt c t e => by
      simp only [Dce.dceE, Binaryen.dceE, Dce.dceL_eq c, Dce.dceL_eq t, Dce.dceL_eq e]
  | .tryTable bt cs b => by simp only [Dce.dceE, Binaryen.dceE, Dce.dceL_eq b]
theorem Dce.dceL_eq : ∀ es : List BExpr, Dce.dceL es = Binaryen.dceL es
  | [] => rfl
  | e :: es => by simp only [Dce.dceL, Binaryen.dceL, Dce.dceE_eq e, Dce.dceL_eq es]
end

theorem Dce.endsInBotB_eq : Dce.endsInBotB = Binaryen.endsInBotB := rfl

mutual
theorem Dce.dceSafeWEB_eq : ∀ e : BExpr, Dce.dceSafeWEB e = Binaryen.dceSafeWEB e
  | .op _ args => by
      simp only [Dce.dceSafeWEB, Binaryen.dceSafeWEB, Dce.dceSafeWB_eq args, Dce.dceL_eq,
        Dce.endsInBotB_eq]
  | .block _ b => by simp only [Dce.dceSafeWEB, Binaryen.dceSafeWEB, Dce.dceSafeWB_eq b]
  | .loop _ b => by simp only [Dce.dceSafeWEB, Binaryen.dceSafeWEB, Dce.dceSafeWB_eq b]
  | .tryTable _ _ b => by simp only [Dce.dceSafeWEB, Binaryen.dceSafeWEB, Dce.dceSafeWB_eq b]
  | .if_ _ c t e => by
      simp only [Dce.dceSafeWEB, Binaryen.dceSafeWEB, Dce.dceSafeWB_eq c, Dce.dceSafeWB_eq t,
        Dce.dceSafeWB_eq e, Dce.dceL_eq, Dce.endsInBotB_eq]
theorem Dce.dceSafeWB_eq : ∀ es : List BExpr, Dce.dceSafeWB es = Binaryen.dceSafeWB es
  | [] => rfl
  | e :: es => by
      simp only [Dce.dceSafeWB, Binaryen.dceSafeWB, Dce.dceSafeWEB_eq e, Dce.dceSafeWB_eq es,
        Dce.dceE_eq, Dce.endsInBotB_eq]
end

/-- The executable checked DCE is `Binaryen.dceChecked`. -/
theorem Dce.dceChecked_eq : Dce.dceChecked = Binaryen.dceChecked := by
  have h : Dce.dceBodyChecked = Binaryen.dceBodyChecked := by
    funext b
    simp only [Dce.dceBodyChecked, Binaryen.dceBodyChecked, Dce.dceSafeWB_eq, Dce.dceL_eq]
  funext m
  simp only [Dce.dceChecked, Binaryen.dceChecked, BModule.mapBodies, h]

section PassAPI

open PassAPI

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

/-- Checked DCE keeps validity and is export-equivalent (closed host). -/
theorem dce_stageOk : StageOk o H Dce.dceChecked := by
  rw [Dce.dceChecked_eq]
  exact fun _ hm => ⟨dceChecked_ok hm.ok, dceChecked_sound_closed hm.ok⟩

end PassAPI

end Silmaril.Wasm.Binaryen.Exe
