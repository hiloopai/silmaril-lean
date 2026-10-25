module

public import Silmaril.Wasm.Binaryen.Toolkit.CtorEvalSound
public import Silmaril.Wasm.Binaryen.PassAPI.ModuleModes

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit.CtorEval

open Execution.Core Numerics Validation

variable {H : Type}

/-- Direct Core-module passes use the same contract and shared composition API
as folded Binaryen passes; the tool's explicit unsupported-input rejection is
kept separately in `evaluate`. -/
def equivalenceP (P : Profile) :
    Silmaril.Compile.PassAPI.Pass (Modes.moduleContract .equivalence P (closedHost (H := H))) where
  run := optimize
  inv_run {x} valid := by
    unfold optimize
    split
    · exact ⟨_, module_ok _ _ _ true⟩
    · exact valid
  sound {x} _ := by
    change Modes.ExportCorrect .equivalence P closedHost x (optimize x)
    unfold optimize
    split
    · rename_i p recognized
      rw [recognize?_sound recognized]
      exact exportCorrect p.type p.initial p.value
    · exact Modes.ExportCorrect.refl _ _ _ _

theorem evaluate_sound {source result : Module} (h : evaluate source = .ok result) (P : Profile) :
    ModuleValid result ∧ Modes.ExportCorrect .equivalence P (closedHost (H := H)) source result := by
  unfold evaluate at h
  split at h
  · rename_i p recognized
    cases Except.ok.inj h
    exact ⟨⟨_, module_ok _ _ _ true⟩, recognize?_sound recognized ▸ exportCorrect p.type p.initial p.value⟩
  · cases h

theorem evaluate_eq_pass_run {source result : Module} (h : evaluate source = .ok result)
    (P : Profile) : (equivalenceP (H := H) P).run source = result := by
  unfold evaluate at h
  change optimize source = result
  unfold optimize
  split at h
  · rename_i p recognized
    exact Except.ok.inj h
  · cases h

end Silmaril.Wasm.Binaryen.Toolkit.CtorEval
