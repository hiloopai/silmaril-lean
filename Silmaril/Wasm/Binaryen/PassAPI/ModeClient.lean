module

public import Silmaril.Wasm.Binaryen.PassAPI.Modes
public import Silmaril.Wasm.Binaryen.ArbitraryProfile

@[expose] public section

/-! # The arbitrary-profile cleanup through each optimization mode

This is the existing four-pass implementation with unchanged execution. Its
exact-equivalence proof supplies every weaker mode's obligations. The API permits
future passes proved only at a weaker mode without mislabeling them as exact.
No executable flag or mode-specific extra stage is enabled by this module.
-/

namespace Silmaril.Wasm.Binaryen.Modes

open Execution.Core Numerics Optimization

variable {H : Type}

def cleanupP (mode : Mode) (P : Profile) :
    Silmaril.Compile.PassAPI.Pass (contract mode P (closedHost (H := H))) :=
  let exactPass := Silmaril.Compile.PassAPI.Pass.weaken (old_equivalence_le P closedHost)
    (ArbitraryProfile.cleanupP (H := H) P)
  match mode with
  | .equivalence => exactPass
  | .refinement =>
      Silmaril.Compile.PassAPI.Pass.weaken (equivalence_le_refinement P closedHost) exactPass
  | .trapInsertion =>
      Silmaril.Compile.PassAPI.Pass.weaken (refinement_le_trapInsertion P closedHost)
        (Silmaril.Compile.PassAPI.Pass.weaken (equivalence_le_refinement P closedHost) exactPass)

@[simp] theorem cleanupP_run (mode : Mode) (P : Profile) :
    (cleanupP (H := H) mode P).run = ArbitraryProfile.cleanup := by
  cases mode <;> rfl

theorem cleanup_sound (mode : Mode) (P : Profile) {m : BModule} (valid : m.Ok) :
    (ArbitraryProfile.cleanup m).Ok ∧
      ExportCorrect mode P (closedHost (H := H)) m.lower (ArbitraryProfile.cleanup m).lower := by
  have result : ((cleanupP (H := H) mode P).run m).Ok ∧
      ExportCorrect mode P (closedHost (H := H)) m.lower ((cleanupP (H := H) mode P).run m).lower :=
    ⟨(cleanupP (H := H) mode P).inv_run valid, (cleanupP (H := H) mode P).sound valid⟩
  simpa only [cleanupP_run] using result

end Silmaril.Wasm.Binaryen.Modes
