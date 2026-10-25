module

public import Silmaril.Wasm.Binaryen.Toolkit.MetaDCEProjection
public import Silmaril.Wasm.Binaryen.PassAPI.SelectedExports

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit.MetaDCE

open Execution.Core Numerics Validation

variable {H : Type}

theorem pipeline_valid {source : Module} {names : List String}
    (valid : ModuleValid (project names source)) :
    ModuleValid (rume (tree (project names source))).lower := by
  apply rume_valid
  change ModuleValid (tree (project names source)).lower
  rw [tree_lower]
  exact valid

/-- The original source (not just its export projection) is equivalent to the
actual function-removing output on graph-selected invocation scripts. -/
theorem pipeline_correct {source : Module} {names : List String}
    (hsup : supported source = true) (valid : ModuleValid source)
    (projectedValid : ModuleValid (project names source)) (P : Profile) :
    Modes.ExportCorrectOn (· ∈ names) P (closedHost (H := H)) source
      (rume (tree (project names source))).lower := by
  have hproj : Modes.ExportCorrectOn (· ∈ names) P (closedHost (H := H)) source
      (project names source) :=
    ⟨project_admission hsup valid projectedValid,
      fun s imports script hs on => project_observations hsup valid projectedValid s imports hs script on⟩
  have hv : (tree (project names source)).Ok := by rw [BModule.Ok, tree_lower]; exact projectedValid
  have hr := Modes.equivalence_iff.mpr (rume_sound hv P (H := H))
  rw [tree_lower] at hr
  exact hproj.trans (.of_equivalence hr)

/-- A total shared-API pass for a fixed selected export interface. Unsupported
inputs retain identity; the partial CLI continues to reject them explicitly. -/
def equivalenceP (names : List String) (P : Profile) :
    Silmaril.Compile.PassAPI.Pass
      (Modes.moduleContractOn (· ∈ names) P (closedHost (H := H))) where
  run := optimize names
  inv_run {x} valid := by
    unfold optimize
    split
    · cases hv : validate? (project names x) with
      | none => exact valid
      | some mt => exact pipeline_valid ⟨mt, validate?_sound hv⟩
    · exact valid
  sound {x} valid := by
    change Modes.ExportCorrectOn (· ∈ names) P closedHost x (optimize names x)
    unfold optimize
    split
    · rename_i hs
      cases hv : validate? (project names x) with
      | none => exact .refl _ _ _ _
      | some mt => exact pipeline_correct hs valid ⟨mt, validate?_sound hv⟩ P
    · exact .refl _ _ _ _

end Silmaril.Wasm.Binaryen.Toolkit.MetaDCE
