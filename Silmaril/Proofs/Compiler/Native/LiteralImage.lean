module

public import Silmaril.Compiler.Native.Correctness.LiteralImage.Defs
public import Silmaril.Compiler.Native.Correctness.Execution.Thms
public import Silmaril.Compiler.Native.Correctness.LiteralTotal.Defs
public import Silmaril.Compiler.Native.Correctness.Hets.Thms
/-! Actual fetched-byte completion and image-node institutional satisfaction for
one explicit image. All observations are characterized; no source compiler or
external GNU-as correctness follows from this isolated-image result. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.LiteralImage
open Silmaril Silmaril.X86
open Silmaril.Compiler.Native.Correctness.Execution
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
attribute [local cbv_eval] String.toUTF8_eq_toByteArray
attribute [local cbv_eval] Std.ExtDHashMap.Const.get?_insert Std.ExtDHashMap.Const.get?_empty

theorem loaded : Loaded ["a.out"] image := by cbv; decide +kernel
theorem arguments_ok : Silmaril.Compile.Core.Spec.ArgsOk ["a.out"] := by
  unfold Silmaril.Compile.Core.Spec.ArgsOk
  cbv
  decide +kernel

theorem result_eq : result = some 42 := by cbv

private theorem realises_of_result {exit : Word} {initial : NativeState}
    {n status : Nat}
    (checked : ((Features.run Features.FeatureSet.baseline64
      [Features.floatExt, Features.Fpu.ext] exit n initial).bind
        fun mid => returnedExit? (step exit mid)) = some status) :
    ∃ final, Realises exit initial (.returned final) ∧
      observe (.returned final) = .exit status [] := by
  cases executed : Features.run Features.FeatureSet.baseline64
      [Features.floatExt, Features.Fpu.ext] exit n initial with
  | none => simp [executed] at checked
  | some mid =>
    simp only [executed, Option.bind_some] at checked
    cases outcome : step exit mid <;> simp [outcome, returnedExit?] at checked
    case returned final =>
      exact ⟨final, ⟨mid, run_reaches exit n executed, outcome⟩,
        by simpa [observe] using congrArg (fun status => Silmaril.Compile.Core.Spec.Obs.exit status []) checked⟩

theorem actual_bytes_return :
    ∃ final, Realises image.exit image.initial (.returned final) ∧
      observe (.returned final) = .exit 42 [] :=
  realises_of_result result_eq

theorem actual_bytes_all_observations (observation : Observation)
    (realised : Realises image.exit image.initial observation) :
    observe observation = .exit 42 [] := by
  obtain ⟨final, ⟨before, reaches, returned⟩, observed⟩ := actual_bytes_return
  rw [(realises_completed_iff reaches returned observation).mp realised]
  exact observed

/-- The actual image realizes at least one returning observation. -/
theorem nonempty : Set.Nonempty behaviors := by
  obtain ⟨final, realised, observed⟩ := actual_bytes_return
  exact ⟨.returned final, realised⟩

/-- The concrete image's actual behavior model satisfies the existing projected
return42 sentence. This is distinct from a compiled-target toolchain claim. -/
theorem satisfies : behaviors ⊆ LiteralTotal.specification 42 := by
  intro observation realised
  exact actual_bytes_all_observations observation realised

/-- The same isolated image behavior model satisfies that sentence at the
existing Hets nativeMachine node. A toolchain only selects the graph; no loaded
compiled target or source-to-machine correctness is inferred here. -/
theorem satisfies_hets (domain : Source → Prop) (toolchain : Toolchain domain) :
    ((((Hets.graph domain toolchain).inst Hets.Node.nativeMachine).I.obj
      (CategoryTheory.Discrete.mk PUnit.unit))).Sat
        behaviors (LiteralTotal.specification 42) :=
  satisfies

end Silmaril.Compiler.Native.Correctness.LiteralImage
