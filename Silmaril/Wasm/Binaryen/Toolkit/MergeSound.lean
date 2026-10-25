module

public import Silmaril.Wasm.Binaryen.Toolkit.Merge
public import Silmaril.Wasm.Binaryen.Toolkit.LinkSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

open Execution.Core

theorem decodeMergeInputs_sound {inputs : List (String × ByteArray)}
    {modules : List (String × Wasm.Module)} (h : decodeMergeInputs inputs = .ok modules) :
    List.Forall₂ (fun input decoded => input.1 = decoded.1 ∧
      Binary.Core.Encodes input.2.data.toList decoded.2) inputs modules := by
  induction inputs generalizing modules with
  | nil =>
    cases Except.ok.inj h
    exact .nil
  | cons input rest ih =>
    obtain ⟨name, bytes⟩ := input
    unfold decodeMergeInputs at h
    obtain ⟨m, hm, h⟩ := Exe.bind_ok h
    obtain ⟨modules', hrest, h⟩ := Exe.bind_ok h
    cases Except.ok.inj h
    exact .cons ⟨rfl, decodeInput_sound hm⟩ (ih hrest)

/-- All original input names and byte meanings are retained, the checked merge
actually ran, and the actual output bytes encode its valid resulting module. -/
theorem mergeBytes_sound {inputs : List (String × ByteArray)} {artifact : MergedArtifact}
    (h : mergeBytes inputs = .ok artifact) :
    List.Forall₂ (fun input decoded => input.1 = decoded.1 ∧
      Binary.Core.Encodes input.2.data.toList decoded.2) inputs artifact.inputs ∧
    checkedMerge? artifact.inputs = some artifact.merged ∧
    Validation.ModuleValid artifact.merged ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.merged := by
  unfold mergeBytes at h
  obtain ⟨modules, hm, h⟩ := Exe.bind_ok h
  obtain ⟨merged, hr, h⟩ := Exe.bind_ok h
  obtain ⟨bytes, hb, h⟩ := Exe.bind_ok h
  cases Except.ok.inj h
  have hmerge : checkedMerge? modules = some merged := by
    unfold mergeModules at hr
    split at hr
    · cases hr
      assumption
    · cases hr
  exact ⟨decodeMergeInputs_sound hm, hmerge, (checkedMerge?_conditions hmerge).2.2.2.2.2.2,
    Exe.encodeModule?_sound hb⟩

/-- The scoped N-ary behaviour theorem applies to the retained original modules.
The profile remains deterministic grow-oracle/no-host, exactly as in `merge_sound`. -/
theorem mergeBytes_semantics {H : Type} {inputs : List (String × ByteArray)}
    {artifact : MergedArtifact} (h : mergeBytes inputs = .ok artifact)
    {o : SingleThreaded.GrowOracle} {n x : String} {vs : List Val}
    (hx : ∃ p ∈ artifact.inputs, p.1 = n ∧ ∃ e ∈ p.2.exports, e.name = x) :
    Program.beh (SingleThreaded.profile o)
        (SingleThreaded.Det.noHost (H := H)) artifact.inputs n x vs =
      (moduleEntryPoints (SingleThreaded.profile o)
        (SingleThreaded.Det.noHost (H := H)) closedEnv).beh artifact.merged x vs :=
  checkedMerge?_sound (mergeBytes_sound h).2.1 hx

end Silmaril.Wasm.Binaryen.Toolkit
