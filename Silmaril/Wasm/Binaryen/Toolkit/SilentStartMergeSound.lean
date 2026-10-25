module

public import Silmaril.Wasm.Binaryen.Toolkit.SilentStartMerge
public import Silmaril.Wasm.Binaryen.Toolkit.MergeSound
public import Silmaril.Wasm.Binaryen.SilentStartMergeSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

open Execution.Core

theorem eraseSilentStartModule_sound {ns : String} {m erased : Wasm.Module}
    (accepted : eraseSilentStartModule ns m = .ok erased) :
    Link.SilentStart.erase? m = some erased ∧ Validation.ModuleValid m := by
  unfold eraseSilentStartModule at accepted
  split at accepted
  · cases accepted
  · rename_i valid
    split at accepted
    · cases accepted
    · cases accepted
      refine ⟨by assumption, Validation.validate?_isSome_iff.mp ?_⟩
      cases checked : Validation.validate? m with
      | none => simp [checked] at valid
      | some mt => rfl

theorem eraseSilentStarts_sound
    {inputs prepared : List (String × Wasm.Module)}
    (accepted : eraseSilentStarts inputs = .ok prepared) :
    List.Forall₂ (fun p q => p.1 = q.1 ∧ Link.SilentStart.erase? p.2 = some q.2 ∧
      Validation.ModuleValid p.2) inputs prepared := by
  induction inputs generalizing prepared with
  | nil =>
      cases Except.ok.inj accepted
      exact .nil
  | cons p rest ih =>
      obtain ⟨ns, m⟩ := p
      unfold eraseSilentStarts at accepted
      obtain ⟨erased, he, accepted⟩ := Exe.bind_ok accepted
      obtain ⟨tail, tailAccepted, accepted⟩ := Exe.bind_ok accepted
      cases Except.ok.inj accepted
      exact .cons ⟨rfl, eraseSilentStartModule_sound he⟩ (ih tailAccepted)

/-- Original byte meanings and validity, the exact checked erasure relation,
the actual prepared-program merge and valid encoded output. Execution
preservation is connected separately through the silent-start Ready theorem. -/
theorem mergeSilentStartBytes_sound
    {inputs : List (String × ByteArray)} {artifact : SilentStartMergedArtifact}
    (accepted : mergeSilentStartBytes inputs = .ok artifact) :
    List.Forall₂ (fun input decoded => input.1 = decoded.1 ∧
      Binary.Core.Encodes input.2.data.toList decoded.2) inputs artifact.inputs ∧
    List.Forall₂ (fun p q => p.1 = q.1 ∧ Link.SilentStart.erase? p.2 = some q.2 ∧
      Validation.ModuleValid p.2) artifact.inputs artifact.prepared ∧
    checkedMerge? artifact.prepared = some artifact.merged ∧
    Validation.ModuleValid artifact.merged ∧
    Binary.Core.Encodes artifact.bytes.data.toList artifact.merged := by
  unfold mergeSilentStartBytes at accepted
  obtain ⟨modules, decoded, accepted⟩ := Exe.bind_ok accepted
  obtain ⟨prepared, starts, accepted⟩ := Exe.bind_ok accepted
  obtain ⟨merged, linking, accepted⟩ := Exe.bind_ok accepted
  obtain ⟨bytes, encoded, accepted⟩ := Exe.bind_ok accepted
  cases Except.ok.inj accepted
  have linkedEq : checkedMerge? prepared = some merged := by
    unfold mergeModules at linking
    split at linking
    · cases linking
      assumption
    · cases linking
  exact ⟨decodeMergeInputs_sound decoded, eraseSilentStarts_sound starts, linkedEq,
    (checkedMerge?_conditions linkedEq).2.2.2.2.2.2, Exe.encodeModule?_sound encoded⟩

/-- An accepted byte-level silent-start merge refines the actual original
program, with the original decoded modules retained in the artifact. This is
target-to-source inclusion, at every numerical profile, for the closed host. -/
theorem mergeSilentStartBytes_refines_original
    {H : Type} {inputs : List (String × ByteArray)} {artifact : SilentStartMergedArtifact}
    (accepted : mergeSilentStartBytes inputs = .ok artifact) (P : Numerics.Profile)
    {n x : String} {vs : List Val}
    (exported : ∃ p ∈ artifact.prepared, p.1 = n ∧ ∃ e ∈ p.2.exports, e.name = x) :
    (moduleEntryPoints P (SingleThreaded.Det.noHost (H := H)) closedEnv).beh
        artifact.merged x vs ⊆
      Program.beh P (SingleThreaded.Det.noHost (H := H))
        artifact.inputs n x vs := by
  obtain ⟨_, provenance, merged, _, _⟩ := mergeSilentStartBytes_sound accepted
  exact SilentStartMerge.checkedMerge_refines_original provenance merged P exported

end Silmaril.Wasm.Binaryen.Toolkit
