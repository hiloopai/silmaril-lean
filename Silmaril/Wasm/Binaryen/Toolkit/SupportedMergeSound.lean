module

public import Silmaril.Wasm.Binaryen.Toolkit.SupportedMerge
public import Silmaril.Wasm.Binaryen.Toolkit.SilentStartMergeSound
public import Silmaril.Wasm.Binaryen.Toolkit.MergeProfileEquivalence
public import Silmaril.Wasm.Binaryen.Toolkit.EmptyIdentityMergeSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

open Execution.Core Numerics

/-- Exact original and emitted binary meanings, and valid emitted module. -/
theorem mergeSupportedBytes_sound {inputs : List (String × ByteArray)}
    {a : SupportedMergedArtifact} (accepted : mergeSupportedBytes inputs = .ok a) :
    List.Forall₂ (fun input decoded => input.1 = decoded.1 ∧
      Binary.Core.Encodes input.2.data.toList decoded.2) inputs a.inputs ∧
    Validation.ModuleValid a.merged ∧ Binary.Core.Encodes a.bytes.data.toList a.merged := by
  unfold mergeSupportedBytes at accepted
  cases original : mergeBytes inputs with
  | ok artifact =>
      simp only [original] at accepted
      cases Except.ok.inj accepted
      obtain ⟨provenance, _, valid, bytes⟩ := mergeBytes_sound original
      exact ⟨provenance, valid, bytes⟩
  | error error =>
      simp only [original] at accepted
      cases silent : mergeSilentStartBytes inputs with
      | error error =>
          simp only [silent] at accepted
          cases identity : mergeEmptyIdentityBytes inputs with
          | error error => simp [identity] at accepted
          | ok artifact =>
              simp only [identity] at accepted
              cases Except.ok.inj accepted
              obtain ⟨provenance, _, _, valid, bytes, _⟩ := mergeEmptyIdentityBytes_sound identity
              exact ⟨provenance, valid, bytes⟩
      | ok artifact =>
          simp only [silent] at accepted
          cases Except.ok.inj accepted
          obtain ⟨provenance, _, _, valid, bytes⟩ := mergeSilentStartBytes_sound silent
          exact ⟨provenance, valid, bytes⟩

/-- Every supported default output refines the actual retained original
program at every numerical profile. Old successful merges retain their exact
artifact and stronger behavior equality theorem. -/
theorem mergeSupportedBytes_refines_original {H : Type}
    {inputs : List (String × ByteArray)} {a : SupportedMergedArtifact}
    (accepted : mergeSupportedBytes inputs = .ok a) (P : Profile)
    {n x : String} {vs : List Val}
    (exported : ∃ p ∈ a.interfaces, p.1 = n ∧ ∃ e ∈ p.2.exports, e.name = x) :
    (moduleEntryPoints P (SingleThreaded.Det.noHost (H := H)) closedEnv).beh
        a.merged x vs ⊆
      Program.beh P (SingleThreaded.Det.noHost (H := H)) a.inputs n x vs := by
  unfold mergeSupportedBytes at accepted
  cases original : mergeBytes inputs with
  | ok artifact =>
      simp only [original] at accepted
      cases Except.ok.inj accepted
      exact (mergeBytes_semantics_profile original P exported).symm.subset
  | error error =>
      simp only [original] at accepted
      cases silent : mergeSilentStartBytes inputs with
      | error error =>
          simp only [silent] at accepted
          cases identity : mergeEmptyIdentityBytes inputs with
          | error error => simp [identity] at accepted
          | ok artifact =>
              simp only [identity] at accepted
              cases Except.ok.inj accepted
              obtain ⟨p, member, name, _⟩ := exported
              have pair : p = (artifact.survivor, artifact.merged) := List.mem_singleton.mp member
              have queryName : artifact.survivor = n := by simpa only [pair] using name
              rw [← queryName]
              exact mergeEmptyIdentityBytes_refines_original identity P _ x vs
      | ok artifact =>
          simp only [silent] at accepted
          cases Except.ok.inj accepted
          exact mergeSilentStartBytes_refines_original silent P exported

end Silmaril.Wasm.Binaryen.Toolkit
