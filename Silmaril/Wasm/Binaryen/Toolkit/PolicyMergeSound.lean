module

public import Silmaril.Wasm.Binaryen.Toolkit.PolicyMerge
public import Silmaril.Wasm.Binaryen.Toolkit.SupportedMergeSound
public import Silmaril.Wasm.Binaryen.Toolkit.BarePreparedMergeSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

open Execution.Core Numerics

theorem mergePolicyBytes_sound {policy : MergeExportNames.Policy}
    {inputs : List (String × ByteArray)} {a : PolicyMergedArtifact}
    (accepted : mergePolicyBytes policy inputs = .ok a) :
    List.Forall₂ (fun input decoded => input.1 = decoded.1 ∧
      Binary.Core.Encodes input.2.data.toList decoded.2) inputs a.inputs ∧
    Validation.ModuleValid a.merged ∧ Binary.Core.Encodes a.bytes.data.toList a.merged := by
  unfold mergePolicyBytes at accepted
  cases supported : mergeSupportedBytes inputs with
  | ok artifact =>
      simp only [supported] at accepted
      cases Except.ok.inj accepted
      exact mergeSupportedBytes_sound supported
  | error error =>
      simp only [supported] at accepted
      split at accepted
      · cases accepted
      · cases aliases : mergeBareAliasBytes policy inputs with
        | error error => simp [aliases] at accepted
        | ok artifact =>
            simp only [aliases] at accepted
            cases Except.ok.inj accepted
            exact mergeBareAliasBytes_sound aliases

/-- A single original-program refinement contract for the actual selected
route. Source namespace/query transport and skip-policy visibility are explicit.
The statement is independent of deterministic numerical-profile choices. -/
theorem mergePolicyBytes_refines_original {H : Type} {policy : MergeExportNames.Policy}
    {inputs : List (String × ByteArray)} {a : PolicyMergedArtifact}
    (accepted : mergePolicyBytes policy inputs = .ok a) (P : Profile)
    {namespaceName query : String} {args : List Val}
    (declared : ∃ p ∈ a.interfaces, p.1 = namespaceName ∧
      ∃ e ∈ p.2.exports, e.name = query)
    (retained : a.retained policy namespaceName query = true) :
    (moduleEntryPoints P (closedHost (H := H)) closedEnv).beh a.merged
        (a.query namespaceName query) args ⊆
      Program.beh P (closedHost (H := H)) a.inputs namespaceName query args := by
  unfold mergePolicyBytes at accepted
  cases supported : mergeSupportedBytes inputs with
  | ok artifact =>
      simp only [supported] at accepted
      cases Except.ok.inj accepted
      exact mergeSupportedBytes_refines_original supported P declared
  | error error =>
      simp only [supported] at accepted
      split at accepted
      · cases accepted
      · cases aliases : mergeBareAliasBytes policy inputs with
        | error error => simp [aliases] at accepted
        | ok artifact =>
            simp only [aliases] at accepted
            cases Except.ok.inj accepted
            have sourceDeclared : ∃ m, (namespaceName, m) ∈ artifact.startless ∧
                query ∈ m.exports.map Export.name := by
              obtain ⟨⟨ns, m⟩, member, name, e, exportMember, exportName⟩ := declared
              cases name
              exact ⟨m, member, List.mem_map.mpr ⟨e, exportMember, exportName⟩⟩
            exact mergeBareAliasBytes_refines_original aliases P sourceDeclared retained

end Silmaril.Wasm.Binaryen.Toolkit
