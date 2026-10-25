module

public import Silmaril.Wasm.Binaryen.Toolkit.BarePreparedMerge
public import Silmaril.Wasm.Binaryen.Toolkit.BareAliasMergeSound
public import Silmaril.Wasm.Binaryen.Toolkit.ExperimentalPreparedMergeSound
public import Silmaril.Wasm.Binaryen.Toolkit.SilentStartMergeSound
public import Silmaril.Wasm.Binaryen.MergeExportPublicSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

open Execution.Core Numerics

theorem bareAliasTransportB_closedFacts {aliases : List MergeExportNames.Alias}
    {ns : String} {m : Module} (checked : bareAliasTransportB aliases ns m = true) :
    MergeExportNames.ClosedFacts aliases ns m := by
  obtain ⟨bare, profile, functions, sourceValid, targetValid, injection⟩ :=
    bareAliasTransportB_sound checked
  refine ⟨?_, profile, sourceValid, targetValid, functions, injection⟩
  rcases m with ⟨types, imports, tags, globals, memories, tables, funcs, data, elems, start, exports⟩
  rcases bare with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rfl

theorem mergeBareAliasBytes_conditions {policy : MergeExportNames.Policy}
    {inputs : List (String × ByteArray)} {a : PreparedMergedArtifact}
    (accepted : mergeBareAliasBytes policy inputs = .ok a) :
    policy ≠ .reject ∧ experimentalPreparedMergeBytes policy inputs = .ok a ∧
    (∀ p ∈ a.startless, MergeExportNames.ClosedFacts a.prepared.aliases p.1 p.2) ∧
    bareAliasTransportB [] "" a.linked = true := by
  unfold mergeBareAliasBytes at accepted
  split at accepted
  · cases accepted
  · rename_i policyChecked
    obtain ⟨artifact, broad, accepted⟩ := Exe.bind_ok accepted
    split at accepted
    · rename_i sourceChecked
      split at accepted
      · rename_i targetChecked
        cases Except.ok.inj accepted
        refine ⟨by simpa using policyChecked, broad, ?_, targetChecked⟩
        intro p member
        exact bareAliasTransportB_closedFacts (List.all_eq_true.mp sourceChecked p member)
      · cases accepted
    · cases accepted

/-- Original byte meanings, actual guarded preparation and valid output. -/
theorem mergeBareAliasBytes_sound {policy : MergeExportNames.Policy}
    {inputs : List (String × ByteArray)} {a : PreparedMergedArtifact}
    (accepted : mergeBareAliasBytes policy inputs = .ok a) :
    List.Forall₂ (fun input decoded => input.1 = decoded.1 ∧
      Binary.Core.Encodes input.2.data.toList decoded.2) inputs a.inputs ∧
    Validation.ModuleValid a.merged ∧ Binary.Core.Encodes a.bytes.data.toList a.merged := by
  have broad := (mergeBareAliasBytes_conditions accepted).2.1
  obtain ⟨provenance, _, _, _, _, valid, bytes⟩ := experimentalPreparedMergeBytes_sound broad
  exact ⟨provenance, valid, bytes⟩

/-- Rename/skip-policy outputs are related to the actual original program through
the explicit namespace-qualified alias, after restoring checked silent starts.
No prepared module is silently substituted for an original source. -/
theorem mergeBareAliasBytes_refines_original {H : Type} {policy : MergeExportNames.Policy}
    {inputs : List (String × ByteArray)} {a : PreparedMergedArtifact}
    (accepted : mergeBareAliasBytes policy inputs = .ok a) (P : Profile)
    {namespaceName query : String} {args : List Val}
    (declared : ∃ m, (namespaceName, m) ∈ a.startless ∧ query ∈ m.exports.map Export.name)
    (retained : MergeExportNames.visible policy a.prepared.aliases
      (MergeExportNames.lookup a.prepared.aliases namespaceName query) = true) :
    (moduleEntryPoints P (closedHost (H := H)) closedEnv).beh a.merged
        (MergeExportNames.lookup a.prepared.aliases namespaceName query) args ⊆
      Program.beh P (closedHost (H := H)) a.inputs namespaceName query args := by
  obtain ⟨policyChecked, broad, facts, targetChecked⟩ := mergeBareAliasBytes_conditions accepted
  obtain ⟨_, starts, preparation, linked, output, outputValid, _⟩ :=
    experimentalPreparedMergeBytes_sound broad
  have prepared : a.prepared.modules =
      MergeExportNames.rewriteProgram a.prepared.aliases a.startless := by
    unfold MergeExportNames.prepare? at preparation
    obtain ⟨aliases, found, preparation⟩ := Option.bind_eq_some_iff.mp preparation
    have notReject : (policy == MergeExportNames.Policy.reject) = false := by
      cases policy with
      | reject => exact False.elim (policyChecked rfl)
      | rename => rfl
      | skip => rfl
    simp only [notReject] at preparation
    have record : (⟨aliases, MergeExportNames.rewriteProgram aliases a.startless⟩ :
        MergeExportNames.Prepared) = a.prepared := Option.some.inj preparation
    have aliasEq := congrArg MergeExportNames.Prepared.aliases record
    have modulesEq := congrArg MergeExportNames.Prepared.modules record
    change aliases = a.prepared.aliases at aliasEq
    change MergeExportNames.rewriteProgram aliases a.startless = a.prepared.modules at modulesEq
    rw [aliasEq] at modulesEq
    exact modulesEq.symm
  have aliasBridge := MergeExportNames.checkedMerge_public_refines_original (H := H)
    (args := args) facts (by simpa only [← prepared] using linked)
    (bareAliasTransportB_closedFacts targetChecked) (by simpa only [← output] using outputValid)
    P declared retained
  have provenance := eraseSilentStarts_sound starts
  have profiles : ∀ p ∈ a.startless, Link.GC.inProfile p.2 = true := by
    intro p member
    have bare := (facts p member).bare
    rw [bare]
    rfl
  rw [output]
  exact Set.Subset.trans aliasBridge
    (SilentStartMerge.program_beh_subset (H := H) (P := P) provenance profiles namespaceName query args)

end Silmaril.Wasm.Binaryen.Toolkit
