module

public import Silmaril.Wasm.Binaryen.Toolkit.SupportedMerge
public import Silmaril.Wasm.Binaryen.Toolkit.BarePreparedMerge

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

inductive PolicyMergedArtifact where
  | supported (artifact : SupportedMergedArtifact)
  | aliases (artifact : PreparedMergedArtifact)

namespace PolicyMergedArtifact

def inputs : PolicyMergedArtifact → List (String × Module)
  | .supported a => a.inputs
  | .aliases a => a.inputs

def interfaces : PolicyMergedArtifact → List (String × Module)
  | .supported a => a.interfaces
  | .aliases a => a.startless

def merged : PolicyMergedArtifact → Module
  | .supported a => a.merged
  | .aliases a => a.merged

def bytes : PolicyMergedArtifact → ByteArray
  | .supported a => a.bytes
  | .aliases a => a.bytes

/-- Explicit transport of a source namespace and exported query. -/
def query : PolicyMergedArtifact → String → String → String
  | .supported _, _, name => name
  | .aliases a, ns, name => MergeExportNames.lookup a.prepared.aliases ns name

/-- Skip policy retains a subset of the original public observations. Internal
wiring is resolved before this public-interface restriction. -/
def retained (policy : MergeExportNames.Policy) : PolicyMergedArtifact → String → String → Bool
  | .supported _, _, _ => true
  | .aliases a, ns, name => MergeExportNames.visible policy a.prepared.aliases
      (MergeExportNames.lookup a.prepared.aliases ns name)

end PolicyMergedArtifact

/-- Preserve every existing successful route and artifact, then attempt the
explicitly requested conflict policy in the checked alias transport scope. -/
def mergePolicyBytes (policy : MergeExportNames.Policy) (inputs : List (String × ByteArray)) :
    Except String PolicyMergedArtifact :=
  match mergeSupportedBytes inputs with
  | .ok a => .ok (.supported a)
  | .error originalError =>
      if policy == .reject then .error originalError
      else PolicyMergedArtifact.aliases <$> mergeBareAliasBytes policy inputs

end Silmaril.Wasm.Binaryen.Toolkit
