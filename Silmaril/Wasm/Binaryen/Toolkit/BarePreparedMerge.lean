module

public import Silmaril.Wasm.Binaryen.Toolkit.ExperimentalPreparedMerge
public import Silmaril.Wasm.Binaryen.Toolkit.BareAliasMerge

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

/-- A narrower checked alias route, retaining the broader experimental
endpoint intact. Its source scope permits actual original-program transport;
the linked-output gate also supports certified public export filtering. -/
def mergeBareAliasBytes (policy : MergeExportNames.Policy)
    (inputs : List (String × ByteArray)) : Except String PreparedMergedArtifact := do
  if policy == .reject then throw "bare alias merge: explicit rename/skip policy required"
  let artifact ← experimentalPreparedMergeBytes policy inputs
  if artifact.startless.all (fun p => bareAliasTransportB artifact.prepared.aliases p.1 p.2) then
    if bareAliasTransportB [] "" artifact.linked then
      pure artifact
    else throw "bare alias merge: linked output is outside checked projection scope"
  else throw "bare alias merge: sources are outside checked alias transport scope"

end Silmaril.Wasm.Binaryen.Toolkit
