module

public import Silmaril.Wasm.Binaryen.Toolkit.MetaDCERuntime

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit.MetaDCE

structure CheckedArtifact extends Artifact where
  transformed : Bool

/-- Compatibility path: valid modules outside the proven optimization fragment
retain their original bytes. The external graph and all export bindings still
have to check. The existing rejecting `eliminateBytes` remains unchanged. -/
def eliminateBytesOrKeep (text : String) (input : ByteArray) : Except String CheckedArtifact := do
  let graph ← parseGraph text
  let live ← match solve graph with
    | some live => pure live
    | none => throw "metadce: graph closure check failed"
  let source ← (Binary.Core.Decode.decodeModule input).mapError ("metadce: " ++ ·)
  match Validation.validate? source with
  | none => throw "metadce: source validation failed"
  | some _ => pure ()
  checkBindings graph source
  if supported source then
    let artifact ← eliminateBytes text input
    pure ⟨artifact, true⟩
  else
    pure ⟨⟨graph, live, source, source, source, input⟩, false⟩

def CheckedArtifact.report (artifact : CheckedArtifact) : String :=
  if artifact.transformed then "metadce: applied checked external-graph and Wasm reachability"
  else "metadce: skipped unsupported module shape; kept original bytes"

end Silmaril.Wasm.Binaryen.Toolkit.MetaDCE
