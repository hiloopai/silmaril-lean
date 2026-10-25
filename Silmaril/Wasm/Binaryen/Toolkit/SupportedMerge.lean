module

public import Silmaril.Wasm.Binaryen.Toolkit.SilentStartMerge
public import Silmaril.Wasm.Binaryen.Toolkit.EmptyIdentityMerge

@[expose] public section

/-! Additive checked merge selection. The original endpoint always runs first,
retaining its exact successful artifact. A rejected input may then use the
separately certified finite silent-start preparation. -/

namespace Silmaril.Wasm.Binaryen.Toolkit

inductive SupportedMergedArtifact where
  | original (artifact : MergedArtifact)
  | silent (artifact : SilentStartMergedArtifact)
  | identity (artifact : EmptyIdentityMergedArtifact)

namespace SupportedMergedArtifact

def inputs : SupportedMergedArtifact → List (String × Wasm.Module)
  | .original a => a.inputs
  | .silent a => a.inputs
  | .identity a => a.inputs

/-- Interfaces to which the retained query witness refers. Start erasure
changes no exports or namespace names. -/
def interfaces : SupportedMergedArtifact → List (String × Wasm.Module)
  | .original a => a.inputs
  | .silent a => a.prepared
  | .identity a => [(a.survivor, a.merged)]

def merged : SupportedMergedArtifact → Wasm.Module
  | .original a => a.merged
  | .silent a => a.merged
  | .identity a => a.merged

def bytes : SupportedMergedArtifact → ByteArray
  | .original a => a.bytes
  | .silent a => a.bytes
  | .identity a => a.bytes

end SupportedMergedArtifact

def mergeSupportedBytes (inputs : List (String × ByteArray)) :
    Except String SupportedMergedArtifact :=
  match mergeBytes inputs with
  | .ok a => .ok (.original a)
  | .error _ =>
      match mergeSilentStartBytes inputs with
      | .ok a => .ok (.silent a)
      | .error _ => SupportedMergedArtifact.identity <$> mergeEmptyIdentityBytes inputs

end Silmaril.Wasm.Binaryen.Toolkit
