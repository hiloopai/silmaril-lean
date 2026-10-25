module

public import Silmaril.Wasm.Binaryen.Toolkit.AsBinaryen

@[expose] public section

/-! Magic-detected binary or certified original WAT input. File extensions are
irrelevant: Binaryen's `.second` fixtures are original source files too. -/

namespace Silmaril.Wasm.Binaryen.Toolkit

inductive MergeSourceArtifact where
  | binary (bytes : ByteArray)
  | text (source : String) (artifact : AssembledArtifact)

def MergeSourceArtifact.bytes : MergeSourceArtifact → ByteArray
  | .binary bytes => bytes
  | .text _ artifact => artifact.bytes

def prepareMergeSource (bytes : ByteArray) : Except String MergeSourceArtifact := do
  if bytes.data.toList.take 4 == [0, 97, 115, 109] then
    return .binary bytes
  else
    let source ← match String.fromUTF8? bytes with
      | none => .error "merge input is neither a WASM binary nor UTF-8 WAT source"
      | some source => .ok source
    let artifact ← assembleBinaryenText source
    pure (.text source artifact)

def prepareMergeSources : List (String × ByteArray) →
    Except String (List (String × MergeSourceArtifact))
  | [] => .ok []
  | (ns, input) :: rest => do
      let prepared ← (prepareMergeSource input).mapError (ns ++ ": " ++ ·)
      let tail ← prepareMergeSources rest
      pure ((ns, prepared) :: tail)

end Silmaril.Wasm.Binaryen.Toolkit
