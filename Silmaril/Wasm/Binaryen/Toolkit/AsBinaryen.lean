module

public import Silmaril.Wasm.Binaryen.Toolkit.As
public import Silmaril.Wasm.Binaryen.Toolkit.WatBinaryenMacros
public import Silmaril.Formats.SExp.EncodingWatFullLexer

@[expose] public section

/-! Assembly of Core WAT and the separately specified Binaryen source macros.
The Core endpoint and theorem retain their original contracts. The broader
endpoint additionally certifies the original source's macro expansion before
running the same validator and binary encoder. -/

namespace Silmaril.Wasm.Binaryen.Toolkit

/-- A source grammar certificate paired with successful Core validation. -/
structure ValidatedBinaryenSource (tree : Text.SExp) where
  module : Wasm.Module
  source : Text.Extensions.BinaryenMacros.ModuleT tree module
  valid : Validation.ModuleValid module

def validateBinaryenCandidate {tree : Text.SExp}
    (candidate : {m : Wasm.Module // Text.Extensions.BinaryenMacros.ModuleT tree m}) :
    Option (ValidatedBinaryenSource tree) :=
  match checked : Validation.validate? candidate.1 with
  | none => none
  | some mt => some ⟨candidate.1, candidate.2, ⟨mt, Validation.validate?_sound checked⟩⟩

/-- Try exact source expansion before adding implicit reference declarations.
Errors distinguish a missing source derivation from failed Core validation. -/
def checkBinaryenSource (tree : Text.SExp) : Except String (ValidatedBinaryenSource tree) :=
  let ordinary := Wat.BinaryenMacros.parse? tree
  match ordinary.bind validateBinaryenCandidate with
  | some result => .ok result
  | none =>
      let declared := Wat.BinaryenMacros.parseDeclared? tree
      match declared.bind validateBinaryenCandidate with
      | some result => .ok result
      | none =>
          if ordinary.isSome || declared.isSome then
            .error "assembler: module validation failed after Binaryen source elaboration"
          else .error "assembler: unsupported WAT syntax after Binaryen source elaboration"

/-- Preserved optional interface to the source checker. -/
def validateBinaryenSource? (tree : Text.SExp) : Option (ValidatedBinaryenSource tree) :=
  (checkBinaryenSource tree).toOption

/-- Prefer exact Core source assembly, then try the independent source macros.
This endpoint never invokes an external parser or assembler. -/
def assembleBinaryenText (input : String) : Except String AssembledArtifact :=
  match assembleText input with
  | .ok artifact => .ok artifact
  | .error originalError =>
      match Formats.SExpEncoding.Wat.sexpWatFullExec? .core3 input with
      | none => .error originalError
      | some tree =>
          match checkBinaryenSource tree with
          | .error error => .error error
          | .ok parsed => do
              let bytes ← Exe.encodeModule? parsed.module
              pure ⟨parsed.module, ⟨bytes.toArray⟩⟩

end Silmaril.Wasm.Binaryen.Toolkit
