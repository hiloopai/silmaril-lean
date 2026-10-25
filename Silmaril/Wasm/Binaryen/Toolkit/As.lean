module

public import Silmaril.Wasm.Binaryen.Toolkit.WatSource
public import Silmaril.Formats.SExp.EncodingWatByteLexer
public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Wasm.Binaryen.Exe.Encode

@[expose] public section

/-! # Runtime assembly of certified WAT

The original input passes the formal WAT lexer/bracketer, a source grammar
certificate check, the executable module validator and the certified
binary encoder. Every unsupported syntax or invalid module is rejected.
-/

namespace Silmaril.Wasm.Binaryen.Toolkit

structure AssembledArtifact where
  module : Wasm.Module
  bytes : ByteArray

/-- Assemble checked WAT. Comments and whitespace are handled by the
existing executable WAT lexer; all accepted syntax is checked against the
formal module grammar for the complete original input. -/
def assembleText (input : String) : Except String AssembledArtifact :=
  match Formats.SExpEncoding.Wat.sexpWatByteExec? .core3 input with
  | none => .error "assembler: malformed WAT lexical or bracket syntax"
  | some tree =>
    match Wat.parseSupported? tree with
    | none => .error "assembler: unsupported WAT syntax"
    | some m =>
      match Validation.validate? m with
      | none => .error "assembler: module validation failed"
      | some _ => do
        let bytes ← Exe.encodeModule? m
        pure ⟨m, ⟨bytes.toArray⟩⟩

end Silmaril.Wasm.Binaryen.Toolkit
