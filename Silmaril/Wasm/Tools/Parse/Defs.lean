module

public import Silmaril.Wasm.Binaryen.Toolkit.WatSource
public import Silmaril.Formats.SExp.EncodingWatFullLexer
public import Silmaril.Wasm.Binaryen.Exe.Encode

/-!
# `wasm-tools parse`: WAT text to a Core module binary

`parseModule s` turns Core 3.0 WAT text into a module binary in three certified steps:

1. `sexpWatFullExec? .core3`: silmaril-lean's executable WAT lexer and bracketer, sound for
   the lexical grammar `sexpWat3` (`sexpWat_of_fullExec`);
2. `Wat.Source.module?`: silmaril-lean's source-directed, proof-carrying elaborator, whose
   result carries `Text.Core.ModuleT x m` (names, abbreviations, folded instructions and
   implicit types included);
3. `Exe.encodeModule`: silmaril-lean's certified encoder, sound for the binary grammar
   `Binary.Core.Encodes` (`encodeModule_sound`); the data count section is written exactly
   when the code mentions a data index, as the `wat` crate does.

The specification (`Silmaril.Wasm.Tools.Parse.Thms.parseModule_sound`): the text encodes a
module `m` in the Core 3.0 text grammar and the output bytes encode the same `m` in the
binary grammar. Both grammars are functional, so `m` is *the* module of the text.

`wasm-tools parse` also writes a `name` custom section for the identifiers of the text; that
section is not produced here yet (see `tools/wasm-tools/README.md`, Known limitations).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Parse

open Silmaril Silmaril.Wasm

/-- Why `parseModule` failed: lexical/bracket syntax, unsupported or ill-formed module syntax,
or an encoder limit (a vector longer than `2^32`, …). -/
inductive Error where
  | lexical
  | syntax
  | encode (msg : String)
  deriving Repr, BEq, Inhabited

def Error.message : Error → String
  | .lexical => "malformed WAT: lexical or bracket syntax"
  | .syntax => "WAT module syntax not recognised (outside the certified Core 3.0 text elaborator)"
  | .encode msg => s!"cannot encode module: {msg}"

/-- The module of a WAT text, with no certificate in the type (`textModule_sound`). -/
def textModule (s : String) : Except Error Wasm.Module :=
  match Formats.SExpEncoding.Wat.sexpWatFullExec? .core3 s with
  | none => .error .lexical
  | some x =>
    match Binaryen.Toolkit.Wat.Source.module? x with
    | none => .error .syntax
    | some m => .ok m.1

/-- `wasm-tools parse`: WAT text to the binary of its module. -/
def parseModule (s : String) : Except Error ByteArray := do
  let m ← textModule s
  (Binaryen.Exe.encodeModule ByteArray.empty m).mapError .encode

/-- The binary magic and version-1 prefix `\0asm\1\0\0\0`; `wasm-tools parse` passes a binary
input through unchanged. -/
def isBinary (b : ByteArray) : Bool :=
  b.size ≥ 4 && b[0]! == 0 && b[1]! == 0x61 && b[2]! == 0x73 && b[3]! == 0x6d

end Silmaril.Wasm.Tools.Parse
