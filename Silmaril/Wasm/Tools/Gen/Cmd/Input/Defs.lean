module

public import Silmaril.Wasm.Tools.Gen.Cmd.Sections.Defs
public import Silmaril.Wasm.Perf.CoreDecode.Defs
public import Silmaril.Wasm.Binaryen.Toolkit.WatSource
public import Silmaril.Formats.SExp.EncodingWatFullLexer
public import Silmaril.Wasm.Tools.Gen.Cmd.WatLex.Defs
public import Silmaril.Wasm.Tools.Gen.Cmd.WatFast.Defs

/-!
# Reading the input of `mutate` and `shrink`: binary or text

Upstream reads its input with `wat::parse_bytes`: bytes that start with the `\0asm` magic are
a binary module, anything else is WebAssembly text. `readModule` does the same:

* binary: silmaril's decoder (through the fast verified `Silmaril.Wasm.Perf.CoreDecode.decodeF`,
  equal to `Silmaril.Wasm.Binary.Core.decode?`); the custom sections are kept apart
  (`Sections.customsOf`) and put back into the output;
* text: silmaril's certified full WAT lexer in linear time (`WatLex.lexFull?`: silmaril's
  `lexGoFull` with a block-comment fuel fixed once, proved equal to it; Core 3.0 profile) and
  certified source elaborator (`Binaryen.Toolkit.Wat.parseSupported?`, run as its copy
  `WatFast.parseF?`, which checks each function's identifier context in time linear in its
  locals and is proved equal to it, `WatFast.parseF?_eq`). The two narrower
  lexers that `sexpWatFullExec?` tries first are tried only when the full one refuses (that
  the full lexer accepts whatever they accept is not proved; every tree is sound for the same
  grammar). Text inputs carry no custom sections here (`@custom` annotations are not read).

`Thms.readModule_sound`: the module returned is the one the input encodes, in the binary
grammar (`Binary.Core.Encodes`) or the text grammar (`Text.Core.Encodes`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.Input

open Silmaril Silmaril.Wasm

/-- Does the input start with the `\0asm` magic? (`wat::parse_bytes`'s test.) -/
def isBinary (b : ByteArray) : Bool :=
  b.size ≥ 4 && b[0]! == 0x00 && b[1]! == 0x61 && b[2]! == 0x73 && b[3]! == 0x6d

/-- The module a text denotes, if the certified pipeline accepts it. -/
def textModule? (input : String) : Except String Wasm.Module :=
  match WatLex.lexFull? .core3 input <|> Formats.SExpEncoding.Wat.sexpWatFullExec? .core3 input with
  | none => .error "malformed WAT lexical or bracket syntax"
  | some tree =>
    match WatFast.parseF? tree with
    | none => .error "unsupported WAT syntax (outside silmaril's certified text fragment)"
    | some m => .ok m

/-- **The module of an input**, binary or text. -/
def readModule (b : ByteArray) : Except String Wasm.Module :=
  if isBinary b then
    match Silmaril.Wasm.Perf.CoreDecode.decodeF b with
    | some m => .ok m
    | none => .error "malformed binary module"
  else
    match String.fromUTF8? b with
    | none => .error "input is not valid UTF-8"
    | some s => textModule? s

/-- The anchored custom sections of an input (none for text). -/
def customs (b : ByteArray) : List (Nat × Sections.Sec) :=
  if isBinary b then Sections.customsOf b else []

end Silmaril.Wasm.Tools.Gen.Cmd.Input
