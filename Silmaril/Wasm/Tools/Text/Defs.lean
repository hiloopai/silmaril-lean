module

public import Silmaril.Wasm.Binaryen.Toolkit.Disassemble
public import Silmaril.Wasm.Binaryen.Toolkit.WatSource
public import Silmaril.Formats.SExp.EncodingWatFullLexer
public import Silmaril.Wasm.Binaryen.Exe.Encode
public import Silmaril.Wasm.Tools.Names.Defs
public import Silmaril.Wasm.Tools.Layout.Defs
public import Silmaril.Wasm.Tools.Print.Defs

/-!
# The cores of `wasm-tools parse` and `wasm-tools print` (core modules)

Pure functions behind the `parse` and `print` subcommands of the Lean `wasm-tools`
(`tools/wasm-tools`, see `tools/wasm-tools/README.md`).

* `watToBinary input`: the bytes `wasm-tools parse` writes for `input`. A binary input
  (`\0asm` header) is checked by silmaril's verified decoder and returned unchanged, as
  upstream does. A text input, annotations removed, is lexed by silmaril's certified WAT
  lexer (`sexpWatFullExec?`), elaborated by its certified source elaborator
  (`parseSupported?`) and encoded by the certified encoder (`Exe.encodeModuleWith?`, with a
  data count section exactly when the code uses a data index, as the `wat` crate does); the
  bytes are then laid out as the `wast` crate does (`Layout.relayout`, checked by the
  certified decoder) with the `name` section and the `(@custom …)` sections. Unlike
  silmaril's `assembleText` it does **not** validate, since `wasm-tools parse` does not.
* `binaryToWatWith cfg input`: the text of the module in wasmprinter's format
  (`Print.printModule`), checked by the certified text elaborator.

The theorems are in `Silmaril.Wasm.Tools.Text.Thms`: whatever either function returns encodes
the same module in silmaril's formal text grammar (`Text.Core.Encodes`, the SpecTec text
grammar, read after removing annotations) and binary grammar (`Binary.Core.Encodes`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Text

open Silmaril Silmaril.Wasm

/-- The Wasm binary magic and version 1 (a core module). -/
def coreHeader : List UInt8 := [0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]

/-- Does the input start with the `\0asm` magic (any version or layer)? This is how
upstream's `wat::parse_bytes` decides binary versus text. -/
def isBinary (b : ByteArray) : Bool :=
  b.size ≥ 4 && b[0]! == 0x00 && b[1]! == 0x61 && b[2]! == 0x73 && b[3]! == 0x6d

/-- The module a text denotes, if the certified pipeline accepts it. The text is read with
its annotations replaced by whitespace (`Annot.stripTrivia`), as the annotations
proposal prescribes. -/
def textTree? (input : String) : Except String (Text.SExp × Wasm.Module) :=
  match Formats.SExpEncoding.Wat.sexpWatFullExec? .core3 (Annot.stripTrivia input) with
  | none => .error "malformed WAT lexical or bracket syntax"
  | some tree =>
    match Binaryen.Toolkit.Wat.parseSupported? tree with
    | none => .error "unsupported WAT syntax (outside silmaril's certified text fragment)"
    | some m => .ok (tree, m)

def textModule? (input : String) : Except String Wasm.Module :=
  (textTree? input).map (·.2)

/-- Is one of the `(@custom …)` sections named `name`? (Then the `wast` crate writes no
`name` section of its own: `!customs.iter().any(|c| c.name() == "name")`.) -/
def hasNameCustom (cs : List Annot.Custom) : Bool := cs.any (·.name == [0x6e, 0x61, 0x6d, 0x65])

/-- The generated `name` section `ns`, unless a custom section is named `name`. -/
def namesFor (cs : List Annot.Custom) (ns : List UInt8) : List UInt8 :=
  if hasNameCustom cs then [] else ns

/-- The binary for a text input, as `wasm-tools parse` writes it: the module in the layout
of the `wast` crate (`Layout.relayout`, checked by the certified decoder; otherwise the
canonical encoding), the `(@custom …)` sections at their places and the `name` section of
the text's identifiers (`Names.ofTree`). -/
def textToBinary (input : String) : Except String ByteArray := do
  let (tree, m) ← textTree? input
  let dc := Binaryen.Exe.usesDataIdx m
  let bytes ← Binaryen.Exe.encodeModuleWith? dc m
  let names ← ((Names.ofTree tree m (input.length + 1)).rename (Annot.nameAnnots input)).section
  let cs := (Annot.customs input).getD []
  -- the `wast` crate writes its `name` section only when no custom section is named `name`
  let names := namesFor cs names
  let vals := Annot.branchHints input
  let branch := if vals.isEmpty then #[] else
    match textTree? (Annot.markerText input) with
    | .ok (_, m') => Layout.hintPositions m' vals
    | .error _ => #[]
  let h := { Layout.hints tree (input.length + 1) with branch }
  pure ⟨(Layout.relayout h cs names dc m bytes).toArray⟩

/-- `wasm-tools parse` without `-t`: binary inputs are decoded (checked) and passed
through; text inputs are assembled. -/
def watToBinary (input : ByteArray) : Except String ByteArray :=
  if isBinary input then
    match Binary.Core.Decode.decodeModule input with
    | .ok _ => .ok input
    | .error e => .error e
  else
    match String.fromUTF8? input with
    | none => .error "input is not valid UTF-8"
    | some s => textToBinary s

/-- `wasm-tools print` with options `cfg`: the text of a binary module in wasmprinter's
format (`Print.printModule`). When the printer's own check does not pass, silmaril-lean's
disassembler output is used instead, if the same check passes for it; otherwise an error.
Either way the text returned passed `Print.check`. -/
def binaryToWatWith (cfg : Print.Config) (input : ByteArray) : Except String String :=
  match Print.printModule cfg input with
  | .error e => .error e.message
  | .ok r =>
    if r.certified then .ok r.text
    else
      match Binaryen.Toolkit.disassembleBytes input with
      | .error e => .error e
      | .ok a =>
        if Print.check r.module a.text then .ok a.text
        else .error "the printed text could not be checked against the module"

/-- `wasm-tools print`: the text of a binary module. -/
def binaryToWat (input : ByteArray) : Except String String := binaryToWatWith {} input

/-- `wasm-tools parse -t`: the printed text of the parsed input. -/
def watToWat (input : ByteArray) : Except String String := do
  binaryToWat (← watToBinary input)

end Silmaril.Wasm.Tools.Text
