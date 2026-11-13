module

public import Silmaril.Wasm.Binaryen.Toolkit.Disassemble
public import Silmaril.Wasm.Binaryen.Toolkit.WatSource
public import Silmaril.Formats.SExp.EncodingWatFullLexer
public import Silmaril.Wasm.Binaryen.Exe.Encode
public import Silmaril.Wasm.Perf.WatReadB.Defs
public import Silmaril.Wasm.Perf.WatPrint.Defs
public import Silmaril.Wasm.Tools.Component.Wat.Defs

/-!
# Text inputs and `-t` outputs of the `component` subcommands

Upstream reads every Wasm input with `wat::Parser::parse_bytes` (binary when the input starts
with `\0asm`, else the text format, a core module or a component) and prints `-t` outputs with
`wasmprinter`. Here:

* `toBinary`: a binary input unchanged; core-module text through silmaril's certified WAT
  lexer, elaborator and encoder (as the core `parse` subcommand); component text through the
  verified component WAT reader (`Perf.WatReadB.parseWatB = Wit.Tool.parseWat`).
* `printWat`: a component through the verified component printer (`Perf.WatPrint.printWatF`),
  a core module through silmaril's canonical printer (`disassembleBytes`). Neither is
  `wasmprinter`'s text: `-t` output is documented as differing (docs/projects/wasm-components.md).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Text

open Silmaril Silmaril.Wasm

def hasMagic (b : ByteArray) : Bool :=
  b.size ≥ 4 && b[0]! == 0x00 && b[1]! == 0x61 && b[2]! == 0x73 && b[3]! == 0x6d

/-- The module a core-module text denotes (silmaril's certified text pipeline). -/
def coreText (input : String) : Except String ByteArray :=
  match Formats.SExpEncoding.Wat.sexpWatFullExec? .core3 input with
  | none => .error "malformed WAT lexical or bracket syntax"
  | some tree =>
    match Binaryen.Toolkit.Wat.parseSupported? tree with
    | none => .error "unsupported WAT syntax (outside silmaril's certified text fragment)"
    | some m => (fun (bs : List UInt8) => (⟨bs.toArray⟩ : ByteArray)) <$> Binaryen.Exe.encodeModule? m

/-- Does the text start (after blanks and `;;` comments) with `(component`? -/
def isComponentText (s : String) : Bool :=
  let ls := (s.splitOn "\n").map (·.trimAsciiStart.toString)
  let ls := ls.filter fun l => !(l.isEmpty || l.startsWith ";;")
  match ls with
  | l :: _ => l.startsWith "(component"
  | [] => false

/-- **`wat::parse_bytes`**: the binary of an input. -/
def toBinary (input : ByteArray) : Except String ByteArray :=
  if hasMagic input then .ok input
  else match String.fromUTF8? input with
    | none => .error "input is not valid UTF-8"
    | some s =>
      if isComponentText s then
        -- the fast reader, else the P3 reader of `component parse` (`Wat.parseText`)
        match Silmaril.Wasm.Perf.WatReadB.parseWatB s with
        | .ok b => .ok b
        | .error e => match Silmaril.Wasm.Tools.Component.Wat.parseText s with
          | .ok b => .ok b
          | .error _ => .error e
      else coreText s

/-- The `-t` text of a binary. -/
def printWat (b : ByteArray) : Except String String :=
  if b.size ≥ 8 && b[6]! == 0x01 then (· ++ "\n") <$> Silmaril.Wasm.Perf.WatPrint.printWatF b
  else (·.text) <$> Binaryen.Toolkit.disassembleBytes b

end Silmaril.Wasm.Tools.Component.Text
