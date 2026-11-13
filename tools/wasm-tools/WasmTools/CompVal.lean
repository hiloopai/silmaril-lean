import Silmaril.Wasm.Tools.Component.Validate.Defs
import Silmaril.Wasm.Tools.Component.Features.Defs
import Silmaril.Wasm.Tools.Component.Wat.Defs
import Silmaril.Wasm.Tools.Component.Layout.Defs
import Silmaril.Wasm.Tools.Component.FastRead.Defs
import Silmaril.Wasm.Tools.Component.HandOff.Defs
import Silmaril.Wasm.Binary.Core.Decode
import Silmaril.Wasm.Validation.Check.Validate
import Silmaril.Cli.Args.Defs

/-!
# The compval track's subcommands: `validate`, `print`, `parse` on components

The subcommand table of the compval track (wasm-tools-comp workflow), for the dispatch of
`tools/wasm-tools/WasmTools.lean`. Each entry runs on the arguments after the subcommand name
and returns the exit status. The wrapper only reads and writes; every decision is a pure
function with its theorems:

| step | function | theorem |
|---|---|---|
| arguments | the specification `Silmaril.Cli.Spec.WasmTools.tool` (`ValidateArgs.ofMatches`, `PrintArgs.ofMatches`) | `Silmaril.Cli.Clap.Main.Thms` |
| `--features` | `Features.parseFeatures`, `applyAll`, `toCFlags` | `Features.toCFlags_default`, `toCFlags_all` |
| component validation | `Validate.check` (the reference, or the extended fold `GcAbi.check?` for 🛸 GC lowerings and value exports) | `Validate.check_sound`, `GcAbi.check?_sound` |
| core module validation | silmaril-lean's `decodeModule` and `validate?` | `validate?_sound` |
| component print | `Layout.printBytesW` (wasmprinter's layout, names) | `Layout.printBytesW_read` (with nothing to name), `Layout.read_printW`, `Layout.renderF_eq` |
| component parse | `FastRead.parseTextF` (one read, `encodeF`) | `FastRead.parseTextF_eq`, `FastRead.encodeF_eq`, `Wat.parse_print_decode` |

The theorems are in the `Thms` modules; this file imports the `Defs` only, so that the binary
does not link the proofs.

Upstream's conventions: a usage error prints clap's message on stderr and exits 2; a failure
prints `error: MESSAGE` on stderr and exits 1; success prints nothing for `validate`.
-/

namespace WasmTools.CompVal

open Silmaril.Wasm.Tools.Component

/-- Print a message on stderr and return a status. -/
def fail (msg : String) (code : UInt32 := 1) : IO UInt32 := do
  let e ← IO.getStderr
  e.putStr msg
  e.flush
  return code

/-- Read the input (`-` or none: stdin), with upstream's error text. -/
def readInput (inp : Option String) : IO (Except String ByteArray) := do
  match inp with
  | none => return .ok (← (← IO.getStdin).readBinToEnd)
  | some path =>
    match ← (IO.FS.readBinFile path).toBaseIO with
    | .ok b => return .ok b
    | .error e =>
      let cause := match e with
        | .noFileOrDirectory .. => "No such file or directory (os error 2)"
        | .permissionDenied .. => "Permission denied (os error 13)"
        | .otherError 21 _ => "Is a directory (os error 21)"
        | e => toString e
      return .error s!"failed to read from `{path}`\n\nCaused by:\n    0: {cause}"

/-- Does the input look like a binary (`\0asm`)? Upstream's `InputArg::get_binary_wasm`
parses anything else as text. -/
def isBinary (b : ByteArray) : Bool := b.size ≥ 4 && b[0]! == 0 && b[1]! == 0x61 && b[2]! == 0x73 && b[3]! == 0x6d

/-- Text input to binary: component WAT through the verified reader; otherwise an error. -/
def textToBinary (b : ByteArray) : Except String ByteArray :=
  match String.fromUTF8? b with
  | none => .error "input file is not valid utf-8"
  | some t => FastRead.parseTextF t

/-- Core modules: silmaril-lean's decoder and validator (the core path belongs to the validate
track; this keeps the standalone driver total). -/
def validateCore (b : ByteArray) : Except String Unit :=
  match Silmaril.Wasm.Binary.Core.Decode.decodeModule b with
  | .error e => .error s!"failed to parse WebAssembly module: {e}"
  | .ok m => match Silmaril.Wasm.Validation.validate? m with
    | none => .error "module failed to validate"
    | some _ => .ok ()

/-- The validation of a binary under the flags, as `wasm-tools validate` does it. -/
def validateBytes (flags : Features.Feat) (b : ByteArray) : Except String Unit :=
  match Validate.kindOf b with
  | .module => validateCore b
  | .component =>
    match Features.toCFlags flags with
    | none => .error "component model feature is not enabled (at offset 0x0)"
    | some F => match Validate.check F b with
      | .ok _ => .ok ()
      | .error e => .error e.message
  | .unknown => .error "unknown binary version and encoding combination (at offset 0x4)"

/-- What `validate` reads from its command line: the input (`none`: stdin, also for `-`) and the
`--features` values, in order. -/
structure ValidateArgs where
  input : Option String := none
  features : List String := []
  deriving Repr, DecidableEq

/-- An input positional as upstream's `InputArg` reads it: `-` is stdin. -/
def inputOf (m : Silmaril.Cli.Matches) : Option String :=
  match m.str? "input" with
  | some "-" => none
  | x => x

/-- **The record of a `validate` run**, from the specification's matches at `["validate"]`. -/
def ValidateArgs.ofMatches (m : Silmaril.Cli.Matches) : ValidateArgs where
  input := inputOf m
  features := m.strs "features"

/-- clap's text for a refused value, without a usage line. -/
def noUsage (msg : String) : String := s!"error: {msg}\n\nFor more information, try '--help'.\n"

/-- The component feature set of the `--features` values (`Features.parseFeatures` of each,
`Features.applyAll`), or clap's message for the first value it refuses. The specification has
checked every value already (`Silmaril.Cli.Spec.WasmTools.reason`), so the error is not expected. -/
def featuresOf (vs : List String) : Except String Features.Feat := do
  let mut acts := []
  for v in vs do
    match Features.parseFeatures v with
    | .ok a => acts := acts ++ [a]
    | .error e => throw (noUsage s!"invalid value '{v}' for '--features <FEATURES>': {e}")
  return Features.applyAll acts

/-- `validate` on the bytes of the input (binary or text). -/
def validateOn (flags : Features.Feat) (b : ByteArray) : IO UInt32 := do
  let b := if isBinary b then .ok b else textToBinary b
  match b >>= validateBytes flags with
  | .ok () => return 0
  | .error e => fail s!"error: {e}\n"

/-- `wasm-tools validate` on its record (components and core modules through this track's
cores, `validateOn`). -/
def validate (a : ValidateArgs) : IO UInt32 := do
  match featuresOf a.features with
  | .error m => fail m 2
  | .ok flags =>
    match ← readInput a.input with
    | .error e => fail s!"error: {e}\n"
    | .ok b => validateOn flags b

/-- Write output: `-o PATH` or stdout. -/
def writeOut (output : Option String) (b : ByteArray) : IO (Except String Unit) := do
  match output with
  | some path =>
    match ← (IO.FS.writeBinFile path b).toBaseIO with
    | .ok () => return .ok ()
    | .error _ => return .error s!"failed to write `{path}`"
  | none =>
    let out ← IO.getStdout
    out.write b; out.flush; return .ok ()

/-- `print` on the bytes of the input (binary or text), writing to `output` (`-o`) or stdout;
the error is the text after `error: ` (exit status 1). -/
def printOn (output : Option String) (b : ByteArray) : IO (Except String Unit) := do
  let b := if isBinary b then .ok b else textToBinary b
  match b >>= Layout.printBytesW with
  | .error e => return .error e
  | .ok t => writeOut output t.toUTF8

/-- `parse` on the bytes of the input (binary or text): the binary, or with `wat` (`-t`) the
text, to `output` (`-o`) or stdout; the error is the text after `error: ` (exit status 1). -/
def parseOn (wat : Bool) (output : Option String) (b : ByteArray) : IO (Except String Unit) := do
  let b := if isBinary b then .ok b else textToBinary b
  let out : Except String ByteArray :=
    if wat then b >>= Layout.printBytesW |>.map String.toUTF8 else b
  match out with
  | .error e => return .error e
  | .ok o =>
    if output.isNone && !wat then
      if ← (← IO.getStdout).isTty then
        return .error "cannot print binary wasm output to a terminal, pass the `-t` flag to print the text format"
    writeOut output o

/-- What `print` and `parse` read from their command lines here: the input (`none`: stdin),
`-o`, and `-t` (`parse` only); the other options do not change the component path's output. -/
structure PrintArgs where
  input : Option String := none
  output : Option String := none
  wat : Bool := false
  deriving Repr, DecidableEq

/-- **The record of a `print` or `parse` run**, from the specification's matches. -/
def PrintArgs.ofMatches (m : Silmaril.Cli.Matches) : PrintArgs where
  input := inputOf m
  output := m.str? "output"
  wat := m.flag "wat"

/-- `wasm-tools print` (components) on its record. -/
def print (a : PrintArgs) : IO UInt32 := do
  match ← readInput a.input with
  | .error e => fail s!"error: {e}\n"
  | .ok b =>
    match ← printOn a.output b with
    | .ok () => return 0
    | .error e => fail s!"error: {e}\n"

/-- `wasm-tools parse` (components) on its record. -/
def parse (a : PrintArgs) : IO UInt32 := do
  match ← readInput a.input with
  | .error e => fail s!"error: {e}\n"
  | .ok b =>
    match ← parseOn a.wat a.output b with
    | .ok () => return 0
    | .error e => fail s!"error: {e}\n"

/-- Does an input go to this track's component path? A component binary (preamble
`\0asm 0d 00 01 00`, `Validate.kindOf`) or component text (`(component` after white space and
comments); every other input, binary or text, is the core group's (`HandOff.classify`,
`HandOff.classify_component`). -/
def isComponentInput (b : ByteArray) : Bool := HandOff.classify b == .component

#guard isComponentInput ⟨#[0x00, 0x61, 0x73, 0x6d, 0x0d, 0x00, 0x01, 0x00]⟩
#guard !isComponentInput ⟨#[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]⟩
-- a component layer with another version is left to the core path (its decoder's error)
#guard !isComponentInput ⟨#[0x00, 0x61, 0x73, 0x6d, 0x0e, 0x00, 0x01, 0x00]⟩
#guard isComponentInput " ;; c\n(; a (; b ;) ;)\n( component $c)".toUTF8
#guard !isComponentInput "(module (func))".toUTF8
#guard !isComponentInput "(func)".toUTF8
#guard !isComponentInput "(componentx)".toUTF8

/-- The subcommands, by their path in the specification, on the specification's matches. -/
def byPath (m : Silmaril.Cli.Matches) : Option (IO UInt32) :=
  match m.path with
  | ["validate"] => some (validate (ValidateArgs.ofMatches m))
  | ["print"] => some (print (PrintArgs.ofMatches m))
  | ["parse"] => some (parse (PrintArgs.ofMatches m))
  | _ => none

end WasmTools.CompVal
