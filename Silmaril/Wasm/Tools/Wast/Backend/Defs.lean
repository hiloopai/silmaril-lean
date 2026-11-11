module

public import Silmaril.Wasm.Tools.Wast.Check.Defs
public import Silmaril.Wasm.Tools.Validate.Defs
public import Silmaril.Wasm.Tools.Text.Defs
public import Silmaril.Wasm.Tools.Framing.Defs
public import Silmaril.Wasm.Tools.CompValidate.Defs
public import Silmaril.Wasm.Component.BinaryP3.Check.Defs
public import Silmaril.Wasm.Component.Wat.Defs
public import Silmaril.Wasm.Component.Binary.Encode.Defs
public import Silmaril.Wasm.Tools.Reencode.Defs
public import Silmaril.Wasm.Wac.WatX.Defs
public import Silmaril.Wasm.Tools.WastEnc.Defs
public import Silmaril.Wasm.Tools.Wast.Encode.Defs
public import Silmaril.Wasm.Tools.Wast.Diag.Defs
public import Silmaril.Wasm.Tools.Wast.CompText.Defs

/-!
# The `wast` backend: decoder, validator and round trip under a feature set

`fullBackend F` is the `Backend` (`Silmaril.Wasm.Tools.Wast.Check`) that `wasm-tools wast` runs
with `--features` read as the wasmparser feature set `F` (`Silmaril.Wasm.Tools.Features`):

* **encoder**: `parseEncoder`: the transcription of the `wast` crate's encoder
  (`WastEnc.encodeModuleSrc`), kept only when `checkedCore` accepts it (`checkedCore_sound`),
  as `json-from-wast` uses it; otherwise silmaril-lean's certified elaborator and canonical
  encoder. The re-encoding below keeps the layout choices (`Reencode.reencode`), so
  `binary_compare` holds on the `parse` layout;
* **core modules**: `decode` is `parse_binary_wasm` with features (the decoder
  `Validate.decodeW F`; the encoding gates `Validate.binGates F` belong to validation, as in
  wasmparser); `validate` is
  `Validate.check F`, the `validate` subcommand's core, proved equal to the specification
  (`Validate.check_ok_iff`);
* **components**: `decode` is the component binary grammar at component-model `d095e2f`
  (`BinaryP3.parse`), the checks that grammar leaves to the reader (`BinaryP3.Check.strict`:
  outer alias sorts, attribute uniqueness) and the core decoder on every embedded core module;
  `validate` is the `validate` subcommand's component validator `CompValidate.check F`
  (proved for the embedded core modules, `check_core`; the component rules are a tested
  transcription of wasmparser's, with known gaps);
* **round trip** (`test_wasm_roundtrip`): core modules print with the `print` subcommand's
  printer (`Text.binaryToWat`, wasmprinter's format; `-f` for the folded print) and parse back
  with the `parse` subcommand's `Text.textToBinary`; re-encoding is `Reencode.reencode`
  (`RoundtripReencoder`: the element, table, `rec` and `else` forms of the input kept, its
  custom sections copied; proved to encode the same module, `Reencode.reencode_sound`).
  Components print with the component printer `Component.Wat.print` and read back with `Component.Wat.read` (round trip
  `Component.Wat.read_print`, up to `Wat.norm`), encoded by `Component.Binary.encode`;
  they re-encode through `BinaryP3.parse` and `BinaryP3.encode`; they have no folding printer.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast

open Silmaril Silmaril.Wasm
open Silmaril.Wasm.Tools.Features (WFeatures)

/-! ## Core modules -/

/-- The byte at the position a decoder message names (`… (at byte N)`), in hexadecimal. -/
def byteAtMsg (b : ByteArray) (msg : String) : String :=
  match (msg.splitOn "(at byte ").getLast? with
  | some rest =>
    match (rest.takeWhile Char.isDigit).toString.toNat? with
    | some n => "0x" ++ String.ofList (Nat.toDigits 16 (b.get! n).toNat)
    | none => "0x0"
  | none => "0x0"

/-- wasmparser's wording for a message of silmaril-lean's decoder, by class (the decoder does
not say whether an integer is 32- or 64-bit; the 32-bit wording is used). Other messages are
kept. -/
def wpDecodeMessage (b : ByteArray) (msg : String) : String :=
  let has (t : String) := (msg.splitOn t).length > 1
  if has "signed LEB128 out of range" then "invalid var_i32: integer too large"
  else if has "LEB128 out of range" then "invalid var_u32: integer too large"
  else if has "LEB128 too long" then "invalid var_u32: integer representation too long"
  else if has "bad global mutability" then "malformed global flags"
  else if has "memarg flags" && has "out of range" then "malformed memop alignment: alignment too large"
  else if has "bad composite type" then s!"invalid leading byte ({byteAtMsg b msg}) for type"
  else if has "out of order or repeated" then "section out of order"
  else msg

/-- `parse_binary_wasm` on a core module: wasmparser's parser does not apply the feature gates
of `Validate.binGates` (the validator does: `data count section requires the bulk-memory
proposal` is a validation error), so this is the decoder `Validate.decodeW F` alone. -/
def decodeCoreF (F : WFeatures) (b : ByteArray) : Except String Unit :=
  match Validate.decodeW F b with
  | .ok _ => .ok ()
  | .error e => .error (wpDecodeMessage b e)

/-- `wasm_tools::validate` on a core module: the `validate` subcommand's certified verdict
(`Validate.check F`); for an invalid module the message is the diagnosis of the failing step
(`Diag.diagnose`, wasmparser's wording), since `assert_invalid` compares messages. -/
def validateCoreF (F : WFeatures) (b : ByteArray) : Except String Unit :=
  match Validate.check F b with
  | .ok () => .ok ()
  | .error .invalid =>
    match Validate.decodeW F b with
    | .ok m => .error (Diag.diagnose m)
    | .error _ => .error Validate.Error.invalid.message
  | .error (.malformed e) => .error (wpDecodeMessage b e)
  | .error e => .error e.message

/-! ## Components -/

/-- The embedded core modules of a component, after the structural checks. -/
def componentCores (b : ByteArray) : Except String (List ByteArray) := do
  let c ← (Silmaril.Wasm.Component.BinaryP3.parse b).mapError fun e =>
    s!"failed to parse WebAssembly component: {Silmaril.Wasm.Component.BinaryP3.Check.errStr e}"
  let (oa, att, ms) := Silmaril.Wasm.Component.BinaryP3.Check.strict c
  unless oa do throw "invalid outer alias kind"
  unless att do throw "duplicate attribute in an extern name"
  pure ms

def decodeComponentF (F : WFeatures) (b : ByteArray) : Except String Unit := do
  for m in ← componentCores b do decodeCoreF F m

/-- The `validate` subcommand's component validator (`CompValidate.check`: the proved core
validator on every embedded module, `check_core`, and a tested transcription of wasmparser's
component rules). -/
def validateComponentF (F : WFeatures) (b : ByteArray) : Except String Unit :=
  CompValidate.check F b

/-! ## The `parse` encoder -/

/-- Is `c` a WAT whitespace character? -/
def isBlankChar (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- `(module definition …)` (or `(component definition …)`) read as `(module …)`: the keyword
`definition` after the head keyword replaced by spaces of the same length, so that byte
offsets are kept. Texts of any other shape are unchanged. `parse_wast_module` reads the
definition's fields with `parse_without_module_keyword` after `definition`, which is what the
`parse` reader reads in the blanked text. -/
def blankDefinition (src : String) : String :=
  let cs := src.toList
  let ws := cs.takeWhile isBlankChar
  let rest := cs.drop ws.length
  let try1 (kw : String) : Option String :=
    let k := ("(" ++ kw).toList
    if rest.take k.length == k then
      let after := rest.drop k.length
      let gap := after.takeWhile isBlankChar
      let tail := after.drop gap.length
      let d := "definition".toList
      if gap.length > 0 && tail.take d.length == d &&
          (match tail.drop d.length with
           | c :: _ => isBlankChar c || c == '(' || c == ')'
           | [] => true) then
        some (String.ofList (ws ++ k ++ gap ++ List.replicate d.length ' ' ++ tail.drop d.length))
      else none
    else none
  (try1 "module").getD ((try1 "component").getD src)

/-- A component text through the component encoder: `Wac.WatX.parseWatX` (the component
WAT reader with identifiers and the abbreviations of the text format, then
`Component.Binary.encode`), after its core module definitions are encoded by the `wast`
crate transcription (`CompText.inlineCoreModules`). -/
def componentText (src : String) : Except String ByteArray :=
  (Silmaril.Wasm.Wac.WatX.parseWatX (CompText.inlineCoreModules src)).mapError
    fun e => s!"component text: {e}"

/-- The S-expression of a core module text: its `(module …)` form, or the fields of an
anonymous module wrapped in one (as `QuoteWat::encode` reads a quoted module). The text is
read with its annotations blanked (`Annot.stripTrivia`). -/
def coreTree? (s : String) : Option Silmaril.Formats.SExpEncoding.SExp :=
  match Silmaril.Formats.SExpEncoding.Wat.sexpWatFullExec? .core3 (Annot.stripTrivia s) with
  | none => none
  | some tree =>
    match elems? tree with
    | some [x] =>
      match elems? x with
      | some (.atom (.sym "module") :: _) => some x
      | _ => some (lst (sym "module" :: [x]))
    | some xs => some (lst (sym "module" :: xs))
    | none => none

/-- A core text through the `wast` crate's encoder (`WastEnc.encodeModule`). -/
def wastEncText (s : String) : Except String ByteArray :=
  match coreTree? s with
  | some x => WastEnc.encodeModuleSrc x s
  | none => .error "malformed WAT lexical or bracket syntax"

/-- The message of a text that no encoder takes: the `wast` crate transcription's (whose
messages are the crate's), else `e`. -/
def wastMessage (cand : Except String ByteArray) (e : String) : String :=
  match cand with
  | .error m => m
  | .ok _ => e

/-- A text module encoded as the `parse` subcommand encodes it (`Text.textToBinary`: the
`wast` crate's layout, `name` section, `@custom` sections), from the module's source slice
(with `definition` blanked, `blankDefinition`); when that slice is outside what `parse`
reads, the canonical encoder of `encodeText`. Components go through `componentText`. -/
def parseText : ModKind → Silmaril.Formats.SExpEncoding.SExp → String → Except String ByteArray
  | .core, x, src =>
    let cand := WastEnc.encodeModuleSrc x src
    match checkedCore (blankDefinition src) cand with
    | .ok b => .ok b
    | .error e =>
      match encodeText .core x src with
      | .ok b => .ok b
      | .error _ => .error (wastMessage cand e)
  | .component, _, src => componentText (blankDefinition src)

/-- Quoted text through `Text.textToBinary` (a component through `componentText`), else
`encodeQuoted`. -/
def parseQuoted (text : ByteArray) : Except String ByteArray :=
  match String.fromUTF8? text with
  | some s =>
    if s.trimAsciiStart.toString.startsWith "(component" then componentText s
    else
      let cand := wastEncText s
      match checkedCore s cand with
      | .ok b => .ok b
      | .error e =>
        match encodeQuoted text with
        | .ok b => .ok b
        | .error _ => .error (wastMessage cand e)
  | none => encodeQuoted text

/-- The module encoder of the merged `wasm-tools`: the `parse` subcommand's. -/
def parseEncoder : Encoder := ⟨parseText, parseQuoted⟩

/-! ## The round trip -/

/-- The `print` subcommand's printer (`Text.binaryToWatWith`, checked by the certified
elaborator); for a module outside the certified fragment (an unbound type index in an invalid
module, say), the printer's text unchecked (`Print.printModule`), as the round trip only
compares texts and bytes. -/
def printCore (cfg : Print.Config) (b : ByteArray) : Except String String :=
  match Text.binaryToWatWith cfg b with
  | .ok t => .ok t
  | .error e =>
    match Print.printModule cfg b with
    | .ok r => .ok r.text
    | .error _ => .error e

def printAny (b : ByteArray) : Except String String :=
  if isComponent b then
    match Silmaril.Wasm.Component.Binary.parse b with
    | .ok c => .ok (Silmaril.Wasm.Component.Wat.print c)
    | .error _ => .error "this component is outside the component printer's grammar (component-model 8505ba7)"
  else printCore {} b

def parseAny (s : String) : Except String ByteArray :=
  if (s.trimAscii.toString.startsWith "(component") then
    match Silmaril.Wasm.Component.Wat.read s with
    | none => .error "component text not read by the component reader"
    | some c => match Silmaril.Wasm.Component.Binary.encode c with
      | some b => .ok b
      | none => .error "component not encodable"
  else
    checkedCore s (wastEncText s)

/-- `RoundtripReencoder` on a core module, section by section: custom sections (the `name`
section among them) are copied as they are, the other sections are taken from the canonical
re-encoding `canon` of the decoded module. When the two have different non-custom sections,
`canon` itself. -/
def spliceCustoms (orig canon : ByteArray) : ByteArray :=
  let o := orig.toList
  let c := canon.toList
  match Framing.splitSecs (o.drop 8), Framing.splitSecs (c.drop 8) with
  | some os, some cs =>
    let ids (l : List Framing.RawSec) := (l.filter (·.id != 0)).map (·.id)
    if ids os != ids cs then canon
    else
      let cs' := cs.filter (·.id != 0)
      let pick (s : Framing.RawSec) : Framing.RawSec :=
        if s.id == 0 then s else (cs'.find? (·.id == s.id)).getD s
      ⟨(o.take 8 ++ Framing.join (os.map pick)).toArray⟩
  | _, _ => canon

def reencodeAny (b : ByteArray) : Except String ByteArray :=
  if isComponent b then
    match Silmaril.Wasm.Component.BinaryP3.parse b with
    | .error e => .error (Silmaril.Wasm.Component.BinaryP3.Check.errStr e)
    | .ok c => match Silmaril.Wasm.Component.BinaryP3.encode c with
      | some b' => .ok b'
      | none => .error "component not encodable"
  else Reencode.reencode b

/-- The folding printer (`print -f`) on core modules; components have none. -/
def printFoldedAny (b : ByteArray) : Except String String :=
  if isComponent b then
    .error "printing with folded instructions (`fold_instructions`) is not implemented for components"
  else printCore { fold := true } b

def roundtripTools : Roundtrip :=
  { print := printAny, printFolded := some printFoldedAny, parse := parseAny,
    reencode := reencodeAny }

/-! ## The backend -/

/-- The backend of `wasm-tools wast --features F`. -/
def fullBackend (F : WFeatures) : Backend where
  enc := parseEncoder
  decode b := if isComponent b then decodeComponentF F b else decodeCoreF F b
  validate b := if isComponent b then validateComponentF F b else validateCoreF F b
  roundtrip := some roundtripTools

end Silmaril.Wasm.Tools.Wast
