module

public import Silmaril.Wasm.Component.Codec.Defs
public import Silmaril.Wasm.Tools.Component.Validate.Defs
public import Silmaril.Wasm.Tools.Component.Features.Defs
public import Silmaril.Wasm.Tools.Component.Wat.Defs
public import Silmaril.Wasm.Tools.Component.Layout.Defs
public import Silmaril.Wasm.Tools.Component.FastRead.Defs

/-!
# Hand-off of component inputs from the core `validate`, `print` and `parse`

`wasm-tools validate`, `print` and `parse` take core modules and components alike. In the
combined binary the core group (wasm-tools-core) dispatches these subcommands; on a component
input it calls the functions below, which are pure and depend only on the input and on the
raw `--features` arguments (so that the core group does not need this track's feature type):

* `classify b`: `.component` for a component binary (preamble `\0asm 0d 00 01 00`) or for text
  whose first token after `(` is `component`; `.module` for a core binary or other text; the
  core group handles everything that is not `.component`;
* `validate featureArgs b`: `wasm-tools validate [--features A]… ` on a component binary;
  the result is the text after `error: ` (exit 1) or `ok`. A `--features` argument that does
  not parse is the caller's usage error (clap's value parser), reported as `.badFeatures`;
* `print b`: `wasm-tools print` of a component binary (the text in wasmprinter's layout,
  with names and its final newline); `printPlain b`: the same without names;
* `parse t`: `wasm-tools parse` of component text (the binary).

Theorems (`HandOff.Thms`): `validate_sound` (an accepted binary is accepted by the
specification `Validate.Accepts` at the projected flags), `classify_binary` (a component
binary is classified as one), `printPlain_read` (the verified reader reads `printPlain`'s
text back to the normal form of the decoding, from `Layout.read_printW`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.HandOff

/-- The kind of an input, for the dispatch. -/
inductive InputKind where
  | component
  | module
  deriving Repr, DecidableEq

/-- Skip white space and comments (`;;` to the end of the line, nested `(; … ;)`), with fuel
(each step consumes at least one character, so the length suffices). -/
def skipWs : Nat → List Char → List Char
  | 0, cs => cs
  | n + 1, cs =>
    match cs with
    | c :: rest =>
      if c == ' ' || c == '\t' || c == '\n' || c == '\r' then skipWs n rest
      else match cs with
        | ';' :: ';' :: rest => skipWs n (rest.dropWhile (· != '\n'))
        | '(' :: ';' :: rest => skipWs n (skipBlock n 1 rest)
        | _ => cs
    | [] => []
where
  /-- Inside `depth` nested block comments. -/
  skipBlock : Nat → Nat → List Char → List Char
    | 0, _, cs => cs
    | _, 0, cs => cs
    | n + 1, d + 1, cs =>
      match cs with
      | ';' :: ')' :: rest => skipBlock n d rest
      | '(' :: ';' :: rest => skipBlock n (d + 2) rest
      | _ :: rest => skipBlock n (d + 1) rest
      | [] => []

/-- Is the text a component: `(` then `component` as the first keyword? -/
def isComponentText (t : String) : Bool :=
  let cs := t.toList
  match skipWs (cs.length + 1) cs with
  | '(' :: rest =>
    let rest := skipWs (rest.length + 1) rest
    let kw := rest.takeWhile fun c => c.isAlphanum || c == '_' || c == '.' || c == '-'
    kw == "component".toList
  | _ => false

/-- **The classification** of an input: binary by its preamble, text by its first keyword. -/
def classify (b : ByteArray) : InputKind :=
  match Validate.kindOf b with
  | .component => .component
  | .module => .module
  | .unknown =>
    if b.size ≥ 4 && b[0]! == 0 && b[1]! == 0x61 && b[2]! == 0x73 && b[3]! == 0x6d then .module
    else match String.fromUTF8? b with
      | some t => if isComponentText t then .component else .module
      | none => .module

/-- The result of a hand-off of `validate`. -/
inductive Verdict where
  /-- Valid: exit 0, no output. -/
  | ok
  /-- Invalid: `error: MSG` on stderr, exit 1. -/
  | invalid (msg : String)
  /-- A `--features` value did not parse: clap's usage error (exit 2), with the message of
  the value parser. -/
  | badFeatures (value msg : String)
  deriving Repr, DecidableEq

/-- Parse every `--features` argument (in order) into the feature set, as clap does before
running the command. -/
def features (featureArgs : List String) : Except (String × String) Features.Feat :=
  let rec go : List String → Except (String × String) (List (List Features.Action))
    | [] => .ok []
    | v :: vs => match Features.parseFeatures v with
      | .error e => .error (v, e)
      | .ok a => (go vs).map (a :: ·)
  (go featureArgs).map Features.applyAll

/-- Validation of a component binary under a feature set. -/
def validateFeat (f : Features.Feat) (b : ByteArray) : Verdict :=
  match Features.toCFlags f with
  | none => .invalid "component model feature is not enabled (at offset 0x0)"
  | some F => match Validate.check F b with
    | .ok _ => .ok
    | .error e => .invalid e.message

/-- **`wasm-tools validate [--features A]… B`** on a component binary `B` (text inputs are
converted with `parse` first, as upstream's `InputArg` does). -/
def validate (featureArgs : List String) (b : ByteArray) : Verdict :=
  match features featureArgs with
  | .error (v, e) => .badFeatures v e
  | .ok f =>
    if Validate.kindOf b == .component then validateFeat f b
    else match String.fromUTF8? b with
      | none => .invalid "input file is not valid utf-8"
      | some t => match FastRead.parseTextF t with
        | .error e => .invalid e
        | .ok b' => validateFeat f b'

/-- **`wasm-tools print B`** on a component binary: the text in wasmprinter's layout, with
names, with the final newline (`Layout.printBytesW`). -/
def print (b : ByteArray) : Except String String := Layout.printBytesW b

/-- `print` without names: the verified text (`Layout.read_printW`). -/
def printPlain (b : ByteArray) : Except String String :=
  match Silmaril.Wasm.Component.Codec.decodeLax b with
  | .ok c => .ok (Layout.printW c)
  | .error e => .error s!"failed to parse component: {repr e}"

/-- **`wasm-tools parse T`** on component text: the binary (the tail-recursive reader,
`FastRead.parseTextF_eq`). -/
def parse (t : String) : Except String ByteArray := FastRead.parseTextF t

end Silmaril.Wasm.Tools.Component.HandOff
