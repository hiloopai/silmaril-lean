module

public import Silmaril.Wasm.Wac.Text.Parse.Defs
public import Silmaril.Wasm.Wac.Text.Json.Defs

/-!
# The `wasm-wac` tool: pure core

Every command of `tools/wasm-wac/WasmWac.lean` calls one function here on the file
contents; the executable only reads and writes files.

* `parseJson`: WAC text → the JSON of `wac parse` without spans (`toJson`);
* `printText`, `prettyText`: WAC text → the printed document (`print`, `pretty`);
* `check`: parses, prints, re-parses both layouts, and reports whether the round trip
  holds on this input (the theorem `parse_print` proves it for every well-formed
  document).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Tool

open Silmaril.Wasm.Wac.Text

/-- Parse WAC text. -/
def parseDoc (src : String) : Except String Document :=
  match lex src.toList with
  | none => .error "lexical error"
  | some ts => match Parse.document ts with
    | none => .error "syntax error"
    | some d => .ok d

/-- The JSON of a document. -/
def parseJson (src : String) : Except String String := (parseDoc src).map toJson

/-- The printed document (one space between tokens). -/
def printText (src : String) : Except String String := (parseDoc src).map print

/-- The printed document with line breaks. -/
def prettyText (src : String) : Except String String := (parseDoc src).map pretty

/-- What `check` reports. -/
structure Report where
  statements : Nat
  wellFormed : Bool
  printRoundTrip : Bool
  prettyRoundTrip : Bool
  deriving Repr

/-- Parse, print and re-parse. -/
def check (src : String) : Except String Report := do
  let d ← parseDoc src
  -- The round trip is checked through the JSON (the AST has no `DecidableEq`).
  let j := toJson d
  let same (s : String) : Bool := match parseDoc s with
    | .ok d' => toJson d' == j
    | .error _ => false
  pure { statements := d.statements.length, wellFormed := wf d,
         printRoundTrip := same (print d), prettyRoundTrip := same (pretty d) }

end Silmaril.Wasm.Wac.Tool
