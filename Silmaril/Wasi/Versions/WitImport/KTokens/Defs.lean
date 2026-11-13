module

public import Silmaril.Wasi.Versions.WitImport.KSplit.Defs
public import Silmaril.Wasi.Versions.WitImport.KNoDoc.Defs

@[expose] public section

/-!
# The kernel importer on tokens without doc comments

`parseTokK full` lexes the glued text `full` (with its doc comments, as `wit_src%` gives it)
with the fuelled lexer and parses its tokens without the doc-comment tokens (`notDoc`).
`importTokK`, `kTableTok`, `kDropsTok` and `kRPkgTok` are `importKD`, `kTable`, `kDrops` and
`kRPkg` (`Silmaril.Wasi.Versions.WitImport.KSplit`, `KImport`) with `parseTokK` in place of
`parseCharsK`. `Silmaril.Wasi.Versions.WitImport.KTokens.Thms` relates them.

The theorems on tokens built on these (`<x>_kernel_tokens`, `KCert/Tokens/*`) are the earlier
variant of the `<x>_kernel` theorems of `KCert/Docs/*`, which parse every token, doc comments
included: `Silmaril.Wasi.Versions.WitImport.KErase` proves that doc comments cannot change a table,
a drop list or a resolved package, so no assumption about dropping doc-comment tokens remains.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasm.Wit

/-- Parse the tokens of a glued text without its doc-comment tokens. -/
def parseTokK (full : List Char) : Option Document :=
  (lexK (full.length + 1) full).bind fun ts => Text.Parse.document (ts.filter notDoc)

/-- `parseStep` with `parseTokK`. -/
def parseTokStep (cs : List Char) : Except String Document :=
  match parseTokK cs with
  | some d => .ok d
  | none => .error "not WIT text this parser accepts"

/-- The kernel importer on the texts' tokens without doc comments. -/
def importTokK (sel : Bool) (fulls : List (List Char)) :
    Except String (Binary.Package × Binary.Env) := do
  let ds ← fulls.mapM parseTokStep
  let U := kUniv sel ds
  let P ← U.head?.elim (.error "no package") pure
  Elab.elaborate U P.name []

/-- The signature table of `importTokK`. -/
def kTableTok (ver sel : Bool) (fulls : List (List Char)) : Option Table :=
  match importTokK sel fulls with
  | .ok (P, _) => some (table ver P)
  | .error _ => none

/-- The resource drops of `importTokK`. -/
def kDropsTok (ver : Bool) (fulls : List (List Char)) : Option (List FnName) :=
  match importTokK false fulls with
  | .ok (P, _) => some (drops ver P)
  | .error _ => none

/-- The resolved package of `importTokK`. -/
def kRPkgTok (ver sel : Bool) (fulls : List (List Char)) : Option RPkg :=
  match importTokK sel fulls with
  | .ok (B, deps) => some (rtable ver B, envOf B deps)
  | .error _ => none

end Silmaril.Wasi.Versions.WitImport
