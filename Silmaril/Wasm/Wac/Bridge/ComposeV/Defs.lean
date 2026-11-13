module

public import Silmaril.Wasm.Wac.Bridge.Compose.Defs
public import Silmaril.Wasm.Wac.Valid.Defs

/-!
# WAC bridge: `wasm-wac compose` with validation

`composeWatV` is `composeWat` with the validation of `Silmaril.Wasm.Wac.Valid`
(`Valid.elabDocV`): the document's declarations and scopes are checked before
elaboration, the graph's names, results and structural types after it. The definition
tables are the document's (`docNom`) and, for each package, the one `decodePkg` read
from its binary.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm

/-- **`wasm-wac compose`** with validation; `noms` are the packages' definition tables
by package key. -/
def composeWatV (env : PkgEnv) (noms : List (String × NomTable)) (d : Syntax.Document) :
    Except String String := do
  let T : Valid.Tables := { doc := docNom d, pkgs := noms }
  let g ← match Valid.elabDocV T env d with
    | .ok g => .ok g
    | .error (.elab e) => .error s!"elaboration: {reprStr e}"
    | .error (.valid e) => .error s!"validation: {reprStr e}"
  let c ← encode (docNom d ++ noms.flatMap (·.2)) g
  pure (Component.Wat.print c)

end Silmaril.Wasm.Wac.Bridge
