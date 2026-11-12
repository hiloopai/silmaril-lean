module

public import Silmaril.Wasm.Wac.Bridge.Compose.Defs
public import Silmaril.Wasm.Wac.Bridge.TextX.Defs

/-!
# WAC bridge: the pipeline of `wasm-wac compose`, with function type names

As `Silmaril.Wasm.Wac.Bridge.Compose`, through the elaboration AST with function type
names: text → `Text.Document` (`Tool.parseDoc`) → `FuncAlias.Document` (`ofDocX`) →
`CGraph` (`FuncAlias.elabDocA`, given the packages) → component in the composition
profile (`encode`) → WAT. The packages a document needs and the nominal type
definitions are read from its WIT part (`FuncAlias.Document.forget`: function type
items name no package and define no nominal type).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm

/-- Read a document. -/
def readDocX (src : String) : Except String FuncAlias.Document := do
  ofDocX (← Tool.parseDoc src)

/-- The packages a document needs, once each, without its own. -/
def pkgKeysX (d : FuncAlias.Document) : List String := pkgKeys d.forget

/-- Elaborate a document against packages, up to aliases. -/
def elabStrX (env : PkgEnv) (d : FuncAlias.Document) : Except String CGraph :=
  match FuncAlias.elabDocA env d with
  | .ok g => .ok g
  | .error e => .error s!"elaboration: {reprStr e}"

/-- **`wasm-wac compose`**: the WAT of a document's composition. -/
def composeWatX (env : PkgEnv) (nom : NomTable) (d : FuncAlias.Document) : Except String String := do
  let g ← elabStrX env d
  let c ← encode (docNom d.forget ++ nom) g
  pure (Component.Wat.print c)

end Silmaril.Wasm.Wac.Bridge
