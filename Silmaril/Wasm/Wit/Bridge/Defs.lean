module

public import Silmaril.Wasm.Wit.Binary.Custom.Defs
public import Silmaril.Wasm.Wit.Project.Defs

/-!
# The binary encoder and the projection: definitions

`encodedItems deps P` are the named items wit-component writes for a package
(`Binary.encodeItems` without the section layout): each interface with its
component type, each world with the wrapper component type
(`Binary.worldWrapper`). `asDefTypes` turns them into the items of
`Project.itemsPackage`, and `wrappedWorld` reads the world back out of a
wrapper. `Silmaril.Wasm.Wit.Bridge.Thms` relates them.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary

/-- The named items of a package's binary, in order. -/
def encodedItems (deps : Env) (P : Package) : Except String (List (String × List ComponentDecl)) := do
  let env := P.env deps
  let ifs ← P.interfaces.mapM (encodeIfaceItem env P.name)
  let ws ← P.worlds.mapM (encodeWorldItem env P.name)
  pure (ifs ++ ws)

/-- Items as the component types `Project.itemsPackage` exports. -/
def asDefTypes (items : List (String × List ComponentDecl)) : List (String × DefType) :=
  items.map fun x => (x.1, .component x.2)

/-- The world a world-wrapper component type defines. -/
def wrappedWorld : DefType → Option Project.WorldType
  | .component [.inst (.type (.component w)), .inst (.export _ (.component 0))] => some w
  | _ => none

end Silmaril.Wasm.Wit.Bridge
