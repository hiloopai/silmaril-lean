module

public import Silmaril.Wasm.Wit.Tool.Defs
public import Silmaril.Wasm.Wit.Tool.Source.Defs
public import Silmaril.Wasm.Wit.Binary.Print.Deps.Defs
public import Silmaril.Wasm.Wit.Binary.Encode.Defs
public import Silmaril.Wasm.Wac.TypeOf.Defs
public import Silmaril.Wasm.Wac.Bridge.Encode.Defs

/-!
# `wasm-jco component wit`: the WIT text of a component

`wasm-tools component wit COMP.wasm` prints a WIT package (a type-only component) as it is,
and the world of any other component as the package `root:component` holding `world root`,
followed by the foreign packages its imports and exports name. `componentWit` does the same
from Silmaril's own functions:

* a WIT package is printed by `Wit.Silmaril.Wasm.Wit.Tool.witAll` (silmaril's parser, the WIT decoder,
  `printPackageAll`);
* otherwise the component's type is computed by `Project.projectX` (`Wit.Silmaril.Wasm.Wit.Tool.projectBytesX`),
  wrapped as the world `root:component/root` of a WIT package (`Binary.worldWrapper`,
  `itemSections`), encoded by the component encoder, and that package printed by `witAll`.

The printer is unverified (`printPackageAll` is a transcription of wit-component's printer);
equality with `wasm-tools component wit` is tested (`tools/wasm-jco/tests/wit-cmd.sh`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.WitOf

open Silmaril.Wasm.Component.Binary (ComponentDecl Section)

/-- The package wasm-tools names a component's world after. -/
def rootPkg : Silmaril.Wasm.Wit.Binary.PackageName := ⟨"root", "component", none⟩

/-- The WIT package (as bytes) whose world `root` has the component type `wt`. -/
def worldPackage (wt : List ComponentDecl) : Except String ByteArray :=
  match Silmaril.Wasm.Component.Binary.encode (.mk (Silmaril.Wasm.Wit.Binary.itemSections 0 "root" (Silmaril.Wasm.Wit.Binary.worldWrapper rootPkg "root" wt))) with
  | some b => .ok b
  | none => .error "a number or size exceeds 2^32"

/-- Whether the bytes are a WIT package: a component whose sections are type definitions,
exports of types and custom sections only. -/
def isWitPackage (b : ByteArray) : Bool :=
  match Silmaril.Wasm.Component.Binary.parse b with
  | .ok (.mk ss) => !ss.isEmpty && ss.all fun
      | .types _ => true
      | .exports es => es.all (·.item.sort == .type)
      | .custom .. => true
      | _ => false
  | .error _ => false

/-- Equal nominal definitions. -/
def nomEq : Silmaril.Wasm.Wac.Bridge.Nominal → Silmaril.Wasm.Wac.Bridge.Nominal → Bool
  | .record a, .record b => decide (a = b)
  | .variant a, .variant b => decide (a = b)
  | .enum a, .enum b => decide (a = b)
  | .flags a, .flags b => decide (a = b)
  | _, _ => false

/-- A name the nominal table gives two different definitions (wac's type encoder looks types up
by bare name, so the inferred world would be wrong). -/
def nomClash (t : Silmaril.Wasm.Wac.Bridge.NomTable) : Option String :=
  (t.find? fun (n, d) => t.any fun (m, e) => n == m && !nomEq d e).map (·.1)

/-- The type names an instance kind declares (its type and resource items). -/
def instTypeNames : Silmaril.Wasm.Wac.Kind → List String
  | .inst _ es => es.filterMap fun
      | (n, .type _) | (n, .resource _) => some n
      | _ => none
  | _ => []

/-- A type name declared by two instances (imported or exported). wac's kinds do not record
that one interface's type is another's (`use a.{t}`), so the inferred world would define the
type again: refused. -/
def sharedTypeName (pt : Silmaril.Wasm.Wac.PkgType) : Option String :=
  let all := (pt.imports ++ pt.exports).flatMap (instTypeNames ·.2)
  all.find? fun n => all.count n > 1

/-- An instance imported or exported under a plain name with an interface id (WIT's
`import b: a:b/i`, the `implements` form), which the WIT model here does not represent. -/
def implementsName (pt : Silmaril.Wasm.Wac.PkgType) : Option String :=
  ((pt.imports ++ pt.exports).find? fun
    | (n, .inst (some i) _) => !(n.contains ':') && i != n
    | _ => false).map (·.1)

/-- The component type of a component by wac's inference (`Wac.TypeOf.typeOf`: replays the
sections, so it reads nested shim components and exported inline instances, which the projection
does not), written by wac's type encoder (`Wac.Bridge.importDecls`/`exportDecls`). -/
def inferredDecls (b : ByteArray) : Except String (List ComponentDecl) := do
  let c ← match Silmaril.Wasm.Component.Binary.parse b with
    | .ok c => pure c
    | .error _ => throw "malformed component"
  let (pt, nom) ← Silmaril.Wasm.Wac.TypeOf.typeOf c
  if let some n := sharedTypeName pt then
    throw s!"type `{n}` declared by two interfaces (wac's kinds do not say whether they are one type)"
  if let some n := implementsName pt then
    throw s!"instance `{n}` names an interface of another name (WIT `implements`): not supported"
  if let some n := nomClash nom then
    throw s!"two different types named `{n}` (wac's type encoder looks types up by name)"
  let m : Silmaril.Wasm.Wac.Bridge.TM Unit := do
    Silmaril.Wasm.Wac.Bridge.importDecls pt.imports
    Silmaril.Wasm.Wac.Bridge.exportDecls pt.exports
  match m.run { nom := nom } with
  | .ok ((), s) => pure s.decls
  | .error e => throw e

/-- **`wasm-jco component wit`**: a WIT package's text, else the world of the component as
the package `root:component`: its type by the projection (`Project.projectX`), or, outside the
projection's domain, by inference (`inferredDecls`). -/
def componentWit (b : ByteArray) : Except String String :=
  if isWitPackage b then Silmaril.Wasm.Wit.Tool.witAll b
  else do
    let wt ← match Silmaril.Wasm.Wit.Tool.projectBytesX b with
      | .ok wt => pure wt
      | .error e => match inferredDecls b with
        | .ok wt => pure wt
        | .error e' => throw s!"{e}; by inference: {e'}"
    let pb ← worldPackage wt
    Silmaril.Wasm.Wit.Tool.witAll pb

end Silmaril.Wasm.JcoTool.WitOf
