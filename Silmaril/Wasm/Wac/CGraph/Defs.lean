module

public import Silmaril.Wasm.Wac.Types.Defs

/-!
# WAC: the elaboration target (composition graphs) and the package environment

The elaborator of `Silmaril.Wasm.Wac.Elab` turns a WAC document into a *composition
graph*, the structure wac's resolver builds (`wac-graph`'s `CompositionGraph`, wac
`5a7480c`):

* nodes, each with its kind: explicit imports, implicit imports (added by the
  implicit-import pass of `Silmaril.Wasm.Wac.Implicit`), type definitions (exported
  under their name), instantiations of a package with *named* arguments referring
  to nodes, and aliases of an export of an instance node;
* the exports of the composition, naming nodes.

Nodes are referred to by their position. Implicit imports are appended last; the
other nodes only refer to earlier nodes (`CGraph.Ordered`), so a writer emits imports
first and every other node in order.

This is the *local interface* to the IR track: a graph whose instantiations have
every argument explicit is exactly a component in the composition profile of
`Silmaril.Wasm.Wac.Profile` (imports, `instantiate` with named `with` arguments,
`alias export`, exports), once kinds are written as component types.

## Packages

`PkgEnv` is the package registry, keyed by package key (`ns:name` or
`ns:name@version`, wac's `PackageKey`). A package has the component type of what
`new` instantiates (`imports`, `exports`) and the `defs` that package paths look up
(`ns:name/iface` is the definition `iface`; further segments project into exports):
interface definitions are `.type (.inst (some "ns:name/iface") …)`, worlds
`.type (.comp …)`. Decoding packages from binaries is not part of this track; an
`PkgEnv` is an input (in the differential harness, written from `wasm-tools component
wit`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

/-- A package of the registry. -/
structure PkgType where
  imports : Externs := []
  exports : Externs := []
  defs : Externs := []
  deriving Repr, Inhabited

/-- The package registry, by package key. -/
abbrev PkgEnv := List (String × PkgType)

/-- What a node is. -/
inductive COp where
  /-- An explicit import (`import` statement). -/
  | imp (name : String)
  /-- An implicit import (an unsatisfied argument of an instantiation with `...`). -/
  | implicit (name : String)
  /-- A type definition (a type statement), exported under its name. -/
  | defn (name : String)
  /-- An instantiation of the package `pkg`, whose imports are `imports`, with named
  arguments. -/
  | inst (pkg : String) (imports : Externs) (args : List (String × Nat))
  /-- The export `name` of the instance node `src`. -/
  | alias (src : Nat) (name : String)
  deriving Repr, DecidableEq, Inhabited

/-- A node and its kind. -/
structure CNode where
  op : COp
  kind : Kind
  deriving Repr, DecidableEq, Inhabited

/-- A composition graph. -/
structure CGraph where
  nodes : List CNode := []
  exports : List (String × Nat) := []
  deriving Repr, DecidableEq, Inhabited

namespace CGraph

/-- The kind of node `i`. -/
def kindOf (g : CGraph) (i : Nat) : Kind := (g.nodes[i]?.map (·.kind)).getD (.inst none [])

/-- The operation of node `i`. -/
def opOf? (g : CGraph) (i : Nat) : Option COp := g.nodes[i]?.map (·.op)

/-- Add a node; its index is the old length. -/
def add (g : CGraph) (n : CNode) : CGraph × Nat := ({ g with nodes := g.nodes ++ [n] }, g.nodes.length)

/-- The import name of an (explicit or implicit) import node. -/
def importName? (g : CGraph) (i : Nat) : Option String :=
  match g.opOf? i with
  | some (.imp n) | some (.implicit n) => some n
  | _ => none

/-- The export name of an alias node (`get_alias_source`). -/
def aliasName? (g : CGraph) (i : Nat) : Option String :=
  match g.opOf? i with
  | some (.alias _ n) => some n
  | _ => none

/-- The names of the import nodes. -/
def importNames (g : CGraph) : List String :=
  g.nodes.filterMap fun n => match n.op with
    | .imp x | .implicit x => some x
    | _ => none

/-- The imports of the composition, with their kinds. -/
def imports (g : CGraph) : Externs :=
  g.nodes.filterMap fun n => match n.op with
    | .imp x | .implicit x => some (x, n.kind)
    | _ => none

/-- The alias node of export `n` of instance node `src`, if there is one. -/
def findAlias (g : CGraph) (src : Nat) (n : String) : Option Nat :=
  g.nodes.findIdx? fun x => x.op == .alias src n

/-- Whether the composition exports `n`. -/
def hasExport (g : CGraph) (n : String) : Bool := g.exports.any (·.1 == n)

end CGraph

/-- An elaboration state: the graph and the local names (WAC's root scope). -/
structure ESt where
  g : CGraph := {}
  scope : List (String × Nat) := []
  deriving Repr, Inhabited

/-- Elaboration errors, named after wac's `resolution::ElabError` variants. -/
inductive ElabError where
  | undefinedName (name : String)
  | duplicateName (name : String)
  | unknownPackage (name : String)
  | packageMissingExport (pkg item : String)
  | notAnInstance (what : String)
  | missingInstanceExport (name : String)
  | fillArgumentNotLast
  | duplicateInstantiationArg (name : String)
  | spreadInstantiationNoMatch (name : String)
  | missingComponentImport (pkg name : String)
  | mismatchedInstantiationArg (name : String)
  | missingInstantiationArg (pkg name : String)
  | duplicateImport (name : String)
  | duplicateExport (name : String)
  | exportRequiresAs
  | exportConflict (name : String)
  | declarationConflict (name : String)
  | spreadExportNoEffect
  | implicitImportConflict (name : String)
  | importTypeMergeConflict (name : String)
  | notWorld (name : String)
  | importNotInTarget (name : String)
  | targetMismatch (name : String)
  | missingTargetExport (name : String)
  -- WIT declarations in WAC (`Silmaril.Wasm.Wac.WitDecl`)
  | notInterface (name : String)
  | undefinedInterfaceType (name iface : String)
  | notInterfaceValueType (name : String)
  | useConflict (name : String)
  | duplicateInterfaceExport (name : String)
  | duplicateWorldItem (name : String)
  | duplicateWorldIncludeName (name : String)
  | worldIncludeConflict (name : String)
  | missingWorldInclude (name : String)
  -- function type names (`Silmaril.Wasm.Wac.FuncAlias`)
  | notFuncType (name : String)
  | notFuncOrInterface (name : String)
  -- outside the formalized fragment (see `docs/projects/wasm-components.md`)
  | unsupported (what : String)
  deriving Repr, DecidableEq, Inhabited

end Silmaril.Wasm.Wac
