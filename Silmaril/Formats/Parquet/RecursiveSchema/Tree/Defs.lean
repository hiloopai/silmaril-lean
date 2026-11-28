module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Defs

/-! Checked canonical LIST and Struct trees with signed leaves. Physical
ordinals identify declarations, including the wrappers omitted by Arrow. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Tree

open RecursiveSchema (Location Site Kind)
open Repeated (Absence Boundary Step)

@[expose] public section

inductive Ancestor where
  | struct (site : Site)
  | list (site : Site) (wrapper : Location)
  deriving DecidableEq, Repr

def Ancestor.site : Ancestor → Site
  | .struct site | .list site _ => site

def Ancestor.enter (ctx : Repeated.Context) : Ancestor → Repeated.Context
  | .struct site => ctx.enter site
  | .list site wrapper => ctx.enterList site wrapper

def ancestryContext (ancestors : List Ancestor) : Repeated.Context :=
  ancestors.foldl Ancestor.enter {}

/-- Ordered physical ancestry of one signed leaf. Shared sites use original
SchemaElement ordinals as identities, independent of display names. -/
structure LeafPath where
  site : Site
  kind : Kind
  ancestors : List Ancestor
  deriving DecidableEq, Repr

def LeafPath.steps (path : LeafPath) : List Step :=
  ((ancestryContext path.ancestors).enter path.site).steps

def LeafPath.ancestorSteps (path : LeafPath) (count : Nat) : List Step :=
  (ancestryContext (path.ancestors.take count)).steps

/-- An index is the original definition level that stops at the optional site. -/
def LeafPath.nullable (path : LeafPath) : List (Location × Absence × Nat) :=
  path.steps.zipIdx.filterMap fun
    | (.optional site role, level) => some (site, role, level)
    | (.emptyList .., _) => none

/-- The outermost boundary has repetition level one. Its empty level
comes from the corresponding definition step. -/
def LeafPath.repeated (path : LeafPath) : List Boundary :=
  path.steps.zipIdx.filterMap fun
    | (.emptyList outer wrapper, level) => some ⟨outer, wrapper, level⟩
    | (.optional .., _) => none

def LeafPath.maxDefinition (path : LeafPath) : Nat := path.steps.length
def LeafPath.maxRepetition (path : LeafPath) : Nat := path.repeated.length

structure LeafPlan where
  column : Nat
  path : LeafPath
  deriving DecidableEq, Repr

inductive Declaration where
  | ancestor (value : Ancestor)
  | wrapper (location : Location)
  | signed (site : Site) (kind : Kind)
  deriving DecidableEq, Repr

structure Node where
  declaration : Declaration
  ancestors : List Ancestor
  deriving DecidableEq, Repr

def Node.location (node : Node) : Location :=
  match node.declaration with
  | .ancestor value => value.site.location
  | .wrapper location => location
  | .signed site _ => site.location

def Node.leaf? (node : Node) : Option LeafPath :=
  match node.declaration with
  | .signed site kind => some ⟨site, kind, node.ancestors⟩
  | _ => none

def Node.physical (node : Node) : Option Footer.PhysicalType :=
  node.leaf?.map (·.kind.physical)

def nodes (ancestors : List Ancestor) : Repeated.Field → List Node
  | .group site children =>
    let here := Ancestor.struct site
    ⟨.ancestor here, ancestors⟩ :: children.flatMap (nodes (ancestors ++ [here]))
  | .list site wrapper element =>
    let here := Ancestor.list site wrapper
    let below := ancestors ++ [here]
    ⟨.ancestor here, ancestors⟩ :: ⟨.wrapper wrapper, below⟩ :: nodes below element
  | .leaf leaf => [⟨.signed leaf.site leaf.kind, ancestors⟩]

def columns (original : List Node) : List LeafPlan :=
  (original.filterMap Node.leaf?).zipIdx.map fun (path, column) => ⟨column, path⟩

structure Compiled (limits : Snapshot.Limits) (snapshot : Snapshot.Checked) where
  schema : Repeated.Compiled limits snapshot true
  declarations : List Node
  leaves : Array LeafPlan
  preorder : declarations = schema.fields.flatMap (nodes [])
  ordered : leaves = (columns declarations).toArray

def Compiled.arrow {limits : Snapshot.Limits} {snapshot : Snapshot.Checked} (compiled : Compiled limits snapshot) :
    Arrow.RecursiveSchema.Schema := compiled.schema.arrow

structure Source (limits : Snapshot.Limits) (bytes : Bytes) where
  snapshot : Snapshot.Checked
  schema : Compiled limits snapshot
  original : Snapshot.checkRecursive limits bytes = .ok snapshot

end

public def compile (limits : Snapshot.Limits) (snapshot : Snapshot.Checked) :
    Except Repeated.Error (Compiled limits snapshot) := do
  let schema ← Repeated.compileWith limits snapshot true
  let declarations := schema.fields.flatMap (nodes [])
  return ⟨schema, declarations, (columns declarations).toArray, rfl, rfl⟩

public def openFile (limits : Snapshot.Limits) (bytes : Bytes) : Except Repeated.Error (Source limits bytes) := do
  match original : Snapshot.checkRecursive limits bytes with
  | .error (.original cause) => throw (.original (.snapshot cause))
  | .error (.pageLess cause) => throw (.pageLess cause)
  | .ok snapshot => return ⟨snapshot, ← compile limits snapshot, original⟩

end Silmaril.Formats.Parquet.RecursiveSchema.Tree
