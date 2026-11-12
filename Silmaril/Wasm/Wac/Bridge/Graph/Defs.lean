module

public import Silmaril.Wasm.Wac.Bridge.Encode.Defs
public import Silmaril.Wasm.Wac.Lower.Defs

/-!
# WAC bridge: the direct translation of elaborated graphs to composition graphs

`toGraph S g` translates the elaborator's graph `g` (`CGraph`) to the function-level
composition graph of the IR (`Silmaril.Wasm.Wac.Graph`), given the interfaces `S c` of the
packages by component index, without going through WAT. It reads the nodes in the
encoder's order (imports, then the other nodes, then the exports) and gives each node a
meaning (`V`):

* a function import `n` is the reference `imp n` and declares the import `n`; an
  instance import `n` of an instance with functions `f` is the location `imp n` and
  declares the imports `n#f`;
* an instantiation of package `key` is a new graph node `⟨c, args⟩`, where `c` is the
  component index of the package (packages are numbered in order of first
  instantiation, after the components imported before them) and each argument `n` is
  its function, or, for an instance, the functions `n#f` of the package's imports
  `n#f` (wac's argument order, `argOrder`);
* an alias of the export `n` of an instance location `l` is the function `l.func n`
  or the nested location `l.inst n`;
* an export `x` of a function exports it; of an instance at location `l`, exports
  every function `f` of `l` as `x#f`.

This is `Lower.graph` read on the graph instead of on its WAT: the agreement
`Lower.graph S c = .ok (toGraph S g)` for `encode nom g = .ok c` is
`Silmaril.Wasm.Wac.Bridge.Graph.Thms.lower_encode`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary
open Lower (Loc qual suffix?)

/-- The meaning of a node. -/
inductive V where
  | src (s : Src)
  | loc (l : Loc)
  | comp
  | type
  | none
  deriving Inhabited, DecidableEq

/-- The state of the direct translation. -/
structure DS where
  vals : List (Nat × V) := []
  comps : Nat := 0
  pkgs : List (String × Nat) := []
  imports : Array (String × FuncTy) := #[]
  nodes : Array Inst := #[]
  exports : Array (String × Src) := #[]
  deriving Inhabited

/-- The function exports of an instance kind's exports. -/
def funcNames (es : Externs) : List String :=
  es.filterMap fun p => match p.2 with
    | .func _ => some p.1
    | _ => none

/-- Record the meaning of a node. -/
def DS.setVal (ds : DS) (i : Nat) (v : V) : DS := { ds with vals := ds.vals ++ [(i, v)] }

/-- An import node. -/
def dImport (i : Nat) (n : String) (k : Kind) (ds : DS) : DS :=
  match k with
  | .func _ => { ds.setVal i (.src (.imp n)) with imports := ds.imports.push (n, anyTy) }
  | .inst _ es => { ds.setVal i (.loc (.imp n)) with
      imports := ds.imports ++ ((funcNames es).map fun f => (qual n f, anyTy)).toArray }
  | .comp .. => { ds.setVal i .comp with comps := ds.comps + 1 }
  | .type _ | .resource _ => ds.setVal i .type
  | .value _ => ds.setVal i .none

/-- The component index of a package. -/
def dPackage (key : String) (ds : DS) : Nat × DS :=
  match ds.pkgs.lookup key with
  | some c => (c, ds)
  | none => (ds.comps, { ds with comps := ds.comps + 1, pkgs := ds.pkgs ++ [(key, ds.comps)] })

/-- The arguments given by the argument `n` (node `j`) to a package with interface `s`. -/
def dArg (s : PkgSig) (ds : DS) (a : String × Nat) : List (String × Src) :=
  match ds.vals.lookup a.2 with
  | some (.src x) => [(a.1, x)]
  | some (.loc l) => (s.imports.map Prod.fst).filterMap fun q => (suffix? a.1 q).map fun f => (q, l.func f)
  | _ => []

/-- Keep the first argument of each name (as the encoding does, `firstArgs`). -/
def firstNames : List (String × Nat) → List (String × Nat)
  | [] => []
  | a :: as => a :: (firstNames as).filter fun b => b.1 != a.1

/-- The meaning of an alias of the export `n` of the location `l`. -/
def aliasVal (l : Loc) (n : String) : ItemSort → V
  | .func => .src (l.func n)
  | .instance => .loc (l.inst n)
  | .component => .comp
  | .type => .type
  | _ => .none

/-- A non-import node. -/
def dNode (S : Nat → PkgSig) (g : CGraph) (i : Nat) (nd : CNode) (ds : DS) : DS :=
  match nd.op with
  | .defn _ => ds.setVal i .type
  | .inst key _ args =>
    let (c, ds) := dPackage key ds
    let as := (firstNames (argOrder g args)).map (dArg (S c) ds)
    { ds.setVal i (.loc (.node ds.nodes.size none)) with nodes := ds.nodes.push ⟨c, as.flatten⟩ }
  | .alias src n =>
    match ds.vals.lookup src with
    | some (.loc l) =>
      let ds' := ds.setVal i (aliasVal l n (kindSort nd.kind))
      if kindSort nd.kind = .component then { ds' with comps := ds.comps + 1 } else ds'
    | _ => ds
  | .imp _ | .implicit _ => ds

/-- The functions of a location. -/
def dLocFuncs (S : Nat → PkgSig) (ds : DS) : Loc → List String
  | .imp q => (ds.imports.toList.map Prod.fst).filterMap (suffix? q)
  | .node k p =>
    match ds.nodes[k]? with
    | some n =>
      let fs := (S n.pkg).exports.map Prod.fst
      match p with
      | none => fs
      | some p => fs.filterMap (suffix? p)
    | none => []

/-- An export. -/
def dExport (S : Nat → PkgSig) (ds : DS) (n : String) (j : Nat) : DS :=
  match ds.vals.lookup j with
  | some (.src s) => { ds with exports := ds.exports.push (n, s) }
  | some (.loc l) => { ds with exports := ds.exports ++ ((dLocFuncs S ds l).map fun f => (qual n f, l.func f)).toArray }
  | some .comp => { ds with comps := ds.comps + 1 }
  | _ => ds

/-- The import nodes. -/
def dImports : List (Nat × String × Kind) → DS → DS
  | [], ds => ds
  | (i, n, k) :: rest, ds => dImports rest (dImport i n k ds)

/-- The other nodes. -/
def dNodes (S : Nat → PkgSig) (g : CGraph) : List (CNode × Nat) → DS → DS
  | [], ds => ds
  | (nd, i) :: rest, ds => if isImportNode nd then dNodes S g rest ds else dNodes S g rest (dNode S g i nd ds)

/-- The exports. -/
def dExports (S : Nat → PkgSig) (g : CGraph) : List (String × Nat) → DS → DS
  | [], ds => ds
  | (n, j) :: rest, ds => if isDefnNode g j then dExports S g rest ds else dExports S g rest (dExport S ds n j)

/-- The final step of `Lower.graph`: the types of the declared imports are those the
packages expect. -/
def typeImports (S : Nat → PkgSig) (g : Graph) : Graph :=
  let uses := g.nodes.flatMap (Inst.uses S)
  { g with imports := g.imports.map fun p => (p.1, (uses.lookup p.1).getD p.2) }

/-- **The direct translation** of an elaborated graph to a composition graph. -/
def toGraph (S : Nat → PkgSig) (g : CGraph) : Graph :=
  let ds := dExports S g g.exports (dNodes S g g.nodes.zipIdx (dImports (importOrder g) {}))
  typeImports S ⟨ds.imports.toList, ds.nodes.toList, ds.exports.toList⟩

/-- No node has a value kind (values are outside `Lower.graph`). -/
def NoValue (g : CGraph) : Prop := ∀ nd ∈ g.nodes, kindSort nd.kind ≠ .value

end Silmaril.Wasm.Wac.Bridge
