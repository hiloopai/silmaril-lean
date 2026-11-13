module

public import Silmaril.Wasm.Wac.Profile.Defs
public import Silmaril.Wasm.Wac.Graph.Defs
public import Silmaril.Wasm.Component.Binary.Lower.Defs

/-!
# WAC: from the composition profile of component WAT to composition graphs

`Lower.graph S c` reads a component `c` in the composition profile
(`Silmaril.Wasm.Wac.Profile`) as a composition graph (`Silmaril.Wasm.Wac.Graph`), given the
interfaces `S k` of the packages: the components of index `k` of `c` (embedded
`(component …)` definitions and imported components, in index order).

The index spaces of `c` are followed section by section:

* **components**: embedded definitions, imports of components and component aliases
  each take the next index; an index is a package;
* **instances**: an imported instance `"q"` is the location `imp q`; an
  `(instance (instantiate k …))` is the next graph node; an alias of an instance
  export `n` of `i` extends the location of `i` by `n`;
* **functions**: an imported function `"f"` is `imp f`; an alias of a function export
  `f` of an instance is the reference to `f` in the location of the instance;
* **types**: tracked to read the function exports of imported instance types.

Names are function-level and qualified (`i#f`, as `Binary.lower`): an argument
`(with "n" (instance i))` supplies every import `n#f` of the package by the function
`f` of the instance `i`; an export `(export "x" (instance i))` exports every function
`f` of `i` as `x#f`; an import of an instance `"q"` declares the imports `q#f` for the
function exports `f` of its instance type. Types are not converted (imports and
exports carry the types of the packages; declared imports not used by a package carry
the placeholder `anyTy`).

`Lower.toComp P c` composes this with `Graph.toComp`; `Lower.toCompCore c` uses
`Binary.lower` for the embedded packages (core-module components of the
`Binary.lower` subset), so a WAC composition in WAT lowers end to end to the
component IR.

Outside: nested instances of imported instance types (only function exports are
declared); argument and export sorts other than functions and instances (types and
components are skipped, as they have no runtime content in the component IR); value
sorts are rejected.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Lower

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary

/-- A location of an instance. -/
inductive Loc where
  /-- The imported instance `q` (qualified). -/
  | imp (q : String)
  /-- The node `k`, or its nested instance at the qualified path `p`. -/
  | node (k : Nat) (p : Option String)
  deriving Repr, Inhabited, DecidableEq

/-- Qualify a name by a prefix. -/
def qual (p f : String) : String := p ++ "#" ++ f

/-- The function `f` of an instance. -/
def Loc.func : Loc → String → Src
  | .imp q, f => .imp (qual q f)
  | .node k none, f => .out k f
  | .node k (some p), f => .out k (qual p f)

/-- The nested instance `n` of an instance. -/
def Loc.inst : Loc → String → Loc
  | .imp q, n => .imp (qual q n)
  | .node k none, n => .node k (some n)
  | .node k (some p), n => .node k (some (qual p n))

/-- The suffix `f` of `q = n#f`. -/
def suffix? (n q : String) : Option String :=
  if q.startsWith (n ++ "#") then some (String.ofList (q.toList.drop (n.length + 1))) else none

/-- The lowering state. -/
structure St where
  comps : Nat := 0
  types : Array (Option DefType) := #[]
  insts : Array Loc := #[]
  funcs : Array Src := #[]
  imports : Array (String × FuncTy) := #[]
  nodes : Array Inst := #[]
  exports : Array (String × Src) := #[]
  deriving Inhabited

abbrev LM := StateT St (Except String)

def get? {α : Type} (xs : Array α) (i : Nat) (what : String) : LM α :=
  match xs[i]? with
  | some x => pure x
  | none => throw s!"unknown {what} index {i}"

/-- The function exports declared by an instance type. -/
def instTypeFuncs (types : Array (Option DefType)) (t : Nat) : List String :=
  match types[t]? with
  | some (some (.instance ds)) => ds.filterMap fun
      | .export n (.func _) => some n.name
      | _ => none
  | _ => []

/-- The function exports of an instance location, given the package interfaces. -/
def locFuncs (S : Nat → PkgSig) (st : St) : Loc → List String
  | .imp q => (st.imports.toList.map Prod.fst).filterMap (suffix? q)
  | .node k p =>
    match st.nodes[k]? with
    | some n =>
      let fs := (S n.pkg).exports.map Prod.fst
      match p with
      | none => fs
      | some p => fs.filterMap (suffix? p)
    | none => []

/-- The arguments supplied by `(with "n" x)` to a package with interface `s`. -/
def withArg (s : PkgSig) (n : String) (x : SortIdx) : LM (List (String × Src)) := do
  let st ← get
  match x.sort with
  | .func => pure [(n, ← get? st.funcs x.idx "function")]
  | .instance =>
    let l ← get? st.insts x.idx "instance"
    pure ((s.imports.map Prod.fst).filterMap fun q => (suffix? n q).map fun f => (q, l.func f))
  | .type | .component => pure []
  | _ => throw s!"argument {n}: unsupported sort"

/-- One import. -/
def import_ (i : Silmaril.Wasm.Component.Binary.Import) : LM Unit := do
  let n := i.name.name
  match i.desc with
  | .func _ =>
    modify fun st => { st with
      funcs := st.funcs.push (.imp n)
      imports := st.imports.push (n, anyTy) }
  | .instance t =>
    modify fun st => { st with
      insts := st.insts.push (.imp n)
      imports := st.imports ++ ((instTypeFuncs st.types t).map fun f => (qual n f, anyTy)).toArray }
  | .component _ => modify fun st => { st with comps := st.comps + 1 }
  | .type _ => modify fun st => { st with types := st.types.push none }
  | _ => throw s!"import {n}: unsupported sort"

/-- One alias (instance exports only, as in the profile). -/
def alias_ (a : Alias) : LM Unit := do
  match a.target with
  | .export i n =>
    let st ← get
    let l ← get? st.insts i "instance"
    match a.sort with
    | .func => set { st with funcs := st.funcs.push (l.func n) }
    | .instance => set { st with insts := st.insts.push (l.inst n) }
    | .type => set { st with types := st.types.push none }
    | .component => set { st with comps := st.comps + 1 }
    | _ => throw s!"alias {n}: unsupported sort"
  | _ => throw "alias: outside the composition profile"

/-- One instantiation. -/
def instance_ (S : Nat → PkgSig) : InstanceExpr → LM Unit
  | .instantiate c args => do
    let st ← get
    if c < st.comps then
      let as ← args.mapM fun a => withArg (S c) a.1 a.2
      modify fun st => { st with
        insts := st.insts.push (.node st.nodes.size none)
        nodes := st.nodes.push ⟨c, as.flatten⟩ }
    else throw s!"instantiate: unknown component index {c}"
  | .exports _ => throw "instance: outside the composition profile"

/-- One export. -/
def export_ (S : Nat → PkgSig) (e : Binary.Export) : LM Unit := do
  let st ← get
  let x := e.name.name
  match e.item.sort with
  | .func =>
    let s ← get? st.funcs e.item.idx "function"
    set { st with exports := st.exports.push (x, s), funcs := st.funcs.push s }
  | .instance =>
    let l ← get? st.insts e.item.idx "instance"
    let fs := locFuncs S st l
    set { st with
      exports := st.exports ++ (fs.map fun f => (qual x f, l.func f)).toArray
      insts := st.insts.push l }
  | .type => set { st with types := st.types.push none }
  | .component => set { st with comps := st.comps + 1 }
  | _ => throw s!"export {x}: unsupported sort"

/-- One section. -/
def section_ (S : Nat → PkgSig) : Section → LM Unit
  | .custom _ _ => pure ()
  | .types xs => modify fun st => { st with types := st.types ++ (xs.map some).toArray }
  | .imports xs => xs.forM import_
  | .component _ => modify fun st => { st with comps := st.comps + 1 }
  | .instances xs => xs.forM (instance_ S)
  | .aliases xs => xs.forM alias_
  | .exports xs => xs.forM (export_ S)
  | _ => throw "section outside the composition profile"

/-- **The composition graph of a profile component.** -/
def graph (S : Nat → PkgSig) (c : Ast) : Except String Graph := do
  if !isProfile c then throw "not in the composition profile"
  let ((), st) ← (c.sections.forM (section_ S)).run {}
  let g : Graph := ⟨st.imports.toList, st.nodes.toList, st.exports.toList⟩
  let uses := g.nodes.flatMap (Inst.uses S)
  pure { g with imports := g.imports.map fun p => (p.1, (uses.lookup p.1).getD p.2) }

/-- **A profile component as a component of the component IR**, given its packages. -/
def toComp {M : Type} (P : Nat → Comp M) (c : Ast) : Except String (Comp M) :=
  (graph (fun k => sigOf (P k)) c).map (Graph.toComp P)

/-- The embedded package definitions of a component, in component index order (`none`
for an imported or aliased component). -/
def packages (c : Ast) : List (Option Ast) :=
  c.sections.flatMap fun
    | .component d => [some d]
    | .imports xs => (xs.filter fun i => match i.desc with | .component _ => true | _ => false).map
        fun _ => none
    | .aliases xs => (xs.filter fun a => a.sort == .component).map fun _ => none
    | .exports xs => (xs.filter fun e => e.item.sort == .component).map fun _ => none
    | _ => []

/-- **End to end**: a profile component whose packages are embedded and in the
`Binary.lower` subset, as a component of the component IR over `CoreMod`. -/
def toCompCore (c : Ast) : Except String (Comp CoreMod) := do
  let ps ← (packages c).mapM fun
    | some d => lower d
    | none => throw "imported package: its definition is needed (wac --import-dependencies)"
  toComp (fun k => ps.getD k (.mk [] [] [])) c

end Silmaril.Wasm.Wac.Lower
