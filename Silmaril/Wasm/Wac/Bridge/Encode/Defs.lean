module

public import Silmaril.Wasm.Wac.CGraph.Defs
public import Silmaril.Wasm.Wac.Profile.Defs

/-!
# WAC bridge: composition graphs as component WAT in the composition profile

`encode g` writes the composition graph `g` of the elaborator (`CGraph`) as a component
in the composition profile (`Silmaril.Wasm.Wac.Profile`), following wac-graph's
`CompositionGraphEncoder` (wac `5a7480c`, `crates/wac-graph/src/graph.rs`, `encode`)
with `define_components = false` (`wac compose --import-dependencies`):

1. **imports** (`encode_imports`): the implicit imports, then the explicit ones (the
   order of wac's `TypeAggregator`), instances first; each import's kind is written as
   a component type (below) defined just before it;
2. the other nodes in order (`toposort` keeps index order; the elaborator's nodes only
   refer to earlier nodes or to imports):
   * a **type definition** is its type, exported under its last export name
     (`definition`, `defnName`); an interface definition is wrapped in a component type
     exporting it under its id (`ifaceDef`), a world likewise (`worldDef`);
   * an **instantiation** of a package imports the package once, as
     `unlocked-dep=<ns:name>` (`unlocked-dep=<ns:name@{>=v}>` with a version) of the
     component type of the package's imports and exports (`package_import_name`), then
     instantiates it with one `(with "name" (sort i))` per argument (`instantiation`):
     the explicit arguments last to first, then the implicit ones (`argOrder`);
   * an **alias** is `(alias export i "name" (sort))` (`alias`);
3. the **exports** that are not type definitions (`encode`).

The output is a list of `Item`s, one per section; `Item.toSection` is total and lands in
the profile, so `encode_profile` (in `Silmaril.Wasm.Wac.Bridge.Encode.Thms`) needs no
hypothesis. Instantiation arguments keep the first of each name (`firstArgs`).

**Kinds as component types** (wac-types' `TypeEncoder`). In a type scope (`Scope`: the
number of types and the names of the named types), a value type is primitive or the
index of a definition: anonymous types (`list`, `option`, `result`, `tuple`, `own`,
`borrow`, …) are defined in place, a named reference `⟨_, t⟩` is the index the type
`t` was imported or exported at in the scope. A function is a `func` type; an instance
`(instance …)` with one export per item, in order, each typed in the instance's own
scope; a component `(component …)` with its imports, then its exports. A type item
`type k` is `(type (eq i))` for the definition `i` of `k`, a resource `(type (sub
resource))`; both allocate a type index, recorded under the item's name.

Differences from wac: anonymous types are not shared between items (wac shares types by
identity, which kinds do not keep: the WAT differs in type indices and the number of
type definitions, not in the types themselves); `use_aliases` and the shared-instance
deduplication of `import` are not done; record, variant, enum and flags definitions are
not kept in kinds (`witTypeKind` keeps only the name): the encoder takes them from a
table by type name (`NomTable`, filled from the document and the package binaries), so a
name defined differently by two interfaces gets the first definition; type references
across interfaces (wac's `alias outer` to another instance's type) are not expressible
in kinds (named types are local), and are an `.error`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig)

/-! ## Items -/

/-- One item of the encoded component (one section each). -/
inductive Item where
  /-- A type definition. -/
  | type (d : DefType)
  /-- An import. -/
  | imp (name : String) (desc : ExternDesc)
  /-- An instantiation of the component `c`. -/
  | inst (c : Nat) (args : List (String × SortIdx))
  /-- An alias of the export `name` of the instance `i`. -/
  | alias (sort : ItemSort) (i : Nat) (name : String)
  /-- An export. -/
  | exp (name : String) (x : SortIdx)
  deriving Inhabited

/-- Keep the first argument of each name. -/
def firstArgs : List (String × SortIdx) → List (String × SortIdx)
  | [] => []
  | a :: as => a :: (firstArgs as).filter fun b => b.1 != a.1

/-- The section of an item. -/
def Item.toSection : Item → Section
  | .type d => .types [d]
  | .imp n d => .imports [⟨⟨n, .plain0⟩, d⟩]
  | .inst c as => .instances [.instantiate c (firstArgs as)]
  | .alias s i n => .aliases [⟨s, .export i n⟩]
  | .exp n x => .exports [⟨⟨n, .plain0⟩, x, none⟩]

/-! ## Type scopes -/

/-- The definition of a nominal type (record, variant, enum, flags), which kinds do not
keep (`witTypeKind` keeps only the name). -/
inductive Nominal where
  | record (fields : List (String × Silmaril.Wasm.Wit.Binary.Ty))
  | variant (cases : List (String × Option Silmaril.Wasm.Wit.Binary.Ty))
  | enum (labels : List String)
  | flags (labels : List String)
  deriving Inhabited

/-- Nominal definitions by type name (the first of a name is used). -/
abbrev NomTable := List (String × Nominal)

/-- A type scope: the declarations emitted so far, the number of types, the type
names, and the nominal definitions available. -/
structure Scope where
  decls : List ComponentDecl := []
  ntypes : Nat := 0
  names : List (String × Nat) := []
  nom : NomTable := []
  /-- The type indices that are resources. -/
  resIdx : List Nat := []
  /-- Share structurally equal function, instance and component types (in component
  types: see `nested`). -/
  share : Bool := false
  /-- Defined anonymous value types. -/
  vcache : List (DefValType × Nat) := []
  /-- Defined handle types: `own`/`borrow` (`true`/`false`) of a type index. -/
  hcache : List ((Bool × Nat) × Nat) := []
  /-- Defined function types (when sharing). -/
  fcache : List (Sig × Nat) := []
  /-- Defined instance and component types (when sharing). -/
  kcache : List (Kind × Nat) := []
  deriving Inhabited

abbrev TM := StateT Scope (Except String)

/-- Define a type; its index. -/
def defTy (d : DefType) : TM Nat :=
  modifyGet fun s => (s.ntypes, { s with decls := s.decls ++ [.inst (.type d)], ntypes := s.ntypes + 1 })

/-- The index of a named type. -/
def namedTy (n : String) : TM Nat := do
  match (← get).names.lookup n with
  | some i => pure i
  | none => throw s!"type `{n}` is not in scope"

/-- Define an anonymous value type once per scope; its index as a value type
(wit-parser interns anonymous types, so the types of a package binary define each
once). -/
def defVal (d : DefValType) : TM Silmaril.Wasm.Component.Binary.ValType := do
  match (← get).vcache.lookup d with
  | some j => pure (.idx j)
  | none =>
    let j ← defTy (.val d)
    modify fun s => { s with vcache := s.vcache ++ [(d, j)] }
    pure (.idx j)

/-- A handle type `own i` (`o = true`) or `borrow i`, defined once per scope (wac's
value types `Own`/`Borrow` are compared structurally). -/
def handle (o : Bool) (i : Nat) : TM Silmaril.Wasm.Component.Binary.ValType := do
  match (← get).hcache.lookup (o, i) with
  | some j => pure (.idx j)
  | none =>
    let j ← defTy (.val (if o then .own i else .borrow i))
    modify fun s => { s with hcache := s.hcache ++ [((o, i), j)] }
    pure (.idx j)

mutual
/-- A value type. -/
def valTy : Silmaril.Wasm.Wit.Binary.Ty → TM Silmaril.Wasm.Component.Binary.ValType
  | .prim p => pure (.prim p)
  | .ref r => do
    let i ← namedTy r.name
    if i ∈ (← get).resIdx then handle true i else pure (.idx i)
  | .list t => do defVal (.list (← valTy t))
  | .fixedList t n => do defVal (.fixedList (← valTy t) n)
  | .map k v => do let k ← valTy k; defVal (.map k (← valTy v))
  | .option t => do defVal (.option (← valTy t))
  | .result a b => do let a ← valTyOpt a; defVal (.result a (← valTyOpt b))
  | .tuple ts => do defVal (.tuple (← valTys ts))
  | .own r => do handle true (← namedTy r.name)
  | .borrow r => do handle false (← namedTy r.name)
  | .future t => do defVal (.future (← valTyOpt t))
  | .stream t => do defVal (.stream (← valTyOpt t))
/-- An optional value type. -/
def valTyOpt : Option Silmaril.Wasm.Wit.Binary.Ty → TM (Option Silmaril.Wasm.Component.Binary.ValType)
  | none => pure none
  | some t => do pure (some (← valTy t))
/-- Value types. -/
def valTys : List Silmaril.Wasm.Wit.Binary.Ty → TM (List Silmaril.Wasm.Component.Binary.ValType)
  | [] => pure []
  | t :: ts => do let v ← valTy t; pure (v :: (← valTys ts))
end

/-- The definiens of a type alias whose definiens is an anonymous type, defined anew
(`none` for other types). wac gives every type expression of a document its own
identity, and encodes the definiens of an alias declaration afresh (`DefinedType::Alias`
of a defined type), even if an equal anonymous type was defined before. -/
def freshVal : Silmaril.Wasm.Wit.Binary.Ty → TM (Option Nat)
  | .list t => do pure (some (← defTy (.val (.list (← valTy t)))))
  | .fixedList t n => do pure (some (← defTy (.val (.fixedList (← valTy t) n))))
  | .map k v => do let k ← valTy k; pure (some (← defTy (.val (.map k (← valTy v)))))
  | .option t => do pure (some (← defTy (.val (.option (← valTy t)))))
  | .result a b => do let a ← valTyOpt a; pure (some (← defTy (.val (.result a (← valTyOpt b)))))
  | .tuple ts => do pure (some (← defTy (.val (.tuple (← valTys ts)))))
  | .future t => do pure (some (← defTy (.val (.future (← valTyOpt t)))))
  | .stream t => do pure (some (← defTy (.val (.stream (← valTyOpt t)))))
  | _ => pure none

/-- Define a nominal type; its index. -/
def nominalTy : Nominal → TM Nat
  | .record fs => do
    let fs ← fs.mapM fun f => do pure (f.1, ← valTy f.2)
    defTy (.val (.record fs))
  | .variant cs => do
    let cs ← cs.mapM fun c => do pure (c.1, ← valTyOpt c.2)
    defTy (.val (.variant cs))
  | .enum ls => defTy (.val (.enum ls))
  | .flags ls => defTy (.val (.flags ls))

/-- Named parameters. -/
def paramTys : List (String × Silmaril.Wasm.Wit.Binary.Ty) → TM (List (String × Silmaril.Wasm.Component.Binary.ValType))
  | [] => pure []
  | (n, t) :: ps => do let v ← valTy t; pure ((n, v) :: (← paramTys ps))

/-- A function type; its index. -/
def funcTy (s : Sig) : TM Nat := do
  match (← get).share, (← get).fcache.lookup s with
  | true, some j => pure j
  | _, _ =>
    let ps ← paramTys s.params
    let r ← valTyOpt s.result
    let j ← defTy (.func ⟨ps, r, s.async⟩)
    modify fun sc => { sc with fcache := sc.fcache ++ [(s, j)] }
    pure j

/-- An instance or component type, defined by `m` unless an equal one is shared. -/
def shared (k : Kind) (m : TM Nat) : TM Nat := do
  match (← get).share, (← get).kcache.lookup k with
  | true, some j => pure j
  | _, _ =>
    let j ← m
    modify fun sc => { sc with kcache := sc.kcache ++ [(k, j)] }
    pure j

/-- Run a scope computation in a fresh nested scope; its declarations. With `share`
(component types), structurally equal function, instance and component types are
defined once: wac shares types by identity, and within the type of one package an
import and an export of the same type are usually one type; in instance types (and at
the top level) equal function types of different items are usually different types,
and are not shared. -/
def nested (share : Bool) (m : TM Unit) : TM (List ComponentDecl) := do
  match m.run { nom := (← get).nom, share } with
  | .ok ((), s) => pure s.decls
  | .error e => throw e

/-- The instance declarations of a nested scope. -/
def instDecls (ds : List ComponentDecl) : List InstanceDecl :=
  ds.filterMap fun | .inst d => some d | .import .. => none

/-- Record a declared item: a type item allocates a named type index. -/
def declared (n : String) (d : ExternDesc) : TM Unit :=
  match d with
  | .type b => modify fun s =>
    let isRes := match b with | .subResource => true | .eq i => i ∈ s.resIdx
    { s with ntypes := s.ntypes + 1, names := s.names ++ [(n, s.ntypes)],
             resIdx := if isRes then s.resIdx ++ [s.ntypes] else s.resIdx }
  | _ => pure ()

mutual
/-- The descriptor of an item of a kind (defining its type first). -/
def externDesc : Kind → TM ExternDesc
  | .func s => do pure (.func (← funcTy s))
  | .value t => do pure (.value (.type (← valTy t)))
  | .resource _ => pure (.type .subResource)
  | .type k => typeBound k
  | .inst i es => do
    pure (.instance (← shared (.inst i es) do
      let ds ← nested false (exportDecls es)
      defTy (.instance (instDecls ds))))
  | .comp i is es => do
    pure (.component (← shared (.comp i is es) do
      let ds ← nested true (do importDecls is; exportDecls es)
      defTy (.component ds)))
/-- The descriptor of a type item `type k`. -/
def typeBound : Kind → TM ExternDesc
  | .resource _ => pure (.type .subResource)
  | .value t => do
    let s ← get
    match t with
    | .own r => pure (.type (.eq (← namedTy r.name)))
    | .ref r =>
      match s.names.lookup r.name, s.nom.lookup r.name with
      | none, some d => pure (.type (.eq (← nominalTy d)))
      | _, _ => pure (.type (.eq (← namedTy r.name)))
    | _ =>
      match ← freshVal t with
      | some i => pure (.type (.eq i))
      | none =>
        match ← valTy t with
        | .idx i => pure (.type (.eq i))
        | .prim p => pure (.type (.eq (← defTy (.val (.prim p)))))
  | .func s => do pure (.type (.eq (← funcTy s)))
  | .inst _ es => do
    let ds ← nested false (exportDecls es)
    pure (.type (.eq (← defTy (.instance (instDecls ds)))))
  | .comp _ is es => do
    let ds ← nested true (do importDecls is; exportDecls es)
    pure (.type (.eq (← defTy (.component ds))))
  | .type _ => throw "a type of a type"
/-- Silmaril.Wasm.Component.Binary.Export declarations of a scope. -/
def exportDecls : Externs → TM Unit
  | [] => pure ()
  | (n, k) :: es => do
    let d ← externDesc k
    modify fun s => { s with decls := s.decls ++ [.inst (.export ⟨n, .plain0⟩ d)] }
    declared n d
    exportDecls es
/-- Silmaril.Wasm.Component.Binary.Import declarations of a scope. -/
def importDecls : Externs → TM Unit
  | [] => pure ()
  | (n, k) :: es => do
    let d ← externDesc k
    modify fun s => { s with decls := s.decls ++ [.import ⟨n, .plain0⟩ d] }
    declared n d
    importDecls es
end

/-- A world definition (wac's `TypeEncoder::world`): the component type of the world,
wrapped in a component type that exports it under the world's identifier (the layout of
WIT packages). -/
def worldDef (id : String) (is es : Externs) : TM ExternDesc := do
  let ds ← nested false (do importDecls is; exportDecls es)
  let w ← nested true (do
    let t ← defTy (.component ds)
    modify fun s => { s with decls := s.decls ++ [.inst (.export ⟨id, .plain0⟩ (.component t))] })
  pure (.type (.eq (← defTy (.component w))))

/-- An interface definition (wac's `TypeEncoder::interface` at the top level): the
instance type of the interface, wrapped in a component type that exports it under the
interface's identifier (the layout of WIT packages). -/
def ifaceDef (id : String) (es : Externs) : TM ExternDesc := do
  let ds ← nested false (exportDecls es)
  let w ← nested true (do
    let t ← defTy (.instance (instDecls ds))
    modify fun s => { s with decls := s.decls ++ [.inst (.export ⟨id, .plain0⟩ (.instance t))] })
  pure (.type (.eq (← defTy (.component w))))

/-! ## The encoder -/

/-- The sort of a descriptor. -/
def descSort : ExternDesc → ItemSort
  | .coreModule _ => .core .module
  | .func _ => .func
  | .value _ => .value
  | .type _ => .type
  | .component _ => .component
  | .instance _ => .instance

/-- The sort of the items of a kind. -/
def kindSort : Kind → ItemSort
  | .func _ => .func
  | .value _ => .value
  | .resource _ | .type _ => .type
  | .inst .. => .instance
  | .comp .. => .component

/-- The encoder state: the items, the top-level type scope, the other index spaces, the
item of every encoded node and the component index of every imported package. -/
structure ESt where
  items : List Item := []
  sc : Scope := {}
  funcs : Nat := 0
  insts : Nat := 0
  comps : Nat := 0
  vals : Nat := 0
  idx : List (Nat × SortIdx) := []
  pkgs : List (String × Nat) := []
  deriving Inhabited

/-- Emit an item. -/
def ESt.emit (st : ESt) (it : Item) : ESt := { st with items := st.items ++ [it] }

/-- The type items of the declarations a top-level type computation emitted. -/
def tyItems (ds : List ComponentDecl) : List Item :=
  ds.filterMap fun | .inst (.type d) => some (Item.type d) | _ => none

/-- Run a type-scope computation at the top level: its type definitions become items. -/
def runT {α : Type} (m : TM α) (st : ESt) : Except String (α × ESt) :=
  match m.run { st.sc with decls := [] } with
  | .ok (a, sc) => .ok (a, { st with items := st.items ++ tyItems sc.decls, sc := { sc with decls := [] } })
  | .error e => .error e

/-- Allocate the next index of a sort. -/
def ESt.alloc (st : ESt) : ItemSort → Nat × ESt
  | .func => (st.funcs, { st with funcs := st.funcs + 1 })
  | .instance => (st.insts, { st with insts := st.insts + 1 })
  | .component => (st.comps, { st with comps := st.comps + 1 })
  | .value => (st.vals, { st with vals := st.vals + 1 })
  | .type => (st.sc.ntypes, { st with sc := { st.sc with ntypes := st.sc.ntypes + 1 } })
  | .core _ => (0, st)

/-- Record the item of a node. -/
def ESt.setIdx (st : ESt) (i : Nat) (x : SortIdx) : ESt := { st with idx := st.idx ++ [(i, x)] }

/-- Name a top-level type index (a resource when its bound is). -/
def ESt.nameTy (st : ESt) (n : String) (t : Nat) (b : TypeBound) : ESt :=
  let isRes := match b with | .subResource => true | .eq i => i ∈ st.sc.resIdx
  { st with sc := { st.sc with names := st.sc.names ++ [(n, t)],
                               resIdx := if isRes then st.sc.resIdx ++ [t] else st.sc.resIdx } }

/-- Name a top-level type item. -/
def ESt.nameDesc (st : ESt) (n : String) (j : Nat) : ExternDesc → ESt
  | .type b => st.nameTy n j b
  | _ => st

/-- The item of an encoded node. -/
def ESt.itemOf (st : ESt) (j : Nat) : Except String SortIdx :=
  match st.idx.lookup j with
  | some x => .ok x
  | none => .error s!"node {j} is used before it is encoded"

/-- The import name of a package (`package_import_name`). -/
def depName (key : String) : String :=
  match key.splitOn "@" with
  | [n, v] => "unlocked-dep=<" ++ n ++ "@{>=" ++ v ++ "}>"
  | _ => "unlocked-dep=<" ++ key ++ ">"

/-- An import node. -/
def encImport (i : Nat) (n : String) (k : Kind) (st : ESt) : Except String ESt := do
  let (d, st) ← runT (externDesc k) st
  let st := st.emit (.imp n d)
  let (j, st) := st.alloc (descSort d)
  pure ((st.nameDesc n j d).setIdx i ⟨descSort d, j⟩)

/-- The component index of a package, importing it the first time. -/
def encPackage (key : String) (imps exps : Externs) (st : ESt) : Except String (Nat × ESt) :=
  match st.pkgs.lookup key with
  | some c => .ok (c, st)
  | none => do
    let (d, st) ← runT (externDesc (.comp none imps exps)) st
    let st := st.emit (.imp (depName key) d)
    let (c, st) := st.alloc .component
    pure (c, { st with pkgs := st.pkgs ++ [(key, c)] })

/-- Is node `j` an implicit import? -/
def isImplicitNode (g : CGraph) (j : Nat) : Bool :=
  match g.opOf? j with
  | some (.implicit _) => true
  | _ => false

/-- The order of the arguments of an instantiation in wac's encoding: the explicit ones
last to first (wac-graph iterates the incoming edges of the instantiation node, which
petgraph lists newest first), then the implicit ones. -/
def argOrder (g : CGraph) (args : List (String × Nat)) : List (String × Nat) :=
  (args.filter fun a => !isImplicitNode g a.2).reverse ++ args.filter fun a => isImplicitNode g a.2

/-- The exports of an instance kind. -/
def kindExports : Kind → Externs
  | .inst _ es => es
  | _ => []

/-- The type of a definition node. -/
def defnTy (k : Kind) : TM ExternDesc :=
  match k with
  | .comp (some id) is es => worldDef id is es
  | .inst (some id) es => ifaceDef id es
  | _ => typeBound k

/-- The name a definition node `i` (declared as `n`) is exported under: its last export
name. wac keeps one export name per node (`CompositionGraph::export` overwrites it), so
`type a = u32; export a as "a2";` exports the definition as `a2` only. -/
def defnName (g : CGraph) (i : Nat) (n : String) : String :=
  (g.exports.filter (·.2 == i)).getLast?.elim n (·.1)

/-- A non-import node. -/
def encNode (g : CGraph) (i : Nat) (nd : CNode) (st : ESt) : Except String ESt :=
  match nd.op, nd.kind with
  | .defn n, .type k => do
    let (d, st) ← runT (defnTy k) st
    match d with
    | .type (.eq t) =>
      let st := st.emit (.exp (defnName g i n) ⟨.type, t⟩)
      let (j, st) := st.alloc .type
      pure ((st.nameTy n j (.eq t)).setIdx i ⟨.type, j⟩)
    | _ => .error s!"definition `{n}`: resources cannot be defined"
  | .defn n, _ => .error s!"definition `{n}` is not a type"
  | .inst key imps args, _ => do
    let (c, st) ← encPackage key imps (kindExports nd.kind) st
    let as ← (argOrder g args).mapM fun a => (st.itemOf a.2).map (a.1, ·)
    let st := st.emit (.inst c as)
    let (j, st) := st.alloc .instance
    pure (st.setIdx i ⟨.instance, j⟩)
  | .alias src n, k => do
    let x ← st.itemOf src
    if x.sort != .instance then .error s!"alias `{n}` of a node that is not an instance" else
    let st := st.emit (.alias (kindSort k) x.idx n)
    let (j, st) := st.alloc (kindSort k)
    pure (st.setIdx i ⟨kindSort k, j⟩)
  | .imp _, _ | .implicit _, _ => .ok st

/-- Is a node an import? -/
def isImportNode (nd : CNode) : Bool :=
  match nd.op with
  | .imp _ | .implicit _ => true
  | _ => false

/-- Is a kind an instance? -/
def isInstKind : Kind → Bool
  | .inst .. => true
  | _ => false

/-- The import nodes in wac's order: implicit, then explicit; instances first. -/
def importOrder (g : CGraph) : List (Nat × String × Kind) :=
  let ns := g.nodes.zipIdx.filterMap fun (nd, i) => match nd.op with
    | .implicit n => some (i, n, nd.kind)
    | _ => none
  let xs := g.nodes.zipIdx.filterMap fun (nd, i) => match nd.op with
    | .imp n => some (i, n, nd.kind)
    | _ => none
  let all := ns ++ xs
  all.filter (isInstKind ·.2.2) ++ all.filter (!isInstKind ·.2.2)

/-- Is node `j` a type definition? -/
def isDefnNode (g : CGraph) (j : Nat) : Bool :=
  match g.opOf? j with
  | some (.defn _) => true
  | _ => false

/-- The import nodes. -/
def encImports : List (Nat × String × Kind) → ESt → Except String ESt
  | [], st => .ok st
  | (i, n, k) :: rest, st => do encImports rest (← encImport i n k st)

/-- The other nodes, in order. -/
def encNodes (g : CGraph) : List (CNode × Nat) → ESt → Except String ESt
  | [], st => .ok st
  | (nd, i) :: rest, st =>
    if isImportNode nd then encNodes g rest st else do encNodes g rest (← encNode g i nd st)

/-- One export. -/
def encExport (st : ESt) (n : String) (j : Nat) : Except String ESt := do
  let x ← st.itemOf j
  pure ((st.emit (.exp n x)).alloc x.sort).2

/-- The exports that are not type definitions. -/
def encExports (g : CGraph) : List (String × Nat) → ESt → Except String ESt
  | [], st => .ok st
  | (n, j) :: rest, st =>
    if isDefnNode g j then encExports g rest st else do encExports g rest (← encExport st n j)

/-- Encode the graph. -/
def encGraph (g : CGraph) (st : ESt) : Except String ESt := do
  let st ← encImports (importOrder g) st
  let st ← encNodes g g.nodes.zipIdx st
  encExports g g.exports st

/-- The items of the encoding. -/
def encodeItems (nom : NomTable) (g : CGraph) : Except String (List Item) :=
  (encGraph g { sc := { nom } }).map (·.items)

/-- **A composition graph as a component in the composition profile**, given the
nominal definitions of its named types. -/
def encode (nom : NomTable) (g : CGraph) : Except String Ast :=
  (encodeItems nom g).map fun its => .mk (its.map Item.toSection)

end Silmaril.Wasm.Wac.Bridge
