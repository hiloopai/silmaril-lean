module

public import Silmaril.Wasm.Wac.Bridge.Encode.Defs

/-!
# WAC: the encoder with resources shared between instances

`Bridge.encode` writes every instance type closed: a type an instance type refers to must be
defined in it. Real packages break this: a WASI interface uses resources of other interfaces
(`wasi:io/streams` uses `pollable` of `wasi:io/poll`; `wasi:http/types` and every interface of
a `wit-bindgen` component that has `use … .{r}`). wit-component writes such a use as
`(alias export j "r" (type))` in the enclosing scope, after the import `j` of the defining
interface, and `(alias outer 1 k (type))` in the using instance type, followed by its export
`(export "r" (type (eq _)))`. `Bridge.decExtern` reads that back as the item
`("r", .type (.value (.own ⟨.local, "r"⟩)))` (`selfUse`), so `Bridge.encode` fails with
"type `r` is not in scope".

This module is a copy of `Bridge.encode` (same items, same order, same type definitions) with
one addition. Before an instance type is written, the names its items refer to but do not
define (`needs`) are looked up in the enclosing scope (`resolveRes`): a resource of that name
already in scope, or the last instance of the scope exporting a resource of that name (aliased
by `(alias export j "r" (type))`, an `Item.alias .type` at the top level). Each is brought into
the instance type by `(alias outer 1 k (type))` (`aliasIn`) and is in scope there under its name
(`Scope.xnames`, a resource).

Resources are identified by **name**, as in kinds (`Bridge.decExtern` keeps no owner): the
last instance before the using one that exports a resource of the name is taken. In
wit-component's output interfaces are imported in dependency order, so this is the defining
interface or one that re-exports the same resource.

`EncodeR.encodeAny nom g` is `Bridge.encode nom g` when it succeeds (every theorem about
`Bridge.encode` applies), else `EncodeR.encode nom g`. `EncodeR.encodeAny_of_ok` states the
first case.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.EncodeR

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig)
open Silmaril.Wasm.Wac.Bridge (Item Nominal NomTable firstArgs descSort kindSort depName
  isImplicitNode argOrder kindExports defnName isImportNode isInstKind importOrder isDefnNode)

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
  /-- Resources of other instances, aliased into this scope, by name. -/
  xnames : List (String × Nat) := []
  /-- The instances of this scope (imports and exports of instance sort): index and
  exports, in order. -/
  insts : List (Nat × Externs) := []
  /-- The number of instances of this scope. -/
  ninst : Nat := 0
  deriving Inhabited

abbrev TM := StateT Scope (Except String)

/-- Define a type; its index. -/
def defTy (d : DefType) : TM Nat :=
  modifyGet fun s => (s.ntypes, { s with decls := s.decls ++ [.inst (.type d)], ntypes := s.ntypes + 1 })

/-- The index of a named type. -/
def namedTy (n : String) : TM Nat := do
  match (← get).names.lookup n with
  | some i => pure i
  | none =>
    match (← get).xnames.lookup n with
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
def valTy : Ty → TM Silmaril.Wasm.Component.Binary.ValType
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
def valTyOpt : Option Ty → TM (Option Silmaril.Wasm.Component.Binary.ValType)
  | none => pure none
  | some t => do pure (some (← valTy t))
/-- Value types. -/
def valTys : List Ty → TM (List Silmaril.Wasm.Component.Binary.ValType)
  | [] => pure []
  | t :: ts => do let v ← valTy t; pure (v :: (← valTys ts))
end

/-- The definiens of a type alias whose definiens is an anonymous type, defined anew
(`none` for other types). wac gives every type expression of a document its own
identity, and encodes the definiens of an alias declaration afresh (`DefinedType::Alias`
of a defined type), even if an equal anonymous type was defined before. -/
def freshVal : Ty → TM (Option Nat)
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
def paramTys : List (String × Ty) → TM (List (String × Silmaril.Wasm.Component.Binary.ValType))
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

/-! ## Resources of other instances -/

mutual
/-- The type names a value type refers to. -/
def tyRefs : Ty → List String
  | .prim _ => []
  | .ref r | .own r | .borrow r => [r.name]
  | .list t | .fixedList t _ | .option t => tyRefs t
  | .map k v => tyRefs k ++ tyRefs v
  | .result a b => tyRefsOpt a ++ tyRefsOpt b
  | .tuple ts => tyRefsL ts
  | .future t | .stream t => tyRefsOpt t
/-- The type names an optional value type refers to. -/
def tyRefsOpt : Option Ty → List String
  | none => []
  | some t => tyRefs t
/-- The type names value types refer to. -/
def tyRefsL : List Ty → List String
  | [] => []
  | t :: ts => tyRefs t ++ tyRefsL ts
end

/-- The type names an item of an instance refers to. -/
def kindRefs : Kind → List String
  | .func s => (s.params.map (tyRefs ·.2)).flatten ++ tyRefsOpt s.result
  | .value t | .type (.value t) => tyRefs t
  | _ => []

/-- A type item that is the use of a resource of another instance under its own name:
`(n, type own n)` (how `Bridge.decExtern` reads `(alias outer 1 k (type))` followed by
`(export "n" (type (eq _)))`). -/
def selfUse (n : String) : Kind → Bool
  | .type (.value (.own r)) => r.name == n
  | _ => false

/-- The names an instance's items refer to but do not define: the resources it uses from
other instances. -/
def needs (es : Externs) : List String :=
  ((es.map fun p => kindRefs p.2).flatten).eraseDups.filter fun r =>
    !(es.any fun p => p.1 == r && !selfUse p.1 p.2)

/-- An item that is a resource (defined, or used from another instance). -/
def isResKind : Kind → Bool
  | .type (.resource _) | .resource _ | .type (.value (.own _)) => true
  | _ => false

/-- The index of the resource `r` in this scope, aliasing it from the last instance of the
scope that exports it (`(alias export j "r" (type))`) the first time; `none` when no
instance of the scope has it. -/
def resolveRes (r : String) : TM (Option Nat) := do
  let s ← get
  match s.names.lookup r with
  | some i => pure (if i ∈ s.resIdx then some i else none)
  | none =>
    match s.xnames.lookup r with
    | some i => pure (some i)
    | none =>
      match s.insts.reverse.find? (fun p => p.2.any fun q => q.1 == r && isResKind q.2) with
      | some (j, _) =>
        let i := s.ntypes
        set { s with decls := s.decls ++ [ComponentDecl.inst (.alias ⟨.type, .export j r⟩)], ntypes := i + 1,
                     xnames := s.xnames ++ [(r, i)], resIdx := s.resIdx ++ [i] }
        pure (some i)
      | none => pure none

/-- The resources an instance type needs from the enclosing scope, with their indices
there. -/
def availFor (es : Externs) : TM (List (String × Nat)) :=
  (needs es).foldlM (init := []) fun acc r => do
    match ← resolveRes r with
    | some i => pure (acc ++ [(r, i)])
    | none => pure acc

/-- Bring the resources of the enclosing scope into a nested scope:
`(alias outer 1 k (type))` for each. -/
def aliasIn (av : List (String × Nat)) : TM Unit :=
  av.forM fun p => modify fun s =>
    { s with decls := s.decls ++ [ComponentDecl.inst (.alias ⟨.type, .outer 1 p.2⟩)], ntypes := s.ntypes + 1,
             xnames := s.xnames ++ [(p.1, s.ntypes)], resIdx := s.resIdx ++ [s.ntypes] }

/-- Record an instance item of the scope. -/
def declInst (k : Kind) (d : ExternDesc) : TM Unit :=
  match d, k with
  | .instance _, .inst _ es => modify fun s =>
    { s with insts := s.insts ++ [(s.ninst, es)], ninst := s.ninst + 1 }
  | .instance _, _ => modify fun s => { s with ninst := s.ninst + 1 }
  | _, _ => pure ()

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
      let av ← availFor es
      let ds ← nested false (do aliasIn av; exportDecls es)
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
    let av ← availFor es
    let ds ← nested false (do aliasIn av; exportDecls es)
    pure (.type (.eq (← defTy (.instance (instDecls ds)))))
  | .comp _ is es => do
    let ds ← nested true (do importDecls is; exportDecls es)
    pure (.type (.eq (← defTy (.component ds))))
  | .type _ => throw "a type of a type"
/-- Export declarations of a scope. -/
def exportDecls : Externs → TM Unit
  | [] => pure ()
  | (n, k) :: es => do
    let d ← externDesc k
    modify fun s => { s with decls := s.decls ++ [.inst (.export ⟨n, .plain0⟩ d)] }
    declared n d
    declInst k d
    exportDecls es
/-- Import declarations of a scope. -/
def importDecls : Externs → TM Unit
  | [] => pure ()
  | (n, k) :: es => do
    let d ← externDesc k
    modify fun s => { s with decls := s.decls ++ [.import ⟨n, .plain0⟩ d] }
    declared n d
    declInst k d
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
  ds.filterMap fun
    | .inst (.type d) => some (Item.type d)
    | .inst (.alias ⟨.type, .export j n⟩) => some (Item.alias .type j n)
    | _ => none

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

/-- An import node. -/
def encImport (i : Nat) (n : String) (k : Kind) (st : ESt) : Except String ESt := do
  let (d, st) ← runT (externDesc k) st
  let st := st.emit (.imp n d)
  let (j, st) := st.alloc (descSort d)
  let st := match d, k with
    | .instance _, .inst _ es => { st with sc := { st.sc with insts := st.sc.insts ++ [(j, es)] } }
    | _, _ => st
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

/-- The type of a definition node. -/
def defnTy (k : Kind) : TM ExternDesc :=
  match k with
  | .comp (some id) is es => worldDef id is es
  | .inst (some id) es => ifaceDef id es
  | _ => typeBound k

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

/-- **The encoder `wasm-wac` runs**: `Bridge.encode` when it succeeds, else the encoder with
resources shared between instances. -/
def encodeAny (nom : NomTable) (g : CGraph) : Except String Ast :=
  match Bridge.encode nom g with
  | .ok c => .ok c
  | .error _ => encode nom g

theorem encodeAny_of_ok {nom : NomTable} {g : CGraph} {c : Ast} (h : Bridge.encode nom g = .ok c) :
    encodeAny nom g = .ok c := by
  simp [encodeAny, h]

end Silmaril.Wasm.Wac.EncodeR
