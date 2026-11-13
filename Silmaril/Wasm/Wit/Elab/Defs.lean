module

public import Silmaril.Wasm.Wit.Valid.Defs
public import Silmaril.Wasm.Wit.Binary.Custom.Defs

/-!
# WIT: elaboration of the surface AST to the resolved binary model

`elaborate U p` turns the package `p` of a universe `U` of surface packages
(`Silmaril.Wasm.Wit.Syntax`) into the resolved model the binary encoder works on
(`Silmaril.Wasm.Wit.Binary.Package`), together with the interfaces of the other
packages (`Binary.Env`). It follows wit-parser `0.263.0` (`src/ast/resolve.rs`,
`src/resolve/mod.rs`, `src/ast/toposort.rs`; crate sha256 recorded in
`docs/projects/wasm-components.md`), step by step:

* **Feature gates** (`Universe.gate`): items gated `@unstable(feature = f)` are
  dropped unless `f` is enabled; `@since`/`@deprecated` are kept and become
  `Binary.Stability` with versions printed as text (`Version.str`).
* **Validity**: the gated universe must pass `check` (`Valid`, by `check_iff`).
* **Names** (`Ctx`): a name `x` in the scope of an owner is the local type
  `⟨.local, x⟩`; a `use path.{y as x}` becomes the local type `x` with kind
  `.type (.ref ⟨.iface j, y⟩)` (wit-parser's `resolve_use`), with the use's
  stability and no docs.
* **Own sugar**: a bare name denoting a resource (through aliases and `use`
  chains, `IsResource`) in a type position is `own<x>`, except as the whole
  right-hand side of `type y = x;`, which stays a reference (as in wit-parser).
* **Self sugar**: a method gets the explicit first parameter `self: borrow<r>`,
  a constructor is named after its resource and returns `own<r>`.
* **Type order** (`toposort`): `use`d names first, in order, then the type
  definitions of the scope in wit-parser's topological order: repeatedly the
  first entry (in source order, `use`d names included) whose references are all
  placed.
* **Functions** in source order, the functions of a resource where the resource
  is defined (the encoder reorders them; the decoder's normal form is
  `Binary.Package.canon`).
* **Worlds** (`WorldElab`): the pre-elaboration items (types, then imports and
  resource functions in source order), then `include`s in order (`includeInto`:
  the included world, elaborated first, renamed by `with`; a named item clashing
  with an existing one is an error, an interface import merges its stability),
  then wit-parser's `elaborate_world`: imports sorted by class (`importClass`),
  the interfaces each import depends on imported first (*implicit imports*,
  `importIface`), exported interfaces added with their dependencies, which must
  not be both imported and exported (`addExport`, the
  `InvalidTransitiveDependency` error), and imports sorted again.

`elaborate` then requires the binary validity conditions
(`Binary.Package.Valid`, `NamesUnique`) of its output, so that every successful
elaboration satisfies the hypotheses of `decodePackage_encodePackage_canon`;
`Silmaril.Wasm.Wit.Elab.Thms` states what is proved about these checks.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit

/-- The decimal digits of `n` (with fuel `f`), in front of `acc`. -/
def Elab.digitsAux : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | f + 1, n, acc =>
    let acc := Char.ofNat (48 + n % 10) :: acc
    if n / 10 = 0 then acc else Elab.digitsAux f (n / 10) acc

/-- A natural number in decimal (written out so that the kernel evaluates it). -/
def Elab.natStr (n : Nat) : String := String.ofList (Elab.digitsAux (n + 1) n [])

/-- Strings joined by a separator. -/
def Elab.joinWith (sep : String) : List String → String
  | [] => ""
  | [s] => s
  | s :: rest => s ++ sep ++ Elab.joinWith sep rest

/-- A version as SemVer text: `major.minor.patch(-pre)?(+build)?`. -/
def Version.str (v : Version) : String :=
  Elab.natStr v.major ++ "." ++ Elab.natStr v.minor ++ "." ++ Elab.natStr v.patch ++
    (if v.pre = [] then "" else "-" ++ Elab.joinWith "." v.pre) ++
    (if v.build = [] then "" else "+" ++ Elab.joinWith "." v.build)

namespace Elab

def pkgName (p : PackageName) : Binary.PackageName := ⟨p.ns, p.name, p.version.map Version.str⟩

def ifaceName (i : ItemId) : Binary.IfaceName := ⟨pkgName i.pkg, i.name⟩

/-- The stability of a list of gates (`unknown` for an invalid combination). -/
def stab (gs : List Gate) : Binary.Stability :=
  match Gate.stability gs with
  | some (.stable v d) => .stable v.str (d.map Version.str)
  | some (.unstable f d) => .unstable f (d.map Version.str)
  | _ => .unknown

end Elab

/-! ## Feature gates -/

/-- Whether an item with gates `gs` is kept when the features `fs` are enabled. -/
def Elab.gateOn (fs : List Name) (gs : List Gate) : Bool :=
  match Gate.stability gs with
  | some (.unstable f _) => fs.contains f
  | _ => true

def TypeDef.gate (fs : List Name) (d : TypeDef) : TypeDef :=
  match d.kind with
  | .resource fns => { d with kind := .resource (fns.filter fun rf => Elab.gateOn fs rf.gates) }
  | _ => d

def IfaceItem.gates : IfaceItem → List Gate
  | .type d => d.gates
  | .use u => u.gates
  | .func f => f.gates

def IfaceItem.gate (fs : List Name) : IfaceItem → IfaceItem
  | .type d => .type (TypeDef.gate fs d)
  | it => it

def gateItems (fs : List Name) (items : List IfaceItem) : List IfaceItem :=
  (items.filter fun it => Elab.gateOn fs it.gates).map (IfaceItem.gate fs)

def WorldItem.gates : WorldItem → List Gate
  | .import e | .export e => e.gates
  | .use u => u.gates
  | .type d => d.gates
  | .include i => i.gates

def WorldExtern.gate (fs : List Name) (e : WorldExtern) : WorldExtern :=
  match e.ext with
  | .iface n items => { e with ext := .iface n (gateItems fs items) }
  | _ => e

def WorldItem.gate (fs : List Name) : WorldItem → WorldItem
  | .import e => .import (e.gate fs)
  | .export e => .export (e.gate fs)
  | .type d => .type (TypeDef.gate fs d)
  | it => it

def PackageItem.gates : PackageItem → List Gate
  | .iface I => I.gates
  | .world W => W.gates
  | .use u => u.gates

def PackageItem.gate (fs : List Name) : PackageItem → PackageItem
  | .iface I => .iface { I with items := gateItems fs I.items }
  | .world W => .world { W with items := (W.items.filter fun it => Elab.gateOn fs it.gates).map (WorldItem.gate fs) }
  | it => it

def Package.gate (fs : List Name) (P : Package) : Package :=
  { P with items := (P.items.filter fun it => Elab.gateOn fs it.gates).map (PackageItem.gate fs) }

/-- The universe with the items of disabled features removed. -/
def Universe.gate (fs : List Name) (U : Universe) : Universe := U.map (Package.gate fs)

/-- The interfaces and worlds of a package, in source order. -/
def Package.ifaces (P : Package) : List Interface := P.items.filterMap fun | .iface I => some I | _ => none
def Package.worlds (P : Package) : List World := P.items.filterMap fun | .world W => some W | _ => none

namespace Elab

/-! ## Types -/

/-- What elaboration of names needs: the universe and the fuel of the resolution
functions (as in `check`). -/
structure Ctx where
  U : Universe
  F : Nat
  G : Nat

def Ctx.ofUniverse (U : Universe) : Ctx := ⟨U, U.ifaceIds.length, U.typeIds.length⟩

/-- `x` denotes a resource in the scope of `o`. -/
def Ctx.isRes (c : Ctx) (o : Owner) (x : Name) : Bool :=
  match bind c.U c.F o x with
  | some t => Wit.isRes c.U c.F c.G t
  | none => false

def loc (x : Name) : Binary.TyRef := ⟨.local, x⟩

mutual
/-- A type expression in the scope of `o`. -/
def elabTy (c : Ctx) (o : Owner) : Ty → Binary.Ty
  | .bool => .prim .bool
  | .s8 => .prim .s8
  | .s16 => .prim .s16
  | .s32 => .prim .s32
  | .s64 => .prim .s64
  | .u8 => .prim .u8
  | .u16 => .prim .u16
  | .u32 => .prim .u32
  | .u64 => .prim .u64
  | .f32 => .prim .f32
  | .f64 => .prim .f64
  | .char => .prim .char
  | .string => .prim .string
  | .errorContext => .prim .errorContext
  | .named n => if c.isRes o n then .own (loc n) else .ref (loc n)
  | .list t => .list (elabTy c o t)
  | .fixedList t n => .fixedList (elabTy c o t) n
  | .map k v => .map (elabTy c o k) (elabTy c o v)
  | .tuple ts => .tuple (elabTys c o ts)
  | .option t => .option (elabTy c o t)
  | .result a b => .result (elabTyOpt c o a) (elabTyOpt c o b)
  | .own r => .own (loc r)
  | .borrow r => .borrow (loc r)
  | .future t => .future (elabTyOpt c o t)
  | .stream t => .stream (elabTyOpt c o t)
def elabTyOpt (c : Ctx) (o : Owner) : Option Ty → Option Binary.Ty
  | none => none
  | some t => some (elabTy c o t)
def elabTys (c : Ctx) (o : Owner) : List Ty → List Binary.Ty
  | [] => []
  | t :: ts => elabTy c o t :: elabTys c o ts
end

/-- The kind of a type definition. -/
def elabKind (c : Ctx) (o : Owner) : TypeDefKind → Binary.TyDefKind
  | .alias (.named n) => .type (.ref (loc n))
  | .alias t => .type (elabTy c o t)
  | .record fs => .record (fs.map fun f => { name := f.name, ty := elabTy c o f.ty, docs := f.docs.contents })
  | .variant cs => .variant (cs.map fun k => { name := k.name, ty := elabTyOpt c o k.ty, docs := k.docs.contents })
  | .enum ls => .enum (ls.map fun l => { name := l.name, ty := (), docs := l.docs.contents })
  | .flags ls => .flags (ls.map fun l => { name := l.name, ty := (), docs := l.docs.contents })
  | .resource _ => .resource

def elabTypeDef (c : Ctx) (o : Owner) (d : TypeDef) : Binary.TypeDef :=
  { name := d.name, kind := elabKind c o d.kind, docs := d.docs.contents, stability := stab d.gates }

/-- The types a `use` defines in the scope of `o`. -/
def elabUse (c : Ctx) (o : Owner) (u : Use) : List Binary.TypeDef :=
  let j := (resolve c.U .iface o.pkg u.path).getD ⟨o.pkg, u.path.name⟩
  u.names.map fun un =>
    { name := un.bound, kind := .type (.ref ⟨.iface (ifaceName j), un.name⟩), stability := stab u.gates }

/-! ## Topological order of a scope -/

/-- An entry of a scope: its name, the names its definition refers to, and its
type (`none` for a `use`d name, which is placed separately). -/
abbrev Entry := Name × List Name × Option Binary.TypeDef

/-- wit-parser's `toposort`: repeatedly the first remaining entry whose
references are all placed; `none` if none is ready (a cycle or a missing name). -/
def toposort : Nat → List Name → List Entry → Option (List Entry)
  | _, _, [] => some []
  | 0, _, _ :: _ => none
  | f + 1, placed, rest@(_ :: _) =>
    match rest.find? (fun e => e.2.1.all (· ∈ placed)) with
    | none => none
    | some e => (toposort f (e.1 :: placed) (rest.erase e)).map (e :: ·)

/-- The entries of a scope, in source order. -/
def scopeEntries (c : Ctx) (o : Owner) : List ScopeItem → List Entry
  | [] => []
  | .type d :: rest => (d.name, d.refs.map (·.2), some (elabTypeDef c o d)) :: scopeEntries c o rest
  | .use u :: rest => u.names.map (fun un => (un.bound, [], none)) ++ scopeEntries c o rest

/-- The types of a scope: `use`d names first, then the definitions in
topological order. -/
def elabTypes (c : Ctx) (o : Owner) (items : List ScopeItem) : Option (List Binary.TypeDef) := do
  let es := scopeEntries c o items
  let order ← toposort es.length [] es
  pure (items.flatMap (fun | .use u => elabUse c o u | .type _ => []) ++ order.filterMap (·.2.2))

/-! ## Functions -/

def elabParams (c : Ctx) (o : Owner) (ps : List (Name × Ty)) : List (String × Binary.Ty) :=
  ps.map fun p => (p.1, elabTy c o p.2)

def elabFunc (c : Ctx) (o : Owner) (n : Name) (f : Func) (d : Docs) (gs : List Gate) : Binary.Func :=
  { name := n, async := f.async, params := elabParams c o f.params,
    result := elabTyOpt c o f.result, docs := d.contents, stability := stab gs }

/-- A function of the resource `r`. -/
def elabResFunc (c : Ctx) (o : Owner) (r : Name) (rf : ResourceFunc) : Binary.Func :=
  match rf.kind with
  | .ctor =>
    { name := r, kind := .constructor r, params := elabParams c o rf.func.params,
      result := some ((elabTyOpt c o rf.func.result).getD (.own (loc r))),
      docs := rf.docs.contents, stability := stab rf.gates }
  | .method n =>
    { name := n, kind := .method r, async := rf.func.async,
      params := ("self", .borrow (loc r)) :: elabParams c o rf.func.params,
      result := elabTyOpt c o rf.func.result, docs := rf.docs.contents, stability := stab rf.gates }
  | .static n =>
    { name := n, kind := .static r, async := rf.func.async, params := elabParams c o rf.func.params,
      result := elabTyOpt c o rf.func.result, docs := rf.docs.contents, stability := stab rf.gates }

/-- The resource functions of a type definition. -/
def resFuncs (c : Ctx) (o : Owner) (d : TypeDef) : List Binary.Func :=
  match d.kind with
  | .resource fns => fns.map (elabResFunc c o d.name)
  | _ => []

/-- The functions of an interface item, in source order. -/
def itemFuncs (c : Ctx) (o : Owner) : IfaceItem → List Binary.Func
  | .func f => [elabFunc c o f.name f.func f.docs f.gates]
  | .type d => resFuncs c o d
  | .use _ => []

/-- An interface body (of a package interface or an inline interface). -/
def elabBody (c : Ctx) (o : Owner) (items : List IfaceItem) (d : Docs) (gs : List Gate) :
    Option Binary.Interface := do
  let types ← elabTypes c o (items.filterMap IfaceItem.scope)
  pure { types, funcs := items.flatMap (itemFuncs c o), docs := d.contents, stability := stab gs }

/-! ## Worlds: keyed lists -/

/-- The stability of a world item. -/
def itemStab : Binary.WorldItem → Binary.Stability
  | .ifaceRef _ _ s => s
  | .ifaceInline _ b => b.stability
  | .func f => f.stability
  | .type t => t.stability

/-- The interface a world item imports or exports, if it is a named one. -/
def itemIface : Binary.WorldItem → Option Binary.IfaceName
  | .ifaceRef i _ _ => some i
  | _ => none

/-- The interfaces an imported or exported interface uses types from
(`interface_direct_deps`). -/
def itemDeps (env : Binary.Env) : Binary.WorldItem → List Binary.IfaceName
  | .ifaceRef i _ _ => ((Binary.Env.find? env i).map Binary.directDeps).getD []
  | .ifaceInline _ b => Binary.directDeps b
  | _ => []

/-- The interface a world type is `use`d from (`type_interface_dep`). -/
def typeDep : Binary.TypeDef → Option Binary.IfaceName
  | ⟨_, .type (.ref ⟨.iface j, _⟩), _, _⟩ => some j
  | _ => none

/-- wit-parser's import classes: interfaces, `use`d types, other types,
freestanding functions, resource functions. -/
def importClass : Binary.WorldItem → Nat
  | .ifaceRef .. | .ifaceInline .. => 0
  | .type t => if (typeDep t).isSome then 1 else 2
  | .func f => if f.kind.resource?.isNone then 3 else 4

/-- A stable sort by import class. -/
def sortImports (its : List Binary.WorldItem) : List Binary.WorldItem :=
  (List.range 5).flatMap fun k => its.filter (importClass · = k)

def hasKey (its : List Binary.WorldItem) (k : String) : Bool := its.any (·.key == k)

/-- Insert an item whose key must be new. -/
def insertNew (its : List Binary.WorldItem) (it : Binary.WorldItem) : Except String (List Binary.WorldItem) :=
  if hasKey its it.key then throw s!"world item `{it.key}` defined more than once" else pure (its ++ [it])

/-- Insert an item unless its key is present. -/
def insertIfNew (its : List Binary.WorldItem) (it : Binary.WorldItem) : List Binary.WorldItem :=
  if hasKey its it.key then its else its ++ [it]

/-! ## Worlds: implicit imports and exports -/

/-- `elaborate_world_import`: import the interfaces `it` depends on (with
stability `st` and no docs), then `it`, unless its key is present. -/
def importIface (env : Binary.Env) (st : Binary.Stability) :
    Nat → Binary.WorldItem → List Binary.WorldItem → List Binary.WorldItem
  | 0, _, acc => acc
  | f + 1, it, acc =>
    if hasKey acc it.key then acc else
    let acc := (itemDeps env it).foldl (fun acc j => importIface env st f (.ifaceRef j none st) acc) acc
    insertIfNew acc it

/-- The first pass over the (sorted) imports of a world. -/
def elabImport (env : Binary.Env) (fuel : Nat) (acc : List Binary.WorldItem) (it : Binary.WorldItem) :
    Except String (List Binary.WorldItem) :=
  match it with
  | .ifaceRef .. | .ifaceInline .. => pure (importIface env (itemStab it) fuel it acc)
  | .func _ => insertNew acc it
  | .type t =>
    let acc := match typeDep t with
      | some j => importIface env t.stability fuel (.ifaceRef j none t.stability) acc
      | none => acc
    insertNew acc it

/-- The state of export elaboration: imports, exports, interfaces required as
imports. -/
structure XState where
  imports : List Binary.WorldItem
  exports : List Binary.WorldItem
  req : List Binary.IfaceName := []

def reqHas (req : List Binary.IfaceName) (it : Binary.WorldItem) : Bool :=
  match itemIface it with
  | some i => req.contains i
  | none => false

/-- wit-parser's `add_world_export`; `none` is the `InvalidTransitiveDependency`
error (an interface both imported and exported). -/
def addExport (env : Binary.Env) (xs : List String) :
    Nat → Binary.WorldItem → Bool → XState → Option XState
  | 0, _, _, s => some s
  | f + 1, it, add, s =>
    if hasKey s.exports it.key then (if add then some s else none) else
    if !add && reqHas s.req it then some s else
    let st := itemStab it
    match (itemDeps env it).foldlM (fun s j =>
        addExport env xs f (.ifaceRef j none st) (add && xs.contains j.id) s) s with
    | none => none
    | some s =>
      if add then
        if reqHas s.req it then none
        else some { s with exports := s.exports ++ [it] }
      else
        some { s with req := (itemIface it).toList ++ s.req, imports := insertIfNew s.imports it }

/-- wit-parser's `elaborate_world` on pre-elaboration imports and exports. -/
def elabWorldItems (env : Binary.Env) (imports exports : List Binary.WorldItem) :
    Except String (List Binary.WorldItem × List Binary.WorldItem) := do
  let fuel := env.length + 1
  let imps ← (sortImports imports).foldlM (elabImport env fuel) []
  let funcs ← (exports.filter fun it => match it with | .func _ => true | _ => false).foldlM insertNew []
  let ifs := exports.filter fun it => match it with | .ifaceRef .. | .ifaceInline .. => true | _ => false
  let xs := ifs.map (·.key)
  let some s := ifs.foldlM (fun s it => addExport env xs fuel it true s) { imports := imps, exports := funcs }
    | throw "an interface is both imported and exported by the dependencies of an export"
  if (ifs.map (·.key)).Nodup then pure (sortImports s.imports, s.exports)
  else throw "an interface is exported more than once"

/-! ## Worlds: `include` -/

/-- The renaming of `include … with { a as b }` (the first matching name). -/
def renameBy (ns : List IncludeName) (n : String) : String :=
  match ns.find? (·.name = n) with
  | some x => x.as
  | none => n

def renameRef (σ : String → String) (r : Binary.TyRef) : Binary.TyRef :=
  match r.owner with
  | .local => ⟨.local, σ r.name⟩
  | _ => r

mutual
/-- Rename the world's local types in a type. -/
def renameTy (σ : String → String) : Binary.Ty → Binary.Ty
  | .ref r => .ref (renameRef σ r)
  | .own r => .own (renameRef σ r)
  | .borrow r => .borrow (renameRef σ r)
  | .list t => .list (renameTy σ t)
  | .fixedList t n => .fixedList (renameTy σ t) n
  | .map k v => .map (renameTy σ k) (renameTy σ v)
  | .option t => .option (renameTy σ t)
  | .result a b => .result (renameTyOpt σ a) (renameTyOpt σ b)
  | .tuple ts => .tuple (renameTys σ ts)
  | .future t => .future (renameTyOpt σ t)
  | .stream t => .stream (renameTyOpt σ t)
  | .prim p => .prim p
def renameTyOpt (σ : String → String) : Option Binary.Ty → Option Binary.Ty
  | none => none
  | some t => some (renameTy σ t)
def renameTys (σ : String → String) : List Binary.Ty → List Binary.Ty
  | [] => []
  | t :: ts => renameTy σ t :: renameTys σ ts
end

def renameKind (σ : String → String) : Binary.TyDefKind → Binary.TyDefKind
  | .record fs => .record (fs.map fun f => { f with ty := renameTy σ f.ty })
  | .variant cs => .variant (cs.map fun k => { k with ty := renameTyOpt σ k.ty })
  | .type t => .type (renameTy σ t)
  | k => k

def renameFunc (σ : String → String) (f : Binary.Func) : Binary.Func :=
  { f with
    name := match f.kind with
      | .freestanding => σ f.name
      | .constructor r => σ r
      | _ => f.name
    kind := match f.kind with
      | .freestanding => .freestanding
      | .method r => .method (σ r)
      | .static r => .static (σ r)
      | .constructor r => .constructor (σ r)
    params := f.params.map fun p => (p.1, renameTy σ p.2)
    result := renameTyOpt σ f.result }

/-- An item of an included world, renamed. -/
def renameItem (σ : String → String) : Binary.WorldItem → Binary.WorldItem
  | .ifaceRef i d s => .ifaceRef i d s
  | .ifaceInline n b => .ifaceInline (σ n) b
  | .func f => .func (renameFunc σ f)
  | .type t => .type { t with name := σ t.name, kind := renameKind σ t.kind }

/-- `update_stability`. -/
def updateStab (src dst : Binary.Stability) : Option Binary.Stability :=
  if src = dst then some dst else
  match src, dst with
  | .unknown, _ => some dst
  | _, .unknown => some src
  | _, _ => none

def stabIsStable : Binary.Stability → Bool
  | .stable .. => true
  | _ => false

/-- Insert one included item (`resolve_include_item`): a named item must be new;
an interface merges its stability with the import or export present. -/
def includeItem (external : Bool) (its : List Binary.WorldItem) (it : Binary.WorldItem) :
    Except String (List Binary.WorldItem) :=
  match it with
  | .ifaceRef i _ s =>
    let (its, dst) := match its.find? (·.key == it.key) with
      | some old => (its, itemStab old)
      | none => (its ++ [it], s)
    let new? := if external && stabIsStable s then some .unknown else updateStab s dst
    match new? with
    | none => throw s!"stability mismatch for `{i.id}`"
    | some st => pure (its.map fun x => match x with
        | .ifaceRef j d' _ => if j = i then .ifaceRef j d' st else x
        | x => x)
  | _ => insertNew its it

/-- Include the world `W` (already elaborated) into the items `imps`/`exps`. -/
def includeInto (external : Bool) (ns : List IncludeName) (W : Binary.World)
    (imps exps : List Binary.WorldItem) : Except String (List Binary.WorldItem × List Binary.WorldItem) := do
  let σ := renameBy ns
  let imps ← (W.imports.map (renameItem σ)).foldlM (includeItem external) imps
  let exps ← (W.exports.map (renameItem σ)).foldlM (includeItem external) exps
  pure (imps, exps)

/-! ## Worlds of the universe -/

/-- The pre-elaboration imports and exports of a world `W` with id `w`: its
types, then imports and resource functions in source order; exports. -/
def preItems (c : Ctx) (w : ItemId) (W : World) :
    Except String (List Binary.WorldItem × List Binary.WorldItem) := do
  let o : Owner := .world w
  let some types := elabTypes c o (W.items.filterMap WorldItem.scope)
    | throw s!"world `{w.name}`: cyclic or undefined types"
  let ext (isExport : Bool) (e : WorldExtern) : Except String Binary.WorldItem :=
    match e.ext with
    | .func n f => pure (.func (elabFunc c o n f e.docs e.gates))
    | .iface n items =>
      match elabBody c (.inline w isExport n) items e.docs e.gates with
      | some b => pure (.ifaceInline n b)
      | none => throw s!"world `{w.name}`, `{n}`: cyclic or undefined types"
    | .path p => pure (.ifaceRef (ifaceName ((resolve c.U .iface w.pkg p).getD ⟨w.pkg, p.name⟩))
        e.docs.contents (stab e.gates))
  let imps ← W.items.foldlM (fun acc it => match it with
    | .import e => do
      let x ← ext false e
      pure (acc ++ [x])
    | .type d => pure (acc ++ (resFuncs c o d).map .func)
    | _ => pure acc) (types.map .type)
  let exps ← W.items.foldlM (fun acc it => match it with
    | .export e => do
      let x ← ext true e
      pure (acc ++ [x])
    | _ => pure acc) []
  pure (imps, exps)

/-- The includes of a world, resolved. -/
def includesOf (c : Ctx) (w : ItemId) (W : World) : List (ItemId × List IncludeName) :=
  W.items.filterMap fun
    | .include i => some ((resolve c.U .world w.pkg i.path).getD ⟨w.pkg, i.path.name⟩, i.names)
    | _ => none

/-- The interfaces of the universe, elaborated. -/
def elabEnv (c : Ctx) : Except String Binary.Env :=
  c.U.flatMap (fun P => P.items.filterMap fun | .iface I => some (P.name, I) | _ => none) |>.mapM fun (p, I) =>
    let i : ItemId := ⟨p, I.name⟩
    match elabBody c (.iface i) I.items I.docs I.gates with
    | some b => pure (ifaceName i, b)
    | none => throw s!"interface `{I.name}`: cyclic or undefined types"

/-- Elaborate the world `w` of the universe (its includes first, with `fuel`
bounding the depth of `include` chains). -/
def elabWorld (c : Ctx) (env : Binary.Env) : Nat → ItemId → Except String Binary.World
  | 0, _ => throw "include chain too long"
  | f + 1, w => do
    let some W := c.U.world? w | throw s!"unknown world `{w.name}`"
    let (imps, exps) ← preItems c w W
    let (imps, exps) ← (includesOf c w W).foldlM (fun (acc : List Binary.WorldItem × List Binary.WorldItem) (inc : ItemId × List IncludeName) => do
      let W' ← elabWorld c env f inc.1
      includeInto (inc.1.pkg != w.pkg) inc.2 W' acc.1 acc.2) (imps, exps)
    let (imps, exps) ← elabWorldItems env imps exps
    pure { imports := imps, exports := exps, docs := W.docs.contents, stability := stab W.gates }

/-! ## Binary validity, decided -/

def IfaceName.validB (i : Binary.IfaceName) : Bool :=
  !i.pkg.ns.toList.contains ':' && !i.pkg.name.toList.contains '/' && !i.name.toList.contains '@'

def Func.validB (f : Binary.Func) : Bool :=
  match f.kind with
  | .freestanding => f.async || f.name.toList.head? != some '['
  | .method r | .static r => !r.toList.contains '.'
  | .constructor r => f.name == r && !f.async

def Interface.validB (b : Binary.Interface) : Bool := b.funcs.all Func.validB

def WorldItem.validB : Binary.WorldItem → Bool
  | .ifaceRef i _ _ => IfaceName.validB i
  | .ifaceInline n b => !n.toList.contains ':' && Interface.validB b
  | .func f => Func.validB f
  | .type _ => true

def Package.validB (p : Binary.Package) (deps : Binary.Env) : Bool :=
  (!p.interfaces.isEmpty || !p.worlds.isEmpty) &&
  p.interfaces.all (fun nb => IfaceName.validB (p.name.iface nb.1)) &&
  p.worlds.all (fun nw => IfaceName.validB (p.name.iface nw.1)) &&
  (p.env deps).all (fun ib => IfaceName.validB ib.1 && Interface.validB ib.2) &&
  p.worlds.all (fun nw => nw.2.imports.all WorldItem.validB && nw.2.exports.all WorldItem.validB)

def labelsUniqueB : Binary.TyDefKind → Bool
  | .record fs => decide (fs.map (·.name)).Nodup
  | .variant cs => decide (cs.map (·.name)).Nodup
  | .enum cs => decide (cs.map (·.name)).Nodup
  | .flags fs => decide (fs.map (·.name)).Nodup
  | _ => true

def Interface.namesUniqueB (b : Binary.Interface) : Bool :=
  decide (b.types.map (·.name)).Nodup && decide (b.funcs.map Binary.Func.mangled).Nodup &&
    b.types.all (fun td => labelsUniqueB td.kind)

def World.namesUniqueB (w : Binary.World) : Bool :=
  decide (w.imports.map Binary.WorldItem.key).Nodup && decide (w.exports.map Binary.WorldItem.key).Nodup &&
    w.exports.all (fun it => !it.isType) &&
    (w.imports ++ w.exports).all fun it => match it with
      | .ifaceInline _ b => Interface.namesUniqueB b
      | .type td => labelsUniqueB td.kind
      | _ => true

def Package.namesUniqueB (p : Binary.Package) : Bool :=
  decide (p.interfaces.map (·.1)).Nodup && decide (p.worlds.map (·.1)).Nodup &&
    p.interfaces.all (fun nb => Interface.namesUniqueB nb.2) &&
    p.worlds.all (fun nw => World.namesUniqueB nw.2)

/-! ## Packages -/

/-- Elaborate the package `P` of the universe of `c` (no checks). -/
def elabPackage (c : Ctx) (env : Binary.Env) (P : Package) : Except String Binary.Package := do
  let ifs ← P.ifaces.mapM fun I =>
    match elabBody c (.iface ⟨P.name, I.name⟩) I.items I.docs I.gates with
    | some b => pure (I.name, b)
    | none => throw s!"interface `{I.name}`: cyclic or undefined types"
  let ws ← P.worlds.mapM fun W => do
    let w ← elabWorld c env (c.U.worldIds.length + 1) ⟨P.name, W.name⟩
    pure (W.name, w)
  pure { name := pkgName P.name, docs := P.docs.contents, interfaces := ifs, worlds := ws }

/-- Fail with `msg` unless `b`. -/
def require (b : Bool) (msg : String) : Except String Unit := if b then pure () else throw msg

/-- The package of a universe with a given name. -/
def lookupPkg (U : Universe) (p : PackageName) : Except String Package :=
  match U.pkg? p with
  | some P => pure P
  | none => throw "unknown package"

/-- **Elaboration**: the package `p` of the universe `U` (with the features
`fs` enabled), as a resolved binary package, and the interfaces of the other
packages. Fails unless the gated universe is valid and the output satisfies
the binary validity conditions. -/
def elaborate (U : Universe) (p : PackageName) (fs : List Name := []) :
    Except String (Binary.Package × Binary.Env) := do
  let U := Universe.gate fs U
  require (check U) "invalid WIT universe"
  let c := Ctx.ofUniverse U
  let P ← lookupPkg U p
  let env ← elabEnv c
  let out ← elabPackage c env P
  let deps := env.filter (·.1.pkg != pkgName p)
  require (Package.validB out deps) "names do not survive the binary encoding"
  require (Package.namesUniqueB out) "names are not unique"
  pure (out, deps)

/-- Completeness of `elaborate`: it succeeds on every valid (gated) universe whose
package `p` has an interface or a world and whose worlds elaborate. Proved as
`elaborate_complete` (`Silmaril.Wasm.Wit.Elab.Thms`); `elaborate_error` shows that the
world hypothesis is exactly wit-parser's world errors (`WorldError`). -/
def ElaborateComplete : Prop :=
  ∀ (U : Universe) (p : PackageName) (fs : List Name) (P : Package) (env : Binary.Env),
    Valid (Universe.gate fs U) → P ∈ Universe.gate fs U → P.name = p →
    (P.ifaces ≠ [] ∨ P.worlds ≠ []) →
    elabEnv (Ctx.ofUniverse (Universe.gate fs U)) = .ok env →
    (∀ W ∈ P.worlds, ∃ w, elabWorld (Ctx.ofUniverse (Universe.gate fs U)) env
      ((Universe.gate fs U).worldIds.length + 1) ⟨p, W.name⟩ = .ok w) →
    ∃ r, elaborate U p fs = .ok r

end Elab

end Silmaril.Wasm.Wit
