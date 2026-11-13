module

public import Silmaril.Wasm.Wac.Elab.Defs
public import Silmaril.Wasm.Wac.Alias.Defs

/-!
# WAC: function type names (`type f = func(…)`, `x: f`)

WAC's type language extends WIT's with **function type names** (wac `5a7480c`,
`crates/wac-parser/src/resolution.rs`): a type alias may name a function type
(`type f = func(…);`, `type_alias` with `TypeAliasKind::Func`), an alias of such a name
is again one (`type g = f;`), an interface may export a function by such a name
(`x: f;`, `func_type_ref`), and a world may import or export an item typed by a name
(`import x: t;`, `world_item_path` with `ExternType::Ident`), where `t` is a function
type name or an interface (of the world's scope, then of the document). WIT has none
of these (`Wit.TypeDefKind` has no function types), so the elaboration AST
(`Syntax.Document`, over `Wit.Syntax`) cannot express them.

This module extends the elaboration AST **additively**: each layer is the WIT one
(`.wit`) or one of the new items, and the elaborator here handles the new items and
hands every WIT item to the elaborator of `Silmaril.Wasm.Wac.WitDecl` /
`Silmaril.Wasm.Wac.Elab`, one item (statement) at a time.

* `IItem`: interface items, `WExtern`/`WItem`: world items, `Stmt`, `Document`.
* A function type name `f` denotes the elaborated signature `s` (in the scope of its
  declaration); its declaration adds the item `(f, type (func s))` (an interface
  export, a world import, or a top-level type definition exported by the composition,
  as wac's `define_type`), and `x: f` the function `(x, func s)`. In a world,
  `import x: i` with `i` a document interface imports the instance of `i` (with its
  interface id), with `i` a function type name the function.
* `import b: f;` at the top level, with `f` a top-level function type name, imports the
  function `b` (wac's `ItemKind::promote` turns `Type(Func)` into `Func`; the WIT-only
  elaborator's `Kind.promote` does not, and imports a type there).

**Conservativity** (`Silmaril.Wasm.Wac.FuncAlias.Thms`): on the embedding `ofDoc` of a
`Syntax.Document`, `elabDoc` is the elaborator of `Silmaril.Wasm.Wac.Elab`
(`elabDoc_ofDoc`, `elabDocA_ofDoc`), so its soundness and completeness results apply
there. The new cases have no relational specification of their own.

**Restrictions.** A function type name used as a value type (a parameter `p: f`) is a
reference `ref f`, not an error (wac: `UndefinedName`/not a value type); a function
type name declared twice is `duplicateName`; a type name equal to a function type name
is `duplicateName` only when the function type name comes first.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.FuncAlias

open Silmaril.Wasm.Wit.Binary (Ty Sig)
open WitDecl (Scope Look WSt)

/-! ## Syntax -/

/-- An interface item: a WIT item, or one of WAC's function type items. -/
inductive IItem where
  | wit (i : Wit.IfaceItem)
  /-- `type name = func(…);` -/
  | funcType (name : Wit.Name) (f : Wit.Func)
  /-- `name: ty;` with `ty` a function type name. -/
  | funcRef (name : Wit.Name) (ty : Wit.Name)
  deriving Repr, DecidableEq, Inhabited

/-- A world import or export that WIT cannot express. -/
inductive WExtern where
  /-- `name: interface { items }` with WAC items. -/
  | iface (name : Wit.Name) (items : List IItem)
  /-- `name: ty;` with `ty` a function type name or an interface. -/
  | ref (name : Wit.Name) (ty : Wit.Name)
  deriving Repr, DecidableEq, Inhabited

/-- A world item. -/
inductive WItem where
  | wit (i : Wit.WorldItem)
  | «import» (e : WExtern)
  | «export» (e : WExtern)
  /-- `type name = func(…);` -/
  | funcType (name : Wit.Name) (f : Wit.Func)
  deriving Repr, DecidableEq, Inhabited

/-- A statement. -/
inductive Stmt where
  | wit (s : Syntax.Stmt)
  /-- `interface name { items }` -/
  | iface (name : Wit.Name) (items : List IItem)
  /-- `world name { items }` -/
  | world (name : Wit.Name) (items : List WItem)
  /-- `type name = func(…);` -/
  | funcType (name : Wit.Name) (f : Wit.Func)
  /-- `import id (as name)?: interface { items };` -/
  | importIface (id : Wit.Name) (as : Option String) (items : List IItem)
  deriving Repr, Inhabited

/-- A document. -/
structure Document where
  pkg : Syntax.PkgName
  targets : Option Syntax.PkgPath := none
  stmts : List Stmt
  deriving Repr, Inhabited

/-! ## Interfaces -/

/-- The function type names in scope, with their signatures. -/
abbrev FScope := List (String × Sig)

/-- The signature `type g = f` aliases, when `f` is a function type name. -/
def aliasOf (fs : FScope) (d : Wit.TypeDef) : Option Sig :=
  match d.kind with
  | .alias (.named f) => fs.lookup f
  | _ => none

/-- An interface body under construction: type scope, function type names, exports. -/
abbrev ISt := Scope × FScope × Externs

/-- Declare a function type name, once. -/
def declFunc (sc : Scope) (fs : FScope) (xs : Externs) (n : String) (s : Sig) : Except ElabError ISt :=
  if (sc.lookup n).isSome ∨ (fs.lookup n).isSome then .error (.duplicateName n)
  else .ok (sc, fs ++ [(n, s)], xs ++ [(n, .type (.func s))])

/-- One WIT item, by the WIT elaborator. -/
def witItem (L : Look) (sc : Scope) (fs : FScope) (xs : Externs) (it : Wit.IfaceItem) :
    Except ElabError ISt := do
  let (sc, xs) ← WitDecl.ifaceItems L (sc, xs) [it]
  pure (sc, fs, xs)

/-- One interface item. -/
def ifaceItem (L : Look) : ISt → IItem → Except ElabError ISt
  | (sc, fs, xs), .wit (.type d) =>
    match aliasOf fs d with
    | some s => declFunc sc fs xs d.name s
    | none =>
      if (fs.lookup d.name).isSome then .error (.duplicateName d.name)
      else witItem L sc fs xs (.type d)
  | (sc, fs, xs), .wit (.use u) => witItem L sc fs xs (.use u)
  | (sc, fs, xs), .wit (.func f) => witItem L sc fs xs (.func f)
  | (sc, fs, xs), .funcType n f => declFunc sc fs xs n (WitDecl.elabSig sc f)
  | (sc, fs, xs), .funcRef n t =>
    match fs.lookup t with
    | none => .error (.notFuncType t)
    | some s =>
      if n ∈ xs.map (·.1) then .error (.duplicateInterfaceExport n)
      else .ok (sc, fs, xs ++ [(n, .func s)])

/-- The items of an interface body, in order. -/
def ifaceItems (L : Look) : ISt → List IItem → Except ElabError ISt
  | acc, [] => .ok acc
  | acc, it :: rest => do
    let acc ← ifaceItem L acc it
    ifaceItems L acc rest

/-- The exports of an interface body. -/
def ifaceExports (L : Look) (items : List IItem) : Except ElabError Externs := do
  let (_, _, xs) ← ifaceItems L ([], [], []) items
  pure xs

/-! ## Worlds -/

/-- A world under construction, with its function type names. -/
structure XW where
  w : WSt := {}
  fs : FScope := []
  deriving Inhabited

/-- The kinds of the names of the document (wac's root scope). -/
abbrev Root := String → Option Kind

/-- `name: t` in a world: a function type name of the world, else a function type or
an interface of the document (`local_or_root_item`). -/
def externRef (root : Root) (sc : Scope) (fs : FScope) (n t : String) : Except ElabError (String × Kind) :=
  if (sc.lookup t).isSome then .error (.notFuncOrInterface t) else
  match fs.lookup t with
  | some s => .ok (n, .func s)
  | none =>
    match root t with
    | some (.type (.func s)) => .ok (n, .func s)
    | some (.type (.inst id es)) => .ok (n, .inst id es)
    | some _ => .error (.notFuncOrInterface t)
    | none => .error (.undefinedName t)

/-- A world import or export of `WExtern`, named. -/
def externOf (L : Look) (root : Root) (sc : Scope) (fs : FScope) : WExtern → Except ElabError (String × Kind)
  | .iface n items => do pure (n, .inst none (← ifaceExports L items))
  | .ref n t => externRef root sc fs n t

/-- Declare a function type name in a world (an import of the type). -/
def declWorldFunc (w : WSt) (fs : FScope) (n : String) (s : Sig) : Except ElabError XW :=
  if (w.sc.lookup n).isSome ∨ (fs.lookup n).isSome then .error (.duplicateName n)
  else .ok ⟨{ w with imports := w.imports ++ [(n, .type (.func s))] }, fs ++ [(n, s)]⟩

/-- One WIT world item, by the WIT elaborator. -/
def witWorldItem (L : Look) (w : WSt) (fs : FScope) (it : Wit.WorldItem) : Except ElabError XW := do
  let w ← WitDecl.worldItems L w [it]
  pure ⟨w, fs⟩

/-- One world item (includes are kept for later, as by `WitDecl.worldItems`). -/
def worldItem (L : Look) (root : Root) : XW → WItem → Except ElabError XW
  | ⟨w, fs⟩, .wit (.type d) =>
    match aliasOf fs d with
    | some s => declWorldFunc w fs d.name s
    | none =>
      if (fs.lookup d.name).isSome then .error (.duplicateName d.name)
      else witWorldItem L w fs (.type d)
  | ⟨w, fs⟩, .wit (.import e) => witWorldItem L w fs (.import e)
  | ⟨w, fs⟩, .wit (.export e) => witWorldItem L w fs (.export e)
  | ⟨w, fs⟩, .wit (.use u) => witWorldItem L w fs (.use u)
  | ⟨w, fs⟩, .wit (.include i) => witWorldItem L w fs (.include i)
  | ⟨w, fs⟩, .funcType n f => declWorldFunc w fs n (WitDecl.elabSig w.sc f)
  | ⟨w, fs⟩, .import e => do
    let (n, k) ← externOf L root w.sc fs e
    if n ∈ w.imports.map (·.1) then .error (.duplicateWorldItem n)
    else .ok ⟨{ w with imports := w.imports ++ [(n, k)] }, fs⟩
  | ⟨w, fs⟩, .export e => do
    let (n, k) ← externOf L root w.sc fs e
    if n ∈ w.exports.map (·.1) then .error (.duplicateWorldItem n)
    else .ok ⟨{ w with exports := w.exports ++ [(n, k)] }, fs⟩

/-- The items of a world, in order. -/
def worldItems (L : Look) (root : Root) : XW → List WItem → Except ElabError XW
  | x, [] => .ok x
  | x, it :: rest => do
    let x ← worldItem L root x it
    worldItems L root x rest

/-- **The imports and exports of a world body** (as `WitDecl.worldKind`). -/
def worldKind (L : Look) (root : Root) (items : List WItem) : Except ElabError (Externs × Externs) := do
  let x ← worldItems L root {} items
  let w ← WitDecl.includeWorlds L x.w x.w.includes
  let imp ← WitDecl.implicitIfaces L w.imports [] w.allUsed
  pure (imp ++ w.imports, w.exports)

/-! ## Statements and documents -/

/-- The elaboration state, with the top-level function type names. -/
structure XSt where
  st : ESt := {}
  fs : FScope := []
  deriving Inhabited

/-- The kinds of the top-level names. -/
def rootOf (st : ESt) : Root := fun t => (st.scope.lookup t).map st.g.kindOf

/-- Define a type `n` of kind `k`, exported (the `type` statement of `Wac.elabStmt`). -/
def define (st : ESt) (n : String) (k : Kind) : Except ElabError ESt :=
  if st.g.hasExport n then .error (.declarationConflict n) else
  let (st, j) := st.add ⟨.defn n, k⟩
  let st := { st with g := { st.g with exports := st.g.exports ++ [(n, j)] } }
  st.bind n j

/-- Import `k` as `n`, bound to `id` (the `import` statement of `Wac.elabStmt`). -/
def importAs (st : ESt) (id n : String) (k : Kind) : Except ElabError ESt :=
  if n ∈ st.g.importNames then .error (.duplicateImport n) else
  let (st, j) := st.add ⟨.imp n, k.promote⟩
  st.bind id j

/-- A WIT statement, by `Wac.elabStmt`. -/
def witStmt (cx : ECtx) (st : ESt) (fs : FScope) (s : Syntax.Stmt) : Except ElabError XSt := do
  pure ⟨← Wac.elabStmt cx st s, fs⟩

/-- Elaborate a statement. -/
def elabStmt (cx : ECtx) : XSt → Stmt → Except ElabError XSt
  | ⟨st, fs⟩, .wit (.type (.type d)) =>
    match aliasOf fs d with
    | some s => do pure ⟨← define st d.name (.type (.func s)), fs ++ [(d.name, s)]⟩
    | none => witStmt cx st fs (.type (.type d))
  | ⟨st, fs⟩, .wit (.type (.iface i)) => witStmt cx st fs (.type (.iface i))
  | ⟨st, fs⟩, .wit (.type (.world w)) => witStmt cx st fs (.type (.world w))
  | ⟨st, fs⟩, .wit (.import ⟨id, as, .ident x⟩) =>
    match fs.lookup x with
    | some s => do pure ⟨← importAs st id (as.getD id) (.func s), fs⟩
    | none => witStmt cx st fs (.import ⟨id, as, .ident x⟩)
  | ⟨st, fs⟩, .wit (.import ⟨id, as, .path p⟩) => witStmt cx st fs (.import ⟨id, as, .path p⟩)
  | ⟨st, fs⟩, .wit (.import ⟨id, as, .func f⟩) => witStmt cx st fs (.import ⟨id, as, .func f⟩)
  | ⟨st, fs⟩, .wit (.import ⟨id, as, .iface is⟩) => witStmt cx st fs (.import ⟨id, as, .iface is⟩)
  | ⟨st, fs⟩, .wit (.let x e) => witStmt cx st fs (.let x e)
  | ⟨st, fs⟩, .wit (.export e o) => witStmt cx st fs (.export e o)
  | ⟨st, fs⟩, .iface n items => do
    let es ← ifaceExports (cx.look st) items
    pure ⟨← define st n (.type (.inst (some (cx.declId n)) es)), fs⟩
  | ⟨st, fs⟩, .world n items => do
    let (is, es) ← worldKind (cx.look st) (rootOf st) items
    pure ⟨← define st n (.type (.comp (some (cx.declId n)) is es)), fs⟩
  | ⟨st, fs⟩, .funcType n f => do
    let s := WitDecl.elabSig (rootScope st) f
    pure ⟨← define st n (.type (.func s)), fs ++ [(n, s)]⟩
  | ⟨st, fs⟩, .importIface id as items => do
    let es ← ifaceExports (cx.look st) items
    pure ⟨← importAs st id (as.getD id) (.inst none es), fs⟩

/-- Elaborate the statements in order. -/
def elabStmts (cx : ECtx) : XSt → List Stmt → Except ElabError XSt
  | x, [] => .ok x
  | x, s :: ss => do let x ← elabStmt cx x s; elabStmts cx x ss

/-- **Elaborate a document** (as `Wac.elabDoc`): the statements, then implicit imports,
then `targets`. -/
def elabDoc (env : PkgEnv) (d : Document) : Except ElabError CGraph := do
  let cx : ECtx := ⟨env, d.pkg⟩
  let x ← elabStmts cx {} d.stmts
  let g ← Implicit.resolve x.st.g
  checkTargets cx x.st g d.targets
  pure g

/-- Elaboration up to aliases (as `elabDocA`): against the registry with its aliases
expanded. -/
def elabDocA (env : PkgEnv) (d : Document) : Except ElabError CGraph := elabDoc env.expand d

/-! ## The embedding of the WIT-only AST -/

/-- A world item of `Syntax`: inline interfaces become `WExtern.iface`. -/
def ofWorldItem : Wit.WorldItem → WItem
  | .import ⟨.iface n is, _, _⟩ => .import (.iface n (is.map .wit))
  | .export ⟨.iface n is, _, _⟩ => .export (.iface n (is.map .wit))
  | it => .wit it

/-- A statement of `Syntax`: interfaces, worlds and inline interface imports take the
forms of this AST (as `Bridge.ofDocX` produces them), the others are `.wit`. -/
def ofStmt : Syntax.Stmt → Stmt
  | .type (.iface i) => .iface i.name (i.items.map .wit)
  | .type (.world w) => .world w.name (w.items.map ofWorldItem)
  | .import ⟨id, as, .iface is⟩ => .importIface id as (is.map .wit)
  | s => .wit s

/-- A document of `Syntax`. -/
def ofDoc (d : Syntax.Document) : Document := ⟨d.pkg, d.targets, d.stmts.map ofStmt⟩

/-! ## Forgetting the function type items -/

/-- The WIT items of an interface body. -/
def witItems (is : List IItem) : List Wit.IfaceItem :=
  is.filterMap fun | .wit i => some i | _ => none

/-- A world item without its function type items (`none`: a function type item). -/
def WItem.forget : WItem → Option Wit.WorldItem
  | .wit i => some i
  | .import (.iface n is) => some (.import ⟨.iface n (witItems is), {}, []⟩)
  | .export (.iface n is) => some (.export ⟨.iface n (witItems is), {}, []⟩)
  | _ => none

/-- A statement without its function type items. -/
def Stmt.forget : Stmt → Option Syntax.Stmt
  | .wit s => some s
  | .iface n is => some (.type (.iface ⟨n, witItems is, {}, []⟩))
  | .world n is => some (.type (.world ⟨n, is.filterMap WItem.forget, {}, []⟩))
  | .funcType .. => none
  | .importIface id as is => some (.import ⟨id, as, .iface (witItems is)⟩)

/-- A document without its function type items: the WIT declarations that remain
(the tool reads package names and nominal type definitions from it). -/
def Document.forget (d : Document) : Syntax.Document :=
  ⟨d.pkg, d.targets, d.stmts.filterMap Stmt.forget⟩

end Silmaril.Wasm.Wac.FuncAlias
