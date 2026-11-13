module

public import Silmaril.Wasm.Wac.Bridge.Text.Defs
public import Silmaril.Wasm.Wac.FuncAlias.Defs

/-!
# WAC bridge: the text AST to the elaboration AST with function type names

`ofDocX` maps the text AST (`Text.Document`) to the elaboration AST with WAC's function
type names (`FuncAlias.Document`, `Silmaril.Wasm.Wac.FuncAlias`). It is `ofDoc` of
`Silmaril.Wasm.Wac.Bridge.Text` (`ofDocX_ofDoc`) extended by the items WIT cannot express:

* `type f = func(…);` (top level, interfaces, worlds): `funcType f (ofFunc …)`;
* `x: f;` in an interface: `IItem.funcRef x f`;
* `import x: t;` / `export x: t;` in a world: `WExtern.ref x t`;
* interfaces, worlds and inline interfaces take the `FuncAlias` forms (`Stmt.iface`,
  `Stmt.world`, `WExtern.iface`, `Stmt.importIface`), whose items may be any of these.

What is still rejected (`okDocX`, `ofDocX_isOk`) are only the paths WIT's
`UsePath.foreign` cannot express: a world item, `use` or `include` path `ns:pkg/a/b`
with more than one segment after the package, a package name with more than two
`:`-separated parts, or a version that is not a semantic version.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm

/-! ## Type declarations -/

/-- A type declaration: a WIT type definition (`inl`) or a function type name with its
function type (`inr`). -/
def ofTypeDeclX : Text.TypeDecl → Wit.TypeDef ⊕ (Wit.Name × Wit.Func)
  | .variant _ id cs => .inl ⟨id, .variant (cs.map fun c => ⟨c.id, c.ty.map ofTy, {}⟩), {}, []⟩
  | .record _ id fs => .inl ⟨id, .record (fs.map fun f => ⟨f.id, ofTy f.ty, {}⟩), {}, []⟩
  | .flags _ id fs => .inl ⟨id, .flags (fs.map fun f => ⟨f.id, {}⟩), {}, []⟩
  | .enum _ id cs => .inl ⟨id, .enum (cs.map fun c => ⟨c.id, {}⟩), {}, []⟩
  | .alias _ id (.type t) => .inl ⟨id, .alias (ofTy t), {}, []⟩
  | .alias _ id (.func f) => .inr (id, ofFunc f)

/-- A type declaration of an interface or a world. -/
def ofItemTypeDeclX : Text.ItemTypeDecl → Wit.TypeDef ⊕ (Wit.Name × Wit.Func)
  | .resource _ id ms => .inl ⟨id, .resource (ms.map ofMethod), {}, []⟩
  | .decl d => ofTypeDeclX d

/-! ## Interfaces -/

/-- An interface item with function type names. -/
def ofIfaceItemX : Text.InterfaceItem → Except String FuncAlias.IItem
  | .use u => (ofUse u).map fun u => .wit (.use u)
  | .type d => .ok (match ofItemTypeDeclX d with
    | .inl t => .wit (.type t)
    | .inr (n, f) => .funcType n f)
  | .export_ _ id (.func f) => .ok (.wit (.func ⟨id, ofFunc f, {}, []⟩))
  | .export_ _ id (.ident g) => .ok (.funcRef id g)

/-- Is an interface item accepted? -/
def okIfaceItemX : Text.InterfaceItem → Bool
  | .use u => okUse u
  | _ => true

/-- The items of an interface. -/
def ofIfaceItemsX (is : List Text.InterfaceItem) : Except String (List FuncAlias.IItem) :=
  is.mapM ofIfaceItemX

/-! ## Worlds -/

/-- A WIT world import (`imp`) or export. -/
def witExtern (imp : Bool) (e : Wit.Extern) : Wit.WorldItem :=
  if imp then .import ⟨e, {}, []⟩ else .export ⟨e, {}, []⟩

/-- A world import (`imp`) or export of `WExtern`. -/
def xExtern (imp : Bool) (e : FuncAlias.WExtern) : FuncAlias.WItem :=
  if imp then .import e else .export e

/-- What a world imports (`imp`) or exports. -/
def ofWorldPathX (imp : Bool) : Text.WorldItemPath → Except String FuncAlias.WItem
  | .named id (.func f) => .ok (.wit (witExtern imp (.func id (ofFunc f))))
  | .named id (.interface is) => (ofIfaceItemsX is).map fun is => xExtern imp (.iface id is)
  | .named id (.ident t) => .ok (xExtern imp (.ref id t))
  | .package p => (ofForeign p).map fun p => .wit (witExtern imp (.path p))
  | .ident id => .ok (.wit (witExtern imp (.path (.local id))))

/-- Is a world item path accepted? -/
def okWorldPathX : Text.WorldItemPath → Bool
  | .named _ (.interface is) => is.all okIfaceItemX
  | .package p => okForeign p
  | _ => true

/-- A world item with function type names. -/
def ofWorldItemX : Text.WorldItem → Except String FuncAlias.WItem
  | .use u => (ofUse u).map fun u => .wit (.use u)
  | .type d => .ok (match ofItemTypeDeclX d with
    | .inl t => .wit (.type t)
    | .inr (n, f) => .funcType n f)
  | .import_ _ p => ofWorldPathX true p
  | .export_ _ p => ofWorldPathX false p
  | .include _ w ws => (ofInclude w ws).map fun i => .wit (.include i)

/-- Is a world item accepted? -/
def okWorldItemX : Text.WorldItem → Bool
  | .use u => okUse u
  | .type _ => true
  | .import_ _ p | .export_ _ p => okWorldPathX p
  | .include _ w _ => okWorldRef w

/-! ## Statements and documents -/

/-- A type statement. -/
def ofTypeStmtX : Text.TypeStatement → Except String FuncAlias.Stmt
  | .interface _ id is => (ofIfaceItemsX is).map (.iface id)
  | .world _ id is => (is.mapM ofWorldItemX).map (.world id)
  | .type d => .ok (match ofTypeDeclX d with
    | .inl t => .wit (.type (.type t))
    | .inr (n, f) => .funcType n f)

/-- Is a type statement accepted? -/
def okTypeStmtX : Text.TypeStatement → Bool
  | .interface _ _ is => is.all okIfaceItemX
  | .world _ _ is => is.all okWorldItemX
  | .type _ => true

/-- A statement. -/
def ofStmtX : Text.Statement → Except String FuncAlias.Stmt
  | .import_ _ id n (.interface is) => (ofIfaceItemsX is).map (.importIface id (n.map nameStr))
  | .import_ _ id n (.package p) => .ok (.wit (.import ⟨id, n.map nameStr, .path (ofPkgPath p)⟩))
  | .import_ _ id n (.func f) => .ok (.wit (.import ⟨id, n.map nameStr, .func (ofFunc f)⟩))
  | .import_ _ id n (.ident x) => .ok (.wit (.import ⟨id, n.map nameStr, .ident x⟩))
  | .type s => ofTypeStmtX s
  | .let_ _ id e => .ok (.wit (.let id (ofExpr e)))
  | .export_ _ e o => .ok (.wit (.export (ofExpr e) (ofExportOpts o)))

/-- Is a statement accepted? -/
def okStmtX : Text.Statement → Bool
  | .import_ _ _ _ (.interface is) => is.all okIfaceItemX
  | .type s => okTypeStmtX s
  | _ => true

/-- **The text AST as the elaboration AST with function type names.** -/
def ofDocX (d : Text.Document) : Except String FuncAlias.Document :=
  (d.statements.mapM ofStmtX).map fun ss =>
    { pkg := ofPkgName d.package, targets := d.targets.map ofPkgPath, stmts := ss }

/-- Is a document accepted? -/
def okDocX (d : Text.Document) : Bool := d.statements.all okStmtX

end Silmaril.Wasm.Wac.Bridge
