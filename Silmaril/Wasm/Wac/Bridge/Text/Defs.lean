module

public import Silmaril.Wasm.Wac.Text.Ast.Defs
public import Silmaril.Wasm.Wac.Syntax.Defs
public import Silmaril.Wasm.Wit.Text.Parse.Defs

/-!
# WAC bridge: from the text AST to the elaboration AST

The text front end (`Silmaril.Wasm.Wac.Text`) reads WAC into `wac-parser`'s AST
(`Text.Document`); the elaborator (`Silmaril.Wasm.Wac.Elab`) works on `Syntax.Document`,
whose type statements are WIT (`Silmaril.Wasm.Wit.Syntax`). `ofDoc` maps the first to the
second.

**Compositions** (imports, `let`, exports, expressions, arguments, package names and
paths) map totally and one to one: `ofExpr` is a bijection between `Text.Expr` and
`Syntax.Expr` with inverse `toExpr` (`ofExpr_toExpr`, `toExpr_ofExpr`, in
`Silmaril.Wasm.Wac.Bridge.Text.Thms`). A text expression is a primary expression followed
by a list of postfix accesses; a syntax expression nests them (`access (access e a) b`).

**Types** map to WIT where WIT has the construct. Rejected (`.error`), with the reason:

* function type aliases `type f = func(…);` and interface exports by alias name
  `f: g;` (WAC-only; WIT has neither);
* a named world item whose type is a name (`import x: i;` inside a world: WAC-only);
* a world item, `use` path or `include` path `ns:pkg/a/b` with more than one segment
  after the package, a package name with more than two `:`-separated parts, or a
  version that is not `major.minor.patch(-pre)?(+build)?`: WIT's `UsePath.foreign`
  cannot express them.

`use path.{a, b as c};` (in interfaces and worlds) maps to `Wit.Use` and
`include w with { a as b };` to `Wit.Include`, both resolved by the elaborator
(`Silmaril.Wasm.Wac.WitDecl`); a local path `i` is `UsePath.local i`, a package path
`ns:pkg/i@v` is `UsePath.foreign`.

`docsOk`/`okDoc` decide acceptance (`ofDoc_isOk : (ofDoc d).isOk = okDoc d`).
Doc comments are dropped (the elaborator does not read them).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm

/-- Did a computation succeed? -/
def isOk {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

/-! ## Value types and function types (total) -/

mutual
/-- A WAC value type as a WIT type. -/
def ofTy : Text.Ty → Wit.Ty
  | .u8 => .u8 | .s8 => .s8 | .u16 => .u16 | .s16 => .s16 | .u32 => .u32 | .s32 => .s32
  | .u64 => .u64 | .s64 => .s64 | .f32 => .f32 | .f64 => .f64 | .char => .char
  | .bool => .bool | .string => .string | .errorContext => .errorContext
  | .tuple ts => .tuple (ofTys ts)
  | .list t => .list (ofTy t)
  | .option t => .option (ofTy t)
  | .result a b => .result (ofTyOpt a) (ofTyOpt b)
  | .borrow r => .borrow r
  | .stream t => .stream (ofTyOpt t)
  | .future t => .future (ofTyOpt t)
  | .ident x => .named x
def ofTyOpt : Option Text.Ty → Option Wit.Ty
  | none => none
  | some t => some (ofTy t)
def ofTys : List Text.Ty → List Wit.Ty
  | [] => []
  | t :: ts => ofTy t :: ofTys ts
end

/-- Named parameters. -/
def ofParams (ps : List Text.NamedType) : List (Wit.Name × Wit.Ty) := ps.map fun p => (p.id, ofTy p.ty)

/-- A WAC function type as a WIT function type (WAC has at most one result). -/
def ofFunc (f : Text.FuncType) : Wit.Func :=
  { params := ofParams f.params
    result := match f.results with | .empty => none | .scalar t => some (ofTy t)
    async := f.isAsync }

/-! ## Declarations (partial) -/

/-- A type declaration (`type f = func(…)` is rejected). -/
def ofTypeDecl : Text.TypeDecl → Except String Wit.TypeDef
  | .variant _ id cs => .ok ⟨id, .variant (cs.map fun c => ⟨c.id, c.ty.map ofTy, {}⟩), {}, []⟩
  | .record _ id fs => .ok ⟨id, .record (fs.map fun f => ⟨f.id, ofTy f.ty, {}⟩), {}, []⟩
  | .flags _ id fs => .ok ⟨id, .flags (fs.map fun f => ⟨f.id, {}⟩), {}, []⟩
  | .enum _ id cs => .ok ⟨id, .enum (cs.map fun c => ⟨c.id, {}⟩), {}, []⟩
  | .alias _ id (.type t) => .ok ⟨id, .alias (ofTy t), {}, []⟩
  | .alias _ id (.func _) => .error s!"function type alias `{id}` (WAC-only)"

/-- Is a type declaration accepted? -/
def okTypeDecl : Text.TypeDecl → Bool
  | .alias _ _ (.func _) => false
  | _ => true

/-- A constructor or method of a resource. -/
def ofMethod : Text.ResourceMethod → Wit.ResourceFunc
  | .ctor _ ps => ⟨.ctor, { params := ofParams ps }, {}, []⟩
  | .method _ id st f => ⟨if st then .static id else .method id, ofFunc f, {}, []⟩

/-- A type declaration of an interface or a world. -/
def ofItemTypeDecl : Text.ItemTypeDecl → Except String Wit.TypeDef
  | .resource _ id ms => .ok ⟨id, .resource (ms.map ofMethod), {}, []⟩
  | .decl d => ofTypeDecl d

/-- Is an item type declaration accepted? -/
def okItemTypeDecl : Text.ItemTypeDecl → Bool
  | .resource .. => true
  | .decl d => okTypeDecl d

/-- The parts of a string separated by a character. -/
def splitChar (c : Char) (s : String) : List String :=
  (Wit.Text.splitOn c s.toList).map String.ofList

/-- A package path as a WIT foreign use path (`ns:pkg/iface@version`). -/
def ofForeign (p : Text.PkgPath) : Except String Wit.UsePath :=
  match splitChar ':' p.name, splitChar '/' p.segments with
  | [ns, n], [i] =>
    match p.version with
    | none => .ok (.foreign ⟨ns, n, none⟩ i)
    | some v => match Wit.Text.Parse.parseVer v.toList with
      | some v => .ok (.foreign ⟨ns, n, some v⟩ i)
      | none => .error s!"version `{v}` of `{p.name}`"
  | _, _ => .error s!"world item path `{p.name}/{p.segments}` (not `ns:pkg/iface`)"

/-- Is a package path a WIT foreign use path? -/
def okForeign (p : Text.PkgPath) : Bool := isOk (ofForeign p)

/-- A `use` path: a local interface, or `ns:pkg/iface@version`. -/
def ofUsePath : Text.UsePath → Except String Wit.UsePath
  | .ident id => .ok (.local id)
  | .package p => ofForeign p

/-- Is a `use` path accepted? -/
def okUsePath : Text.UsePath → Bool
  | .ident _ => true
  | .package p => okForeign p

/-- A name of a `use`: `id` or `id as asId`. -/
def ofUseItem (u : Text.UseItem) : Wit.UseName := ⟨u.id, u.asId⟩

/-- A `use` (its doc comments are dropped). -/
def ofUse (u : Text.Use) : Except String Wit.Use :=
  (ofUsePath u.path).map fun p => ⟨p, u.items.map ofUseItem, []⟩

/-- Is a `use` accepted? -/
def okUse (u : Text.Use) : Bool := okUsePath u.path

/-- The world of an `include`. -/
def ofWorldRef : Text.WorldRef → Except String Wit.UsePath
  | .ident id => .ok (.local id)
  | .package p => ofForeign p

/-- Is the world of an `include` accepted? -/
def okWorldRef : Text.WorldRef → Bool
  | .ident _ => true
  | .package p => okForeign p

/-- `include w with { a as b, … }`. -/
def ofInclude (w : Text.WorldRef) (ws : List Text.IncludeItem) : Except String Wit.Include :=
  (ofWorldRef w).map fun p => ⟨p, ws.map fun i => ⟨i.from, i.to⟩, []⟩

/-- An interface item. -/
def ofIfaceItem : Text.InterfaceItem → Except String Wit.IfaceItem
  | .use u => (ofUse u).map .use
  | .type d => (ofItemTypeDecl d).map .type
  | .export_ _ id (.func f) => .ok (.func ⟨id, ofFunc f, {}, []⟩)
  | .export_ _ id (.ident g) => .error s!"interface export `{id}: {g}` by function type name (WAC-only)"

/-- Is an interface item accepted? -/
def okIfaceItem : Text.InterfaceItem → Bool
  | .use u => okUse u
  | .type d => okItemTypeDecl d
  | .export_ _ _ (.func _) => true
  | .export_ _ _ (.ident _) => false

/-- The items of an interface. -/
def ofIfaceItems (is : List Text.InterfaceItem) : Except String (List Wit.IfaceItem) :=
  is.mapM ofIfaceItem

/-- What a world imports or exports. -/
def ofWorldPath : Text.WorldItemPath → Except String Wit.Extern
  | .named id (.func f) => .ok (.func id (ofFunc f))
  | .named id (.interface is) => (ofIfaceItems is).map (.iface id)
  | .named id (.ident t) => .error s!"world item `{id}: {t}` by type name (WAC-only)"
  | .package p => (ofForeign p).map .path
  | .ident id => .ok (.path (.local id))

/-- Is a world item path accepted? -/
def okWorldPath : Text.WorldItemPath → Bool
  | .named _ (.func _) => true
  | .named _ (.interface is) => is.all okIfaceItem
  | .named _ (.ident _) => false
  | .package p => okForeign p
  | .ident _ => true

/-- A world item. -/
def ofWorldItem : Text.WorldItem → Except String Wit.WorldItem
  | .use u => (ofUse u).map .use
  | .type d => (ofItemTypeDecl d).map .type
  | .import_ _ p => (ofWorldPath p).map fun e => .import ⟨e, {}, []⟩
  | .export_ _ p => (ofWorldPath p).map fun e => .export ⟨e, {}, []⟩
  | .include _ w ws => (ofInclude w ws).map .include

/-- Is a world item accepted? -/
def okWorldItem : Text.WorldItem → Bool
  | .use u => okUse u
  | .include _ w _ => okWorldRef w
  | .type d => okItemTypeDecl d
  | .import_ _ p | .export_ _ p => okWorldPath p

/-- A type statement. -/
def ofTypeStmt : Text.TypeStatement → Except String Syntax.TypeStmt
  | .interface _ id is => (ofIfaceItems is).map fun is => .iface ⟨id, is, {}, []⟩
  | .world _ id is => (is.mapM ofWorldItem).map fun is => .world ⟨id, is, {}, []⟩
  | .type d => (ofTypeDecl d).map .type

/-- Is a type statement accepted? -/
def okTypeStmt : Text.TypeStatement → Bool
  | .interface _ _ is => is.all okIfaceItem
  | .world _ _ is => is.all okWorldItem
  | .type d => okTypeDecl d

/-! ## Compositions (total) -/

/-- A package name. -/
def ofPkgName (p : Text.PkgName) : Syntax.PkgName := ⟨p.name, p.version⟩

/-- A package path: the segments `a/b` are split at `/`. -/
def ofPkgPath (p : Text.PkgPath) : Syntax.PkgPath := ⟨p.name, splitChar '/' p.segments, p.version⟩

/-- The text of an extern name. -/
def nameStr : Text.ExternName → String
  | .ident x => x
  | .string s => s

/-- An argument name. -/
def ofArgName : Text.ExternName → Syntax.ArgName
  | .ident x => .ident x
  | .string s => .str s

/-- Apply one postfix access. -/
def ofPostfix (e : Syntax.Expr) : Text.Postfix → Syntax.Expr
  | .access x => .access e x
  | .namedAccess n => .namedAccess e n

/-- Apply the postfix accesses, left to right. -/
def ofPostfixes (e : Syntax.Expr) : List Text.Postfix → Syntax.Expr
  | [] => e
  | p :: ps => ofPostfixes (ofPostfix e p) ps

mutual
/-- An expression. -/
def ofExpr : Text.Expr → Syntax.Expr
  | .mk p ps => ofPostfixes (ofPrimary p) ps
/-- A primary expression. -/
def ofPrimary : Text.Primary → Syntax.Expr
  | .new p as => .new (ofPkgName p) (ofArgs as)
  | .nested e => .paren (ofExpr e)
  | .ident x => .ident x
/-- Instantiation arguments. -/
def ofArgs : List Text.Arg → List Syntax.Arg
  | [] => []
  | a :: as => ofArg a :: ofArgs as
/-- An instantiation argument. -/
def ofArg : Text.Arg → Syntax.Arg
  | .inferred x => .inferred x
  | .spread x => .spread x
  | .named n e => .named (ofArgName n) (ofExpr e)
  | .fill => .fill
end

/-! ## The inverse on compositions -/

/-- An argument name as text. -/
def toArgName : Syntax.ArgName → Text.ExternName
  | .ident x => .ident x
  | .str s => .string s

/-- Append a postfix access to a text expression. -/
def postE : Text.Expr → Text.Postfix → Text.Expr
  | .mk p ps, q => .mk p (ps ++ [q])

mutual
/-- An expression as text. -/
def toExpr : Syntax.Expr → Text.Expr
  | .ident x => .mk (.ident x) []
  | .new p as => .mk (.new ⟨p.name, p.version⟩ (toArgs as)) []
  | .paren e => .mk (.nested (toExpr e)) []
  | .access e x => postE (toExpr e) (.access x)
  | .namedAccess e n => postE (toExpr e) (.namedAccess n)
/-- Arguments as text. -/
def toArgs : List Syntax.Arg → List Text.Arg
  | [] => []
  | a :: as => toArg a :: toArgs as
/-- An argument as text. -/
def toArg : Syntax.Arg → Text.Arg
  | .inferred x => .inferred x
  | .spread x => .spread x
  | .named n e => .named (toArgName n) (toExpr e)
  | .fill => .fill
end

/-! ## Statements and documents -/

/-- An import type. -/
def ofImportType : Text.ImportType → Except String Syntax.ImportType
  | .package p => .ok (.path (ofPkgPath p))
  | .func f => .ok (.func (ofFunc f))
  | .interface is => (ofIfaceItems is).map .iface
  | .ident x => .ok (.ident x)

/-- Is an import type accepted? -/
def okImportType : Text.ImportType → Bool
  | .interface is => is.all okIfaceItem
  | _ => true

/-- Export options. -/
def ofExportOpts : Text.ExportOptions → Syntax.ExportOpts
  | .none => .none
  | .spread => .spread
  | .rename n => .rename (nameStr n)

/-- A statement. -/
def ofStmt : Text.Statement → Except String Syntax.Stmt
  | .import_ _ id n ty => (ofImportType ty).map fun ty => .import ⟨id, n.map nameStr, ty⟩
  | .type s => (ofTypeStmt s).map .type
  | .let_ _ id e => .ok (.let id (ofExpr e))
  | .export_ _ e o => .ok (.export (ofExpr e) (ofExportOpts o))

/-- Is a statement accepted? -/
def okStmt : Text.Statement → Bool
  | .import_ _ _ _ ty => okImportType ty
  | .type s => okTypeStmt s
  | _ => true

/-- **The text AST as the elaboration AST.** -/
def ofDoc (d : Text.Document) : Except String Syntax.Document :=
  (d.statements.mapM ofStmt).map fun ss =>
    { pkg := ofPkgName d.package, targets := d.targets.map ofPkgPath, stmts := ss }

/-- Is a document accepted? -/
def okDoc (d : Text.Document) : Bool := d.statements.all okStmt

end Silmaril.Wasm.Wac.Bridge
