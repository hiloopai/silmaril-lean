module

public import Init

/-!
# WAC text: abstract syntax

The abstract syntax of WAC (WebAssembly Compositions) documents, as `wac-parser`
0.12.0 (bytecodealliance/wac at `5a7480c69ae7a4dc9eb161f485cbcb8c95e372c9`, tag
`v0.12.0`, `crates/wac-parser/src/ast.rs` and `ast/*.rs`) defines it, without source
spans. Every type here is one Rust AST type (or an enum and its payload structs
merged), with the same fields in the same order, so that the JSON of
`Silmaril.Wasm.Wac.Text.Json` is `wac parse`'s JSON with the spans removed.

* Identifiers (`String`) have lost their `%` escape; strings (`ExternName.string`,
  `Postfix.namedAccess`) are the characters between the quotes (WAC strings have no
  escapes).
* `Docs`: the doc comments before an item (`///` lines and `/** … */` blocks), each
  trimmed, in order.
* `PkgName` (`ns:name@version`, the operand of `package` and `new`) and `PkgPath`
  (`ns:name/a/b@version`) keep the version as the source text; its validity as a
  semantic version is `Silmaril.Wasm.Wac.Text.semverOk`.
* The type sub-language (`Ty`, `FuncType`, declarations, interfaces, worlds) is WAC's
  own: it differs from WIT's (`Silmaril.Wasm.Wit.Syntax`) by function type aliases
  (`type f = func();`), interface exports by alias name (`f: g;`), single results only,
  and no `map`, `own`, fixed-length lists or gates.
* Compositions: `Statement.import_` (`import id (as name)? : ty;`), `Statement.let_`
  (`let id = expr;`), `Statement.export_` (`export expr (... | as name)?;`) with
  expressions `Expr` (a `Primary`: `new pkg { args }`, `( expr )` or a name; then
  postfix accesses `.id` and `["name"]`) and instantiation arguments `Arg` (inferred
  `id`, spread `...id`, named `name: expr`, fill `...`).

The grammar is the EBNF of `LANGUAGE.md` at the same revision; where the EBNF and the
parser differ, the parser is followed (for example `...` is accepted anywhere in an
argument list, and the `as` of an import accepts strings).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Text

/-- Doc comments: the comment lines before an item, trimmed. -/
abbrev Docs := List String

/-- A package name `ns:name@version` (`wac-parser`'s `PackageName`): `name` is
`ns:name` (two or more identifiers joined by `:`). -/
structure PkgName where
  name : String
  version : Option String := none
  deriving Repr, DecidableEq, Inhabited

/-- A package path `ns:name/a/b@version` (`PackagePath`): `name` is `ns:name`, `segments`
is `a/b`. -/
structure PkgPath where
  name : String
  segments : String
  version : Option String := none
  deriving Repr, DecidableEq, Inhabited

/-- Value types (`Type`). -/
inductive Ty where
  | u8 | s8 | u16 | s16 | u32 | s32 | u64 | s64 | f32 | f64 | char | bool | string
  | tuple (ts : List Ty)
  | list (t : Ty)
  | option (t : Ty)
  | result (ok : Option Ty) (err : Option Ty)
  | borrow (id : String)
  | stream (t : Option Ty)
  | future (t : Option Ty)
  | errorContext
  | ident (id : String)
  deriving Repr, Inhabited

/-- `id: ty` (`NamedType`). -/
structure NamedType where
  id : String
  ty : Ty
  deriving Repr, Inhabited

/-- The results of a function type (`ResultList`). -/
inductive ResultList where
  | empty
  | scalar (t : Ty)
  deriving Repr, Inhabited

/-- `async? func(params) (-> result)?` (`FuncType`). -/
structure FuncType where
  isAsync : Bool
  params : List NamedType
  results : ResultList
  deriving Repr, Inhabited

/-- A function type or the name of one (`FuncTypeRef`). -/
inductive FuncTypeRef where
  | func (f : FuncType)
  | ident (id : String)
  deriving Repr, Inhabited

/-- A case of a variant (`VariantCase`). -/
structure VariantCase where
  docs : Docs
  id : String
  ty : Option Ty
  deriving Repr, Inhabited

/-- A field of a record (`Field`). -/
structure Field where
  docs : Docs
  id : String
  ty : Ty
  deriving Repr, Inhabited

/-- A flag, or a case of an enum (`Flag`, `EnumCase`). -/
structure Case where
  docs : Docs
  id : String
  deriving Repr, Inhabited

/-- The right-hand side of `type id = …;` (`TypeAliasKind`). -/
inductive AliasKind where
  | func (f : FuncType)
  | type (t : Ty)
  deriving Repr, Inhabited

/-- Type declarations (`TypeDecl`, with `VariantDecl`, `RecordDecl`, `FlagsDecl`,
`EnumDecl` and `TypeAlias` as payloads). Each has docs and an identifier. -/
inductive TypeDecl where
  | variant (docs : Docs) (id : String) (cases : List VariantCase)
  | record (docs : Docs) (id : String) (fields : List Field)
  | flags (docs : Docs) (id : String) (flags : List Case)
  | enum (docs : Docs) (id : String) (cases : List Case)
  | alias (docs : Docs) (id : String) (kind : AliasKind)
  deriving Repr, Inhabited

/-- A constructor or method of a resource (`ResourceMethod`). -/
inductive ResourceMethod where
  | ctor (docs : Docs) (params : List NamedType)
  | method (docs : Docs) (id : String) (isStatic : Bool) (ty : FuncType)
  deriving Repr, Inhabited

/-- Type declarations of interfaces and worlds (`ItemTypeDecl`): resources, and the
declarations of `TypeDecl`. -/
inductive ItemTypeDecl where
  | resource (docs : Docs) (id : String) (methods : List ResourceMethod)
  | decl (d : TypeDecl)
  deriving Repr, Inhabited

/-- The path of a `use` (`UsePath`). -/
inductive UsePath where
  | package (p : PkgPath)
  | ident (id : String)
  deriving Repr, Inhabited

/-- `id (as asId)?` (`UseItem`). -/
structure UseItem where
  id : String
  asId : Option String
  deriving Repr, Inhabited

/-- `use path.{items};` (`Use`). -/
structure Use where
  docs : Docs
  path : UsePath
  items : List UseItem
  deriving Repr, Inhabited

/-- Items of interfaces (`InterfaceItem`; `export_` is `InterfaceExport`). -/
inductive InterfaceItem where
  | use (u : Use)
  | type (d : ItemTypeDecl)
  | export_ (docs : Docs) (id : String) (ty : FuncTypeRef)
  deriving Repr, Inhabited

/-- The type of a named world item (`ExternType`; `interface` is `InlineInterface`). -/
inductive ExternType where
  | ident (id : String)
  | func (f : FuncType)
  | interface (items : List InterfaceItem)
  deriving Repr, Inhabited

/-- What a world imports or exports (`WorldItemPath`; `named` is `NamedWorldItem`). -/
inductive WorldItemPath where
  | named (id : String) (ty : ExternType)
  | package (p : PkgPath)
  | ident (id : String)
  deriving Repr, Inhabited

/-- The world of an `include` (`WorldRef`). -/
inductive WorldRef where
  | ident (id : String)
  | package (p : PkgPath)
  deriving Repr, Inhabited

/-- `from as to` in `include … with { … }` (`WorldIncludeItem`). -/
structure IncludeItem where
  «from» : String
  to : String
  deriving Repr, Inhabited

/-- Items of worlds (`WorldItem`, with `WorldImport`, `WorldExport`, `WorldInclude`). -/
inductive WorldItem where
  | use (u : Use)
  | type (d : ItemTypeDecl)
  | import_ (docs : Docs) (path : WorldItemPath)
  | export_ (docs : Docs) (path : WorldItemPath)
  | include (docs : Docs) (world : WorldRef) (with_ : List IncludeItem)
  deriving Repr, Inhabited

/-- Type statements (`TypeStatement`, with `InterfaceDecl` and `WorldDecl`). -/
inductive TypeStatement where
  | interface (docs : Docs) (id : String) (items : List InterfaceItem)
  | world (docs : Docs) (id : String) (items : List WorldItem)
  | type (d : TypeDecl)
  deriving Repr, Inhabited

/-- An import or export name, or the name of a named argument: an identifier or a string
(`ExternName`, `InstantiationArgumentName`). -/
inductive ExternName where
  | ident (id : String)
  | string (s : String)
  deriving Repr, DecidableEq, Inhabited

/-- The type of an import (`ImportType`; `interface` is `InlineInterface`). -/
inductive ImportType where
  | package (p : PkgPath)
  | func (f : FuncType)
  | interface (items : List InterfaceItem)
  | ident (id : String)
  deriving Repr, Inhabited

/-- Postfix expressions: `.id` (`AccessExpr`) and `["name"]` (`NamedAccessExpr`). -/
inductive Postfix where
  | access (id : String)
  | namedAccess (s : String)
  deriving Repr, DecidableEq, Inhabited

mutual
/-- Expressions (`Expr`): a primary expression and postfix accesses. -/
inductive Expr where
  | mk (primary : Primary) (post : List Postfix)
/-- Primary expressions (`PrimaryExpr`): `new pkg { args }`, `( e )`, a name. -/
inductive Primary where
  | new (pkg : PkgName) (args : List Arg)
  | nested (e : Expr)
  | ident (id : String)
/-- Instantiation arguments (`InstantiationArgument`): `id`, `...id`, `name: e`,
`...`. -/
inductive Arg where
  | inferred (id : String)
  | spread (id : String)
  | named (name : ExternName) (e : Expr)
  | fill
end

deriving instance Repr for Expr, Primary, Arg

instance : Inhabited Expr := ⟨.mk (.ident "") []⟩

/-- Export options (`ExportOptions`): none, `...` (spread), `as name` (rename). -/
inductive ExportOptions where
  | none
  | spread
  | rename (n : ExternName)
  deriving Repr, DecidableEq, Inhabited

/-- Statements (`Statement`, with `ImportStatement`, `LetStatement`,
`ExportStatement`). -/
inductive Statement where
  | import_ (docs : Docs) (id : String) (name : Option ExternName) (ty : ImportType)
  | type (s : TypeStatement)
  | let_ (docs : Docs) (id : String) (e : Expr)
  | export_ (docs : Docs) (e : Expr) (opts : ExportOptions)
  deriving Repr, Inhabited

/-- A document (`Document` with its `PackageDirective`): docs, `package name (targets
path)?;` and statements. -/
structure Document where
  docs : Docs
  package : PkgName
  targets : Option PkgPath
  statements : List Statement
  deriving Repr, Inhabited

end Silmaril.Wasm.Wac.Text
