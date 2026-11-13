module

public import Silmaril.Wasm.Wit.Syntax.Defs

/-!
# WAC: the surface language

The abstract syntax of WAC documents, following the grammar of `LANGUAGE.md` of
wac `5a7480c` ("WAC Grammar") and the AST of `crates/wac-parser/src/ast*.rs`.
WAC is a superset of WIT: its type statements, inline interfaces and function
types are the WIT AST of `Silmaril.Wasm.Wit.Syntax` (`Wit.Interface`, `Wit.World`,
`Wit.TypeDef`, `Wit.IfaceItem`, `Wit.Func`).

```
document  ::= package-decl statement*
package-decl ::= 'package' package-name ('targets' package-path)? ';'
statement ::= import-statement | type-statement | let-statement | export-statement
import-statement ::= 'import' id ('as' (id | string))? ':' import-type ';'
import-type      ::= package-path | func-type | inline-interface | id
let-statement    ::= 'let' id '=' expr ';'
expr             ::= primary-expr postfix-expr*
primary-expr     ::= new-expr | nested-expr | id
new-expr         ::= 'new' package-name '{' instantiation-args '}'
instantiation-args ::= instantiation-arg (',' instantiation-arg)* (',' '...'?)?
instantiation-arg  ::= id | '...' id | (id | string) ':' expr
postfix-expr     ::= '.' id | '[' string ']'
export-statement ::= 'export' expr ('...' | 'as' (id | string))? ';'
```

The trailing `...` of a `new` expression (implicit imports) is the argument
`Arg.fill`; the grammar only allows it last, and wac's resolver reports
`FillArgumentNotLast` otherwise, so the AST keeps it as an argument and the
elaborator checks its position (as wac does). Parentheses (`nested-expr`) are kept
(`Expr.paren`), as in wac's AST.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Syntax

open Silmaril.Wasm.Wit (Name Version)

/-- A package name `ns:name(:more)*(@version)?`: `name` is the text before `@`. -/
structure PkgName where
  name : String
  version : Option String := none
  deriving Repr, DecidableEq, Inhabited

/-- The key of a package (`ns:name` or `ns:name@version`), as wac's `PackageKey`
prints it. -/
def PkgName.key (p : PkgName) : String :=
  match p.version with
  | none => p.name
  | some v => p.name ++ "@" ++ v

/-- A package path `ns:name/seg(/seg)*(@version)?`: the package `pkg` (without
version), the path segments and the version. -/
structure PkgPath where
  pkg : String
  segments : List String
  version : Option String := none
  deriving Repr, DecidableEq, Inhabited

/-- The text of a package path, as written: `ns:name/a/b@1.0.0`. -/
def PkgPath.str (p : PkgPath) : String :=
  let base := p.segments.foldl (fun acc s => acc ++ "/" ++ s) p.pkg
  match p.version with
  | none => base
  | some v => base ++ "@" ++ v

/-- The type of an import. -/
inductive ImportType where
  /-- An item of a package by its path. -/
  | path (p : PkgPath)
  /-- A function type. -/
  | func (f : Wit.Func)
  /-- An inline interface. -/
  | iface (items : List Wit.IfaceItem)
  /-- The type a local name denotes (an interface, world or type declared earlier). -/
  | ident (id : Name)
  deriving Repr, DecidableEq, Inhabited

/-- `import id (as name)? : ty;` -/
structure Import where
  id : Name
  as : Option String := none
  ty : ImportType
  deriving Repr, DecidableEq, Inhabited

/-- A type statement: an interface, world or type declaration (WIT). -/
inductive TypeStmt where
  | iface (i : Wit.Interface)
  | world (w : Wit.World)
  | type (d : Wit.TypeDef)
  deriving Repr, DecidableEq, Inhabited

/-- The name of a named instantiation argument: an identifier (subject to
interface-name matching) or a string (used verbatim). -/
inductive ArgName where
  | ident (id : Name)
  | str (s : String)
  deriving Repr, DecidableEq, Inhabited

mutual
/-- Expressions. -/
inductive Expr where
  /-- A local name. -/
  | ident (id : Name)
  /-- `new pkg { args }`. -/
  | new (pkg : PkgName) (args : List Arg)
  /-- `(e)`. -/
  | paren (e : Expr)
  /-- `e.id`. -/
  | access (e : Expr) (id : Name)
  /-- `e["name"]`. -/
  | namedAccess (e : Expr) (name : String)
  deriving Repr, Inhabited

/-- Instantiation arguments. -/
inductive Arg where
  /-- `c`: an argument whose name is inferred. -/
  | inferred (id : Name)
  /-- `name: e`. -/
  | named (name : ArgName) (e : Expr)
  /-- `...c`: the exports of the instance `c`. -/
  | spread (id : Name)
  /-- `...`: import the missing arguments. -/
  | fill
  deriving Repr, Inhabited
end

/-- What an export statement does with its expression. -/
inductive ExportOpts where
  /-- `export e;`: the export name is inferred. -/
  | none
  /-- `export e...;`: every export of the instance `e`. -/
  | spread
  /-- `export e as name;` -/
  | rename (name : String)
  deriving Repr, DecidableEq, Inhabited

/-- Statements. -/
inductive Stmt where
  | «import» (i : Import)
  | type (t : TypeStmt)
  | «let» (id : Name) (e : Expr)
  | «export» (e : Expr) (opts : ExportOpts)
  deriving Repr, Inhabited

/-- A WAC document: `package name (targets path)?;` and its statements. -/
structure Document where
  pkg : PkgName
  targets : Option PkgPath := none
  stmts : List Stmt
  deriving Repr, Inhabited

end Silmaril.Wasm.Wac.Syntax
