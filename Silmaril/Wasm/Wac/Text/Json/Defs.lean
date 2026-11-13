module

public import Silmaril.Wasm.Wac.Text.Ast.Defs

/-!
# WAC text: the JSON of `wac parse`

`wac parse FILE` (wac-cli 0.12.0) prints the `wac-parser` AST with `serde_json`. This
module writes the same JSON for `Silmaril.Wasm.Wac.Text.Document`, with source spans
removed: a `span` field is left out, and a span that is a tuple component or the whole
payload of a variant (`{"u8": {"offset": …, "length": …}}`, `["fill", …]`) is `null`.
`tests/wasm-wac/differential.sh` compares it with `wac parse` after the same
normalisation (`tests/wasm-wac/strip-spans.jq`), with sorted keys.

The encoding follows serde's defaults with the `rename_all = "camelCase"` attributes of
`wac-parser`: structs are objects, unit variants strings (`"empty"`, `"none"`), newtype
variants `{"tag": payload}`, tuple variants `{"tag": [..]}`, struct variants
`{"tag": {..}}`; `Statement` keeps its variant names (`"Import"`, `"Let"`, …); a missing
`targets` is omitted; `semver::Version` is its string.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Text

/-- JSON values. -/
inductive J where
  | null
  | bool (b : Bool)
  | str (s : String)
  | arr (xs : List J)
  | obj (fs : List (String × J))
  deriving Repr, Inhabited

namespace J

/-- Hex digit. -/
def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

/-- A JSON string literal. -/
def quote (s : String) : String :=
  let esc : Char → List Char := fun c =>
    if c = '"' then ['\\', '"'] else if c = '\\' then ['\\', '\\']
    else if c = '\n' then ['\\', 'n'] else if c = '\t' then ['\\', 't']
    else if c = '\r' then ['\\', 'r']
    else if c.toNat < 0x20 then
      ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
    else [c]
  String.ofList ('"' :: s.toList.flatMap esc ++ ['"'])

/-- Compact rendering. -/
partial def render : J → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .str s => quote s
  | .arr xs => "[" ++ ",".intercalate (xs.map render) ++ "]"
  | .obj fs => "{" ++ ",".intercalate (fs.map fun (k, v) => quote k ++ ":" ++ render v) ++ "}"

end J

namespace Json

open J

/-- `{"tag": v}`. -/
def tag (t : String) (v : J) : J := .obj [(t, v)]
/-- An `Ident` (`{"string": …}`). -/
def id (s : String) : J := .obj [("string", .str s)]
/-- Doc comments. -/
def docs (ds : Docs) : J := .arr (ds.map fun d => .obj [("comment", .str d)])
/-- An optional value. -/
def opt {α : Type} (f : α → J) : Option α → J
  | some a => f a
  | none => .null
/-- A version (or `null`). -/
def ver (v : Option String) : J := opt J.str v

/-- A `PackageName`. -/
def pkgName (p : PkgName) : J :=
  .obj [("string", .str (p.name ++ (match p.version with | some v => "@" ++ v | none => ""))),
        ("name", .str p.name), ("version", ver p.version)]

/-- A `PackagePath`. -/
def pkgPath (p : PkgPath) : J :=
  .obj [("string", .str (p.name ++ "/" ++ p.segments ++
          (match p.version with | some v => "@" ++ v | none => ""))),
        ("name", .str p.name), ("segments", .str p.segments), ("version", ver p.version)]

/-- A `Type`. -/
partial def ty : Ty → J
  | .u8 => tag "u8" .null | .s8 => tag "s8" .null | .u16 => tag "u16" .null
  | .s16 => tag "s16" .null | .u32 => tag "u32" .null | .s32 => tag "s32" .null
  | .u64 => tag "u64" .null | .s64 => tag "s64" .null | .f32 => tag "f32" .null
  | .f64 => tag "f64" .null | .char => tag "char" .null | .bool => tag "bool" .null
  | .string => tag "string" .null
  | .tuple ts => tag "tuple" (.arr [.arr (ts.map ty), .null])
  | .list t => tag "list" (.arr [ty t, .null])
  | .option t => tag "option" (.arr [ty t, .null])
  | .result o e => tag "result" (.obj [("ok", opt ty o), ("err", opt ty e)])
  | .borrow i => tag "borrow" (.arr [id i, .null])
  | .stream t => tag "stream" (.arr [opt ty t, .null])
  | .future t => tag "future" (.arr [opt ty t, .null])
  | .errorContext => tag "errorContext" .null
  | .ident i => tag "ident" (id i)

/-- A `NamedType`. -/
def namedType (n : NamedType) : J := .obj [("id", id n.id), ("ty", ty n.ty)]

/-- A `FuncType`. -/
def funcType (f : FuncType) : J :=
  .obj [("isAsync", .bool f.isAsync), ("params", .arr (f.params.map namedType)),
        ("results", match f.results with | .empty => .str "empty" | .scalar t => tag "scalar" (ty t))]

/-- A `FuncTypeRef`. -/
def funcTypeRef : FuncTypeRef → J
  | .func f => tag "func" (funcType f)
  | .ident i => tag "ident" (id i)

/-- A `TypeDecl` (the payload of a `TypeDecl` or `ItemTypeDecl` variant). -/
def typeDecl : TypeDecl → J
  | .variant ds i cs => tag "variant" (.obj [("docs", docs ds), ("id", id i),
      ("cases", .arr (cs.map fun c => .obj [("docs", docs c.docs), ("id", id c.id), ("ty", opt ty c.ty)]))])
  | .record ds i fs => tag "record" (.obj [("docs", docs ds), ("id", id i),
      ("fields", .arr (fs.map fun f => .obj [("docs", docs f.docs), ("id", id f.id), ("ty", ty f.ty)]))])
  | .flags ds i fs => tag "flags" (.obj [("docs", docs ds), ("id", id i),
      ("flags", .arr (fs.map fun f => .obj [("docs", docs f.docs), ("id", id f.id)]))])
  | .enum ds i cs => tag "enum" (.obj [("docs", docs ds), ("id", id i),
      ("cases", .arr (cs.map fun c => .obj [("docs", docs c.docs), ("id", id c.id)]))])
  | .alias ds i k => tag "alias" (.obj [("docs", docs ds), ("id", id i),
      ("kind", match k with | .func f => tag "func" (funcType f) | .type t => tag "type" (ty t))])

/-- A `ResourceMethod`. -/
def resourceMethod : ResourceMethod → J
  | .ctor ds ps => tag "constructor" (.obj [("docs", docs ds), ("params", .arr (ps.map namedType))])
  | .method ds i st f => tag "method" (.obj [("docs", docs ds), ("id", id i),
      ("isStatic", .bool st), ("ty", funcType f)])

/-- An `ItemTypeDecl`. -/
def itemTypeDecl : ItemTypeDecl → J
  | .resource ds i ms => tag "resource" (.obj [("docs", docs ds), ("id", id i),
      ("methods", .arr (ms.map resourceMethod))])
  | .decl d => typeDecl d

/-- A `Use`. -/
def use (u : Use) : J :=
  .obj [("docs", docs u.docs),
        ("path", match u.path with | .package p => tag "package" (pkgPath p) | .ident i => tag "ident" (id i)),
        ("items", .arr (u.items.map fun i => .obj [("id", id i.id), ("asId", opt id i.asId)]))]

/-- An `InterfaceItem`. -/
def interfaceItem : InterfaceItem → J
  | .use u => tag "use" (use u)
  | .type d => tag "type" (itemTypeDecl d)
  | .export_ ds i f => tag "export" (.obj [("docs", docs ds), ("id", id i), ("ty", funcTypeRef f)])

/-- An `InlineInterface`. -/
def inlineInterface (items : List InterfaceItem) : J :=
  .obj [("items", .arr (items.map interfaceItem))]

/-- A `WorldItemPath`. -/
def worldItemPath : WorldItemPath → J
  | .named i t => tag "named" (.obj [("id", id i), ("ty", match t with
      | .ident x => tag "ident" (id x)
      | .func f => tag "func" (funcType f)
      | .interface items => tag "interface" (inlineInterface items))])
  | .package p => tag "package" (pkgPath p)
  | .ident i => tag "ident" (id i)

/-- A `WorldItem`. -/
def worldItem : WorldItem → J
  | .use u => tag "use" (use u)
  | .type d => tag "type" (itemTypeDecl d)
  | .import_ ds p => tag "import" (.obj [("docs", docs ds), ("path", worldItemPath p)])
  | .export_ ds p => tag "export" (.obj [("docs", docs ds), ("path", worldItemPath p)])
  | .include ds w ws => tag "include" (.obj [("docs", docs ds),
      ("world", match w with | .ident i => tag "ident" (id i) | .package p => tag "package" (pkgPath p)),
      ("with", .arr (ws.map fun i => .obj [("from", id i.from), ("to", id i.to)]))])

/-- A `TypeStatement`. -/
def typeStatement : TypeStatement → J
  | .interface ds i items => tag "interface" (.obj [("docs", docs ds), ("id", id i),
      ("items", .arr (items.map interfaceItem))])
  | .world ds i items => tag "world" (.obj [("docs", docs ds), ("id", id i),
      ("items", .arr (items.map worldItem))])
  | .type d => tag "type" (typeDecl d)

/-- An `ExternName` (or `InstantiationArgumentName`). -/
def externName : ExternName → J
  | .ident i => tag "ident" (id i)
  | .string s => tag "string" (.obj [("value", .str s)])

/-- A postfix expression. -/
def postfixJ : Postfix → J
  | .access i => tag "access" (.obj [("id", id i)])
  | .namedAccess s => tag "namedAccess" (.obj [("string", .obj [("value", .str s)])])

mutual
/-- An `Expr`. -/
partial def expr : Expr → J
  | .mk p post => .obj [("primary", primary p), ("postfix", .arr (post.map postfixJ))]
/-- A `PrimaryExpr`. -/
partial def primary : Primary → J
  | .new pkg as => tag "new" (.obj [("package", pkgName pkg), ("arguments", .arr (as.map arg))])
  | .nested e => tag "nested" (.obj [("inner", expr e)])
  | .ident i => tag "ident" (id i)
/-- An `InstantiationArgument`. -/
partial def arg : Arg → J
  | .inferred i => tag "inferred" (id i)
  | .spread i => tag "spread" (id i)
  | .named n e => tag "named" (.obj [("name", externName n), ("expr", expr e)])
  | .fill => tag "fill" .null
end

/-- An `ImportType`. -/
def importType : ImportType → J
  | .package p => tag "package" (pkgPath p)
  | .func f => tag "func" (funcType f)
  | .interface items => tag "interface" (inlineInterface items)
  | .ident i => tag "ident" (id i)

/-- A `Statement`. -/
def statement : Statement → J
  | .import_ ds i n t => tag "Import" (.obj [("docs", docs ds), ("id", id i),
      ("name", opt externName n), ("ty", importType t)])
  | .type s => tag "Type" (typeStatement s)
  | .let_ ds i e => tag "Let" (.obj [("docs", docs ds), ("id", id i), ("expr", expr e)])
  | .export_ ds e o => tag "Export" (.obj [("docs", docs ds), ("expr", expr e),
      ("options", match o with
        | .none => .str "none"
        | .spread => tag "spread" .null
        | .rename n => tag "rename" (externName n))])

/-- A `Document`. -/
def document (d : Document) : J :=
  .obj [("docs", docs d.docs),
        ("directive", .obj ([("package", pkgName d.package)] ++
          (match d.targets with | some p => [("targets", pkgPath p)] | none => []))),
        ("statements", .arr (d.statements.map statement))]

end Json

/-- The JSON of a document (`wac parse` without spans). -/
def toJson (d : Document) : String := (Json.document d).render

end Silmaril.Wasm.Wac.Text
