module

public import Silmaril.Wasm.Wac.Text.Lex.Defs

/-!
# WAC text: the printer

The printer from the AST (`Silmaril.Wasm.Wac.Text.Ast`) to tokens with docs
(`Silmaril.Wasm.Wac.Text.Lex`), in the spelling of `wac-parser` 0.12.0's grammar: the doc
comments of an item are attached to its first token; comma lists have no trailing
comma; `result` is written without `<…>` when both sides are absent and with `_` for an
absent `ok`; `resource r;` when a resource has no methods; `include w;` when the `with`
list is empty; an `ExternName` that is an identifier is written as one.

`print d` lays the tokens out with `render` (one space after each token); `pretty`
breaks lines after `;`, `{` and `}` with indentation by brace depth (any whitespace
lexes the same, `lex_renderWith`).

`semverOk` is the version syntax of the `semver` crate (1.x), which `wac-parser` uses
for the versions of package names and paths.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Text

/-- Tokens with docs. -/
abbrev Toks := List ATok

/-- A token without docs. -/
abbrev tk (t : Tok) : ATok := ⟨[], t⟩
/-- A symbol. -/
abbrev sy (c : Char) : ATok := tk (.sym c)
/-- A keyword. -/
abbrev kw (k : Kw) : ATok := tk (.kw k)
/-- An identifier. -/
abbrev ident (s : String) : ATok := tk (.id s)

/-- Items separated by commas. -/
def commaList {α : Type} (f : α → Toks) : List α → Toks
  | [] => []
  | [a] => f a
  | a :: b :: r => f a ++ sy ',' :: commaList f (b :: r)

namespace Pr

mutual
/-- A type. -/
def ty : Ty → Toks
  | .u8 => [kw .u8] | .s8 => [kw .s8] | .u16 => [kw .u16] | .s16 => [kw .s16]
  | .u32 => [kw .u32] | .s32 => [kw .s32] | .u64 => [kw .u64] | .s64 => [kw .s64]
  | .f32 => [kw .f32] | .f64 => [kw .f64] | .char => [kw .char] | .bool => [kw .bool]
  | .string => [kw .string]
  | .tuple ts => kw .tuple :: sy '<' :: tys ts ++ [sy '>']
  | .list t => kw .list :: sy '<' :: ty t ++ [sy '>']
  | .option t => kw .option :: sy '<' :: ty t ++ [sy '>']
  | .result none none => [kw .result]
  | .result (some o) none => kw .result :: sy '<' :: ty o ++ [sy '>']
  | .result none (some e) => kw .result :: sy '<' :: sy '_' :: sy ',' :: ty e ++ [sy '>']
  | .result (some o) (some e) => kw .result :: sy '<' :: ty o ++ sy ',' :: ty e ++ [sy '>']
  | .borrow id => [kw .borrow, sy '<', ident id, sy '>']
  | .stream none => [kw .stream]
  | .stream (some t) => kw .stream :: sy '<' :: ty t ++ [sy '>']
  | .future none => [kw .future]
  | .future (some t) => kw .future :: sy '<' :: ty t ++ [sy '>']
  | .errorContext => [kw .errorContext]
  | .ident id => [ident id]
/-- Types separated by commas. -/
def tys : List Ty → Toks
  | [] => []
  | [t] => ty t
  | t :: u :: r => ty t ++ sy ',' :: tys (u :: r)
end

/-- `id: ty`. -/
def namedType (n : NamedType) : Toks := ident n.id :: sy ':' :: ty n.ty

/-- `async? func(params) (-> ty)?`. -/
def funcType (f : FuncType) : Toks :=
  (if f.isAsync then [kw .async] else []) ++ kw .func :: sy '(' ::
    commaList namedType f.params ++ sy ')' ::
    (match f.results with
     | .empty => []
     | .scalar t => tk .arrow :: ty t)

/-- A function type or its name. -/
def funcTypeRef : FuncTypeRef → Toks
  | .func f => funcType f
  | .ident id => [ident id]

/-- The first token of an item, with the item's docs. -/
def first (ds : Docs) (t : Tok) : ATok := ⟨ds, t⟩

/-- A variant case. -/
def variantCase (c : VariantCase) : Toks :=
  ⟨c.docs, .id c.id⟩ :: (match c.ty with | some t => sy '(' :: ty t ++ [sy ')'] | none => [])

/-- A record field. -/
def field (f : Field) : Toks := ⟨f.docs, .id f.id⟩ :: sy ':' :: ty f.ty

/-- A flag or enum case. -/
def case (c : Case) : Toks := [⟨c.docs, .id c.id⟩]

/-- A type declaration. -/
def typeDecl : TypeDecl → Toks
  | .variant ds id cs =>
    first ds (.kw .variant) :: ident id :: sy '{' :: commaList variantCase cs ++ [sy '}']
  | .record ds id fs =>
    first ds (.kw .record) :: ident id :: sy '{' :: commaList field fs ++ [sy '}']
  | .flags ds id fs =>
    first ds (.kw .flags) :: ident id :: sy '{' :: commaList case fs ++ [sy '}']
  | .enum ds id cs =>
    first ds (.kw .enum) :: ident id :: sy '{' :: commaList case cs ++ [sy '}']
  | .alias ds id k =>
    first ds (.kw .type) :: ident id :: sy '=' ::
      (match k with | .func f => funcType f | .type t => ty t) ++ [sy ';']

/-- A resource method or constructor. -/
def resourceMethod : ResourceMethod → Toks
  | .ctor ds ps => first ds (.kw .ctor) :: sy '(' :: commaList namedType ps ++ [sy ')', sy ';']
  | .method ds id st f =>
    first ds (.id id) :: sy ':' :: (if st then [kw .static] else []) ++ funcType f ++ [sy ';']

/-- A type declaration of an interface or world. -/
def itemTypeDecl : ItemTypeDecl → Toks
  | .resource ds id [] => [first ds (.kw .resource), ident id, sy ';']
  | .resource ds id ms =>
    first ds (.kw .resource) :: ident id :: sy '{' :: ms.flatMap resourceMethod ++ [sy '}']
  | .decl d => typeDecl d

/-- A package path. -/
def pkgPath (p : PkgPath) : Tok := .ppath p.name p.segments p.version

/-- `id (as id)?`. -/
def useItem (i : UseItem) : Toks :=
  ident i.id :: (match i.asId with | some a => [kw .as, ident a] | none => [])

/-- `use path.{items};`. -/
def use (u : Use) : Toks :=
  first u.docs (.kw .use) ::
    (match u.path with | .package p => tk (pkgPath p) | .ident id => ident id) ::
    sy '.' :: sy '{' :: commaList useItem u.items ++ [sy '}', sy ';']

/-- An interface item. -/
def interfaceItem : InterfaceItem → Toks
  | .use u => use u
  | .type d => itemTypeDecl d
  | .export_ ds id f => first ds (.id id) :: sy ':' :: funcTypeRef f ++ [sy ';']

/-- `interface { items }`. -/
def inlineInterface (items : List InterfaceItem) : Toks :=
  kw .interface :: sy '{' :: items.flatMap interfaceItem ++ [sy '}']

/-- The type of a named world item. -/
def externType : ExternType → Toks
  | .ident id => [ident id]
  | .func f => funcType f
  | .interface items => inlineInterface items

/-- What a world imports or exports. -/
def worldItemPath : WorldItemPath → Toks
  | .named id t => ident id :: sy ':' :: externType t
  | .package p => [tk (pkgPath p)]
  | .ident id => [ident id]

/-- `from as to`. -/
def includeItem (i : IncludeItem) : Toks := [ident i.from, kw .as, ident i.to]

/-- A world item. -/
def worldItem : WorldItem → Toks
  | .use u => use u
  | .type d => itemTypeDecl d
  | .import_ ds p => first ds (.kw .import) :: worldItemPath p ++ [sy ';']
  | .export_ ds p => first ds (.kw .export) :: worldItemPath p ++ [sy ';']
  | .include ds w ws =>
    first ds (.kw .include) ::
      (match w with | .ident id => ident id | .package p => tk (pkgPath p)) ::
      (match ws with
       | [] => []
       | _ => kw .with :: sy '{' ::
           commaList includeItem ws ++ [sy '}']) ++ [sy ';']

/-- A type statement. -/
def typeStatement : TypeStatement → Toks
  | .interface ds id items =>
    first ds (.kw .interface) :: ident id :: sy '{' :: items.flatMap interfaceItem ++ [sy '}']
  | .world ds id items =>
    first ds (.kw .world) :: ident id :: sy '{' :: items.flatMap worldItem ++ [sy '}']
  | .type d => typeDecl d

/-- An identifier or a string. -/
def externName : ExternName → ATok
  | .ident id => ident id
  | .string s => tk (.str s)

/-- A postfix access. -/
def postfixT : Postfix → Toks
  | .access id => [sy '.', ident id]
  | .namedAccess s => [sy '[', tk (.str s), sy ']']

mutual
/-- An expression. -/
def expr : Expr → Toks
  | .mk p post => primary p ++ post.flatMap postfixT
/-- A primary expression. -/
def primary : Primary → Toks
  | .new pkg as => kw .new :: tk (.pname pkg.name pkg.version) :: sy '{' :: args as ++ [sy '}']
  | .nested e => sy '(' :: expr e ++ [sy ')']
  | .ident id => [ident id]
/-- Instantiation arguments, separated by commas. -/
def args : List Arg → Toks
  | [] => []
  | [a] => arg a
  | a :: b :: r => arg a ++ sy ',' :: args (b :: r)
/-- An instantiation argument. -/
def arg : Arg → Toks
  | .inferred id => [ident id]
  | .spread id => [tk .ellipsis, ident id]
  | .named n e => externName n :: sy ':' :: expr e
  | .fill => [tk .ellipsis]
end

/-- The type of an import. -/
def importType : ImportType → Toks
  | .package p => [tk (pkgPath p)]
  | .func f => funcType f
  | .interface items => inlineInterface items
  | .ident id => [ident id]

/-- A statement. -/
def statement : Statement → Toks
  | .import_ ds id n t =>
    first ds (.kw .import) :: ident id ::
      (match n with | some n => [kw .as, externName n] | none => []) ++
      sy ':' :: importType t ++ [sy ';']
  | .type s => typeStatement s
  | .let_ ds id e => first ds (.kw .let) :: ident id :: sy '=' :: expr e ++ [sy ';']
  | .export_ ds e o =>
    first ds (.kw .export) :: expr e ++
      (match o with
       | .none => []
       | .spread => [tk .ellipsis]
       | .rename n => [kw .as, externName n]) ++ [sy ';']

/-- A document. -/
def document (d : Document) : Toks :=
  first d.docs (.kw .package) :: tk (.pname d.package.name d.package.version) ::
    (match d.targets with | some p => [kw .targets, tk (pkgPath p)] | none => []) ++
    sy ';' :: d.statements.flatMap statement

end Pr

/-- The text of a document, one space after each token. -/
def print (d : Document) : String := String.ofList (render (Pr.document d))

/-- Brace depth after the `i`-th token. -/
def depthAt (ts : Toks) (i : Nat) : Nat :=
  ((ts.take (i + 1)).map (·.tok)).foldl
    (fun d t => if t = .sym '{' then d + 1 else if t = .sym '}' then d - 1 else d) 0

/-- A layout for reading: a new line after `;`, `{` and `}` (a blank line between
top-level statements), indented by brace depth; no space after `(`, `<`, `[`, `.`, `...`
and before `,`, `;`, `)`, `>`, `]`, `:`, `.`, `[`, a spread `...` and the `(` of a
function type; a space elsewhere. Unlike `render`, this layout is not covered by
`lex_render`; `wasm-wac check` tests it on its input. -/
def prettySep (ts : Toks) : Nat → List Char := fun i =>
  let depth := depthAt ts i
  let cur := (ts[i]?).map (·.tok)
  let next := (ts[i + 1]?).map (·.tok)
  let nextDepth := if next = some (.sym '}') then depth - 1 else depth
  let brk := '\n' :: List.replicate (2 * nextDepth) ' '
  let glueAfter := cur = some (.sym '(') ∨ cur = some (.sym '<') ∨ cur = some (.sym '[') ∨
    cur = some (.sym '.') ∨ (cur = some .ellipsis ∧ next ≠ some (.sym ';'))
  let glueBefore := next = some (.sym ',') ∨ next = some (.sym ';') ∨ next = some (.sym ')') ∨
    next = some (.sym '>') ∨ next = some (.sym ']') ∨ next = some (.sym ':') ∨
    next = some (.sym '.') ∨ next = some (.sym '[') ∨
    (next = some .ellipsis ∧ cur ≠ some (.sym ',') ∧ cur ≠ some (.sym '{')) ∨
    (next = some (.sym '(') ∧ (cur = some (.kw .func) ∨ cur = some (.kw .ctor)))
  let afterBrace := cur = some (.sym '}') ∧ (next = some (.sym ',') ∨ next = some (.sym ';') ∨
    next = some (.sym '.') ∨ next = some (.sym '[') ∨ next = some .ellipsis ∨
    next = some (.sym ')'))
  match cur with
  | some (.sym ';') => if depth = 0 ∧ next ≠ none then '\n' :: brk else brk
  | some (.sym '{') => if next = some (.sym '}') then [] else brk
  | some (.sym '}') => if afterBrace then [] else if depth = 0 ∧ next ≠ none then '\n' :: brk else brk
  | _ =>
    if next = some (.sym '}') then brk
    else if (glueAfter ∨ glueBefore) ∧ cur ≠ some (.sym ':') then []
    else [' ']

/-- The indentation of the doc lines of the `i`-th token. -/
def prettyInd (ts : Toks) (i : Nat) : List Char :=
  List.replicate (2 * (if i = 0 then 0 else depthAt ts (i - 1))) ' '

/-- The text of a document, with line breaks and indentation. -/
def pretty (d : Document) : String :=
  let ts := Pr.document d
  String.ofList (renderWith (prettySep ts) (prettyInd ts) 0 ts)

/-! ## Well-formedness -/

/-- An identifier: `word(-word)*`, `word = [a-z][a-z0-9]* | [A-Z][A-Z0-9]*`. -/
def idOk (s : String) : Bool :=
  match idBody s.toList with
  | some (_, []) => true
  | _ => false

/-- A numeric identifier of a version: digits, without a leading zero (unless `0`). -/
def numOk (cs : List Char) : Bool :=
  !cs.isEmpty && cs.all isDigitC && (cs.length == 1 || cs.head? != some '0')

/-- Split a list at every occurrence of `c`. -/
def splitOnC (c : Char) : List Char → List (List Char)
  | [] => [[]]
  | d :: ds =>
    if d = c then [] :: splitOnC c ds
    else match splitOnC c ds with
      | x :: xs => (d :: x) :: xs
      | [] => [[d]]

/-- Split at the first occurrence of `c`. -/
def splitFirstC (c : Char) : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | d :: ds =>
    if d = c then ([], some ds) else (d :: (splitFirstC c ds).1, (splitFirstC c ds).2)

/-- An identifier of a pre-release or build part: `[0-9A-Za-z-]+`. -/
def semIdOk (cs : List Char) : Bool :=
  !cs.isEmpty && cs.all (fun c => isLetter c || isDigitC c || c == '-')

/-- The version syntax of the `semver` crate: `major.minor.patch(-pre)?(+build)?`, with
numeric parts without leading zeros (also among the pre-release identifiers). -/
def semverOk (s : String) : Bool :=
  let (core, build) := splitFirstC '+' s.toList
  let (mmp, pre) := splitFirstC '-' core
  (match splitOnC '.' mmp with
   | [a, b, c] => numOk a && numOk b && numOk c
   | _ => false) &&
  (match pre with
   | none => true
   | some p => (splitOnC '.' p).all fun i =>
       semIdOk i && (!i.all isDigitC || numOk i)) &&
  (match build with
   | none => true
   | some b => (splitOnC '.' b).all semIdOk)

/-- A string literal: no `"` and no rejected character. -/
def strOk (s : String) : Bool := !s.toList.contains '"' && !s.toList.any badChar

/-- A doc comment: one line, trimmed, no rejected character. -/
def docOk (d : String) : Bool :=
  !d.toList.contains '\n' && trimU d.toList == d.toList && !d.toList.any badChar

/-- Doc comments. -/
def docsOk (ds : Docs) : Bool := ds.all docOk

/-- The source text of a package name `ns:name` (identifiers, possibly with `%`). -/
def nameOk (n : String) : Bool :=
  match idRaw n.toList with
  | some (_, r) => !(sepIds ':' r).1.isEmpty && (sepIds ':' r).2.isEmpty
  | none => false

/-- The segments `a/b` of a package path. -/
def segsOk (s : String) : Bool := (sepIds '/' ('/' :: s.toList)).2.isEmpty &&
  !(sepIds '/' ('/' :: s.toList)).1.isEmpty

/-- A version the lexer reads back as one: `atVer` takes all of `@v`. -/
def verLexOk (v : String) : Bool := atVer ('@' :: v.toList) == (some v.toList, [])

/-- An optional version: valid for `semver` and read back by the lexer. -/
def verOk : Option String → Bool
  | some v => semverOk v && verLexOk v
  | none => true

/-- A package name. -/
def pkgNameOk (p : PkgName) : Bool := nameOk p.name && verOk p.version

/-- A package path. -/
def pkgPathOk (p : PkgPath) : Bool := nameOk p.name && segsOk p.segments && verOk p.version

/-- Tokens the lexer reads back (followed by whitespace). -/
def Tok.ok : Tok → Bool
  | .id s => idOk s
  | .kw _ => true
  | .str s => strOk s
  | .pname n v => nameOk n && (match v with | some v => verLexOk v | none => true)
  | .ppath n sg v => nameOk n && segsOk sg && (match v with | some v => verLexOk v | none => true)
  | .sym c => symChars.contains c
  | .arrow | .ellipsis => true

namespace Wf

mutual
/-- Types. -/
def ty : Ty → Bool
  | .tuple ts => !ts.isEmpty && tys ts
  | .list t | .option t => ty t
  | .result o e => (match o with | some t => ty t | none => true) &&
      (match e with | some t => ty t | none => true)
  | .borrow id | .ident id => idOk id
  | .stream (some t) | .future (some t) => ty t
  | _ => true
/-- Lists of types. -/
def tys : List Ty → Bool
  | [] => true
  | t :: ts => ty t && tys ts
end

/-- `id: ty`. -/
def namedType (n : NamedType) : Bool := idOk n.id && ty n.ty

/-- Function types. -/
def funcType (f : FuncType) : Bool :=
  f.params.all namedType && (match f.results with | .empty => true | .scalar t => ty t)

/-- Function type references. -/
def funcTypeRef : FuncTypeRef → Bool
  | .func f => funcType f
  | .ident id => idOk id

/-- Type declarations: nonempty bodies. -/
def typeDecl : TypeDecl → Bool
  | .variant ds id cs => docsOk ds && idOk id && !cs.isEmpty &&
      cs.all fun c => docsOk c.docs && idOk c.id && (match c.ty with | some t => ty t | none => true)
  | .record ds id fs => docsOk ds && idOk id && !fs.isEmpty &&
      fs.all fun f => docsOk f.docs && idOk f.id && ty f.ty
  | .flags ds id fs | .enum ds id fs => docsOk ds && idOk id && !fs.isEmpty &&
      fs.all fun c => docsOk c.docs && idOk c.id
  | .alias ds id k => docsOk ds && idOk id &&
      (match k with | .func f => funcType f | .type t => ty t)

/-- Resource methods. -/
def resourceMethod : ResourceMethod → Bool
  | .ctor ds ps => docsOk ds && ps.all namedType
  | .method ds id _ f => docsOk ds && idOk id && funcType f

/-- Item type declarations. -/
def itemTypeDecl : ItemTypeDecl → Bool
  | .resource ds id ms => docsOk ds && idOk id && ms.all resourceMethod
  | .decl d => typeDecl d

/-- `use`. -/
def use (u : Use) : Bool :=
  docsOk u.docs && (match u.path with | .package p => pkgPathOk p | .ident id => idOk id) &&
    u.items.all fun i => idOk i.id && (match i.asId with | some a => idOk a | none => true)

/-- Interface items. -/
def interfaceItem : InterfaceItem → Bool
  | .use u => use u
  | .type d => itemTypeDecl d
  | .export_ ds id f => docsOk ds && idOk id && funcTypeRef f

/-- Extern types. -/
def externType : ExternType → Bool
  | .ident id => idOk id
  | .func f => funcType f
  | .interface items => items.all interfaceItem

/-- World item paths. -/
def worldItemPath : WorldItemPath → Bool
  | .named id t => idOk id && externType t
  | .package p => pkgPathOk p
  | .ident id => idOk id

/-- World items. -/
def worldItem : WorldItem → Bool
  | .use u => use u
  | .type d => itemTypeDecl d
  | .import_ ds p | .export_ ds p => docsOk ds && worldItemPath p
  | .include ds w ws => docsOk ds &&
      (match w with | .ident id => idOk id | .package p => pkgPathOk p) &&
      ws.all fun i => idOk i.from && idOk i.to

/-- Type statements. -/
def typeStatement : TypeStatement → Bool
  | .interface ds id items => docsOk ds && idOk id && items.all interfaceItem
  | .world ds id items => docsOk ds && idOk id && items.all worldItem
  | .type d => typeDecl d

/-- Extern names. -/
def externName : ExternName → Bool
  | .ident id => idOk id
  | .string s => strOk s

/-- Postfix accesses. -/
def postfixOk : Postfix → Bool
  | .access id => idOk id
  | .namedAccess s => strOk s

mutual
/-- Expressions. -/
def expr : Expr → Bool
  | .mk p post => primary p && post.all postfixOk
/-- Primary expressions. -/
def primary : Primary → Bool
  | .new pkg as => pkgNameOk pkg && args as
  | .nested e => expr e
  | .ident id => idOk id
/-- Arguments. -/
def args : List Arg → Bool
  | [] => true
  | a :: as => arg a && args as
/-- An argument. -/
def arg : Arg → Bool
  | .inferred id | .spread id => idOk id
  | .named n e => externName n && expr e
  | .fill => true
end

/-- Import types. -/
def importType : ImportType → Bool
  | .package p => pkgPathOk p
  | .func f => funcType f
  | .interface items => items.all interfaceItem
  | .ident id => idOk id

/-- Statements. -/
def statement : Statement → Bool
  | .import_ ds id n t => docsOk ds && idOk id &&
      (match n with | some n => externName n | none => true) && importType t
  | .type s => typeStatement s
  | .let_ ds id e => docsOk ds && idOk id && expr e
  | .export_ ds e o => docsOk ds && expr e &&
      (match o with | .rename n => externName n | _ => true)

end Wf

/-- A well-formed document: what `print` writes lexes and parses back to it
(`parse_print`). Identifiers, strings, docs, package names and versions are spellable;
tuples, variants, records, flags and enums are nonempty. -/
def wf (d : Document) : Bool :=
  docsOk d.docs && pkgNameOk d.package &&
    (match d.targets with | some p => pkgPathOk p | none => true) &&
    d.statements.all Wf.statement

end Silmaril.Wasm.Wac.Text
