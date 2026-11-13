module

public import Silmaril.Wasm.Wac.Text.Print.Defs

/-!
# WAC text: the parser

A recursive-descent parser from tokens with docs (`Silmaril.Wasm.Wac.Text.Lex`) to the AST
(`Silmaril.Wasm.Wac.Text.Ast`), transcribing the `Parse` implementations of `wac-parser`
0.12.0 (`crates/wac-parser/src/ast.rs`, `ast/*.rs`; bytecodealliance/wac
`5a7480c69ae7a4dc9eb161f485cbcb8c95e372c9`): the same alternatives in the same order,
`parse_delimited` (`delim`: items until a closing token, with or without commas, a
trailing comma allowed), `parse_optional`, the empty-declaration errors (variant,
record, flags, enum, tuple) and the version check of package names and paths
(`semverOk`). The docs of an item are the docs of its first token.

Every parser takes fuel (`n`) and the tokens, and returns the result and the remaining
tokens; nested parsers spend one unit. `document` starts with three times the number of
tokens plus three (an expression nesting level spends up to three units).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Text

namespace Parse

/-- The docs of the next token. -/
def docsOf : Toks → Docs
  | a :: _ => a.docs
  | [] => []

/-- The next token is `t`. -/
def isTok (t : Tok) : Toks → Bool
  | a :: _ => a.tok == t
  | [] => false

/-- Consume the token `t`. -/
def expect (t : Tok) : Toks → Option Toks
  | a :: r => if a.tok = t then some r else none
  | [] => none

/-- Consume the symbol `c`. -/
def sym (c : Char) : Toks → Option Toks := expect (.sym c)

/-- An identifier. -/
def ident : Toks → Option (String × Toks)
  | ⟨_, .id s⟩ :: r => some (s, r)
  | _ => none

/-- A string literal. -/
def str : Toks → Option (String × Toks)
  | ⟨_, .str s⟩ :: r => some (s, r)
  | _ => none

/-- A checked optional version. -/
def ver? : Option String → Option (Option String)
  | none => some none
  | some v => if semverOk v then some (some v) else none

/-- A package name. -/
def pkgName : Toks → Option (PkgName × Toks)
  | ⟨_, .pname n v⟩ :: r => (ver? v).map fun v => ({ name := n, version := v }, r)
  | _ => none

/-- A package path. -/
def pkgPath : Toks → Option (PkgPath × Toks)
  | ⟨_, .ppath n s v⟩ :: r => (ver? v).map fun v => ({ name := n, segments := s, version := v }, r)
  | _ => none

/-- `parse_delimited`: items until the symbol `close` (not consumed), separated by
commas when `commas`, with an optional trailing comma. -/
def delim {α : Type} (p : Toks → Option (α × Toks)) (close : Char) (commas : Bool) :
    Nat → Toks → Option (List α × Toks)
  | 0, _ => none
  | n + 1, ts =>
    if isTok (.sym close) ts then some ([], ts) else
    match p ts with
    | none => none
    | some (a, r) =>
      if isTok (.sym close) r then some ([a], r)
      else if commas then
        match sym ',' r with
        | some r' => (delim p close commas n r').map fun q => (a :: q.1, q.2)
        | none => none
      else (delim p close commas n r).map fun q => (a :: q.1, q.2)

/-- `< t >` around a parser's result. -/
def angle {α : Type} (p : Toks → Option (α × Toks)) (ts : Toks) : Option (α × Toks) := do
  let r ← sym '<' ts
  let (a, r) ← p r
  let r ← sym '>' r
  pure (a, r)

/-- The primitive type of a keyword. -/
def primOf : Kw → Option Ty
  | .u8 => some .u8 | .s8 => some .s8 | .u16 => some .u16 | .s16 => some .s16
  | .u32 => some .u32 | .s32 => some .s32 | .u64 => some .u64 | .s64 => some .s64
  | .f32 => some .f32 | .f64 => some .f64 | .char => some .char | .bool => some .bool
  | .string => some .string | .errorContext => some .errorContext
  | _ => none

/-- `_` (nothing) or a type, in `result<…>`. -/
def optTy (p : Toks → Option (Ty × Toks)) (r : Toks) : Option (Option Ty × Toks) :=
  if isTok (.sym '_') r then some (none, r.drop 1) else (p r).map fun (t, r) => (some t, r)

/-- A type (`Type::parse`). -/
def ty : Nat → Toks → Option (Ty × Toks)
  | 0, _ => none
  | n + 1, ts =>
    match ts with
    | ⟨_, .kw k⟩ :: r =>
      match primOf k with
      | some t => some (t, r)
      | none =>
        match k with
        | .tuple => do
          let r ← sym '<' r
          if isTok (.sym '>') r then none else
          let (ts, r) ← delim (ty n) '>' true n r
          let r ← sym '>' r
          pure (.tuple ts, r)
        | .list => (angle (ty n) r).map fun (t, r) => (.list t, r)
        | .option => (angle (ty n) r).map fun (t, r) => (.option t, r)
        | .result =>
          match sym '<' r with
          | none => some (.result none none, r)
          | some r => do
            let (ok, r) ← optTy (ty n) r
            let (err, r) ← (match sym ',' r with
              | none => some (none, r)
              | some r => optTy (ty n) r)
            let r ← sym '>' r
            pure (.result ok err, r)
        | .borrow => (angle ident r).map fun (id, r) => (.borrow id, r)
        | .stream =>
          match sym '<' r with
          | none => some (.stream none, r)
          | some _ => (angle (ty n) r).map fun (t, r) => (.stream (some t), r)
        | .future =>
          match sym '<' r with
          | none => some (.future none, r)
          | some _ => (angle (ty n) r).map fun (t, r) => (.future (some t), r)
        | _ => none
    | ⟨_, .id s⟩ :: r => some (.ident s, r)
    | _ => none

/-- `id: ty`. -/
def namedType (n : Nat) (ts : Toks) : Option (NamedType × Toks) := do
  let (id, r) ← ident ts
  let r ← sym ':' r
  let (t, r) ← ty n r
  pure ({ id, ty := t }, r)

/-- A function type (`FuncType::parse`). -/
def funcType (n : Nat) (ts : Toks) : Option (FuncType × Toks) := do
  let (isAsync, r) := match ts with
    | ⟨_, .kw .async⟩ :: r => (true, r)
    | _ => (false, ts)
  let r ← expect (.kw .func) r
  let r ← sym '(' r
  let (ps, r) ← delim (namedType n) ')' true n r
  let r ← sym ')' r
  if isTok .arrow r then
    let (t, r) ← ty n (r.drop 1)
    pure ({ isAsync, params := ps, results := .scalar t }, r)
  else pure ({ isAsync, params := ps, results := .empty }, r)

/-- A function type or its name (`FuncTypeRef::parse`). -/
def funcTypeRef (n : Nat) (ts : Toks) : Option (FuncTypeRef × Toks) :=
  match ts with
  | ⟨_, .kw .async⟩ :: _ | ⟨_, .kw .func⟩ :: _ => (funcType n ts).map fun (f, r) => (.func f, r)
  | ⟨_, .id s⟩ :: r => some (.ident s, r)
  | _ => none

/-- `{ items }` with a nonempty comma list, as the declarations of variants, records,
flags and enums require. -/
def braced {α : Type} (p : Toks → Option (α × Toks)) (n : Nat) (ts : Toks) :
    Option (List α × Toks) := do
  let r ← sym '{' ts
  let (xs, r) ← delim p '}' true n r
  let r ← sym '}' r
  if xs.isEmpty then none else pure (xs, r)

/-- A variant case. -/
def variantCase (n : Nat) (ts : Toks) : Option (VariantCase × Toks) := do
  let (id, r) ← ident ts
  match sym '(' r with
  | some r =>
    let (t, r) ← ty n r
    let r ← sym ')' r
    pure ({ docs := docsOf ts, id, ty := some t }, r)
  | none => pure ({ docs := docsOf ts, id, ty := none }, r)

/-- A record field. -/
def field (n : Nat) (ts : Toks) : Option (Field × Toks) :=
  (namedType n ts).map fun (nt, r) => ({ docs := docsOf ts, id := nt.id, ty := nt.ty }, r)

/-- A flag or enum case. -/
def case (ts : Toks) : Option (Case × Toks) :=
  (ident ts).map fun (id, r) => ({ docs := docsOf ts, id }, r)

/-- A type declaration (`TypeDecl::parse`), after the keyword `k`. -/
def typeDecl (n : Nat) (ts : Toks) : Option (TypeDecl × Toks) :=
  let ds := docsOf ts
  match ts with
  | ⟨_, .kw .variant⟩ :: r => do
    let (id, r) ← ident r
    let (cs, r) ← braced (variantCase n) n r
    pure (.variant ds id cs, r)
  | ⟨_, .kw .record⟩ :: r => do
    let (id, r) ← ident r
    let (fs, r) ← braced (field n) n r
    pure (.record ds id fs, r)
  | ⟨_, .kw .flags⟩ :: r => do
    let (id, r) ← ident r
    let (fs, r) ← braced case n r
    pure (.flags ds id fs, r)
  | ⟨_, .kw .enum⟩ :: r => do
    let (id, r) ← ident r
    let (cs, r) ← braced case n r
    pure (.enum ds id cs, r)
  | ⟨_, .kw .type⟩ :: r => do
    let (id, r) ← ident r
    let r ← sym '=' r
    let (k, r) ← (if isTok (.kw .async) r || isTok (.kw .func) r then
        (funcType n r).map fun (f, r) => (AliasKind.func f, r)
      else (ty n r).map fun (t, r) => (AliasKind.type t, r))
    let r ← sym ';' r
    pure (.alias ds id k, r)
  | _ => none

/-- A resource method or constructor (`ResourceMethod::parse`). -/
def resourceMethod (n : Nat) (ts : Toks) : Option (ResourceMethod × Toks) :=
  let ds := docsOf ts
  match ts with
  | ⟨_, .kw .ctor⟩ :: r => do
    let r ← sym '(' r
    let (ps, r) ← delim (namedType n) ')' true n r
    let r ← sym ')' r
    let r ← sym ';' r
    pure (.ctor ds ps, r)
  | ⟨_, .id id⟩ :: r => do
    let r ← sym ':' r
    let (st, r) := match r with
      | ⟨_, .kw .static⟩ :: r => (true, r)
      | _ => (false, r)
    let (f, r) ← funcType n r
    let r ← sym ';' r
    pure (.method ds id st f, r)
  | _ => none

/-- A type declaration of an interface or world (`ItemTypeDecl::parse`). -/
def itemTypeDecl (n : Nat) (ts : Toks) : Option (ItemTypeDecl × Toks) :=
  match ts with
  | ⟨ds, .kw .resource⟩ :: r => do
    let (id, r) ← ident r
    match r with
    | ⟨_, .sym ';'⟩ :: r => pure (.resource ds id [], r)
    | ⟨_, .sym '{'⟩ :: r =>
      let (ms, r) ← delim (resourceMethod n) '}' false n r
      let r ← sym '}' r
      pure (.resource ds id ms, r)
    | _ => none
  | _ => (typeDecl n ts).map fun (d, r) => (.decl d, r)

/-- A `use` path. -/
def usePath (ts : Toks) : Option (UsePath × Toks) :=
  match ts with
  | ⟨_, .ppath _ _ _⟩ :: _ => (pkgPath ts).map fun (p, r) => (.package p, r)
  | ⟨_, .id s⟩ :: r => some (.ident s, r)
  | _ => none

/-- `id (as id)?`. -/
def useItem (ts : Toks) : Option (UseItem × Toks) := do
  let (id, r) ← ident ts
  if isTok (.kw .as) r then
    let (a, r) ← ident (r.drop 1)
    pure ({ id, asId := some a }, r)
  else pure ({ id, asId := none }, r)

/-- `use path.{items};`. -/
def use (n : Nat) (ts : Toks) : Option (Use × Toks) := do
  let r ← expect (.kw .use) ts
  let (p, r) ← usePath r
  let r ← sym '.' r
  let r ← sym '{' r
  let (items, r) ← delim useItem '}' true n r
  let r ← sym '}' r
  let r ← sym ';' r
  pure ({ docs := docsOf ts, path := p, items }, r)

/-- An interface item (`InterfaceItem::parse`). -/
def interfaceItem (n : Nat) (ts : Toks) : Option (InterfaceItem × Toks) :=
  match ts with
  | ⟨_, .kw .use⟩ :: _ => (use n ts).map fun (u, r) => (.use u, r)
  | ⟨ds, .id id⟩ :: r => do
    let r ← sym ':' r
    let (f, r) ← funcTypeRef n r
    let r ← sym ';' r
    pure (.export_ ds id f, r)
  | _ => (itemTypeDecl n ts).map fun (d, r) => (.type d, r)

/-- `{ items }` of an interface. -/
def interfaceBody (n : Nat) (ts : Toks) : Option (List InterfaceItem × Toks) := do
  let r ← sym '{' ts
  let (items, r) ← delim (interfaceItem n) '}' false n r
  let r ← sym '}' r
  pure (items, r)

/-- `interface { items }` (`InlineInterface::parse`). -/
def inlineInterface (n : Nat) (ts : Toks) : Option (List InterfaceItem × Toks) := do
  let r ← expect (.kw .interface) ts
  interfaceBody n r

/-- The type of a named world item (`ExternType::parse`). -/
def externType (n : Nat) (ts : Toks) : Option (ExternType × Toks) :=
  match ts with
  | ⟨_, .id s⟩ :: r => some (.ident s, r)
  | ⟨_, .kw .async⟩ :: _ | ⟨_, .kw .func⟩ :: _ => (funcType n ts).map fun (f, r) => (.func f, r)
  | ⟨_, .kw .interface⟩ :: _ => (inlineInterface n ts).map fun (i, r) => (.interface i, r)
  | _ => none

/-- What a world imports or exports (`WorldItemPath::parse`). -/
def worldItemPath (n : Nat) (ts : Toks) : Option (WorldItemPath × Toks) :=
  match ts with
  | ⟨_, .ppath _ _ _⟩ :: _ => (pkgPath ts).map fun (p, r) => (.package p, r)
  | ⟨_, .id s⟩ :: ⟨_, .sym ':'⟩ :: r => (externType n r).map fun (t, r) => (.named s t, r)
  | ⟨_, .id s⟩ :: r => some (.ident s, r)
  | _ => none

/-- `from as to`. -/
def includeItem (ts : Toks) : Option (IncludeItem × Toks) := do
  let (a, r) ← ident ts
  let r ← expect (.kw .as) r
  let (b, r) ← ident r
  pure ({ «from» := a, to := b }, r)

/-- A world item (`WorldItem::parse`). -/
def worldItem (n : Nat) (ts : Toks) : Option (WorldItem × Toks) :=
  match ts with
  | ⟨_, .kw .use⟩ :: _ => (use n ts).map fun (u, r) => (.use u, r)
  | ⟨ds, .kw .import⟩ :: r => do
    let (p, r) ← worldItemPath n r
    let r ← sym ';' r
    pure (.import_ ds p, r)
  | ⟨ds, .kw .export⟩ :: r => do
    let (p, r) ← worldItemPath n r
    let r ← sym ';' r
    pure (.export_ ds p, r)
  | ⟨ds, .kw .include⟩ :: r => do
    let (w, r) ← (match r with
      | ⟨_, .ppath _ _ _⟩ :: _ => (pkgPath r).map fun (p, r) => (WorldRef.package p, r)
      | ⟨_, .id s⟩ :: r => some (WorldRef.ident s, r)
      | _ => none)
    let (ws, r) ← (match r with
      | ⟨_, .kw .with⟩ :: r => do
        let r ← sym '{' r
        let (ws, r) ← delim includeItem '}' true n r
        let r ← sym '}' r
        pure (ws, r)
      | _ => some ([], r))
    let r ← sym ';' r
    pure (.include ds w ws, r)
  | _ => (itemTypeDecl n ts).map fun (d, r) => (.type d, r)

/-- A type statement (`TypeStatement::parse`). -/
def typeStatement (n : Nat) (ts : Toks) : Option (TypeStatement × Toks) :=
  match ts with
  | ⟨ds, .kw .interface⟩ :: r => do
    let (id, r) ← ident r
    let (items, r) ← interfaceBody n r
    pure (.interface ds id items, r)
  | ⟨ds, .kw .world⟩ :: r => do
    let (id, r) ← ident r
    let r ← sym '{' r
    let (items, r) ← delim (worldItem n) '}' false n r
    let r ← sym '}' r
    pure (.world ds id items, r)
  | _ => (typeDecl n ts).map fun (d, r) => (.type d, r)

/-- An identifier or a string. -/
def externName : Toks → Option (ExternName × Toks)
  | ⟨_, .id s⟩ :: r => some (.ident s, r)
  | ⟨_, .str s⟩ :: r => some (.string s, r)
  | _ => none

/-- Postfix accesses `.id` and `["name"]`, as many as follow. -/
def postfixes : Toks → Option (List Postfix × Toks)
  | ⟨_, .sym '.'⟩ :: ⟨_, .id s⟩ :: r => (postfixes r).map fun q => (.access s :: q.1, q.2)
  | ⟨_, .sym '.'⟩ :: _ => none
  | ⟨_, .sym '['⟩ :: ⟨_, .str s⟩ :: ⟨_, .sym ']'⟩ :: r =>
    (postfixes r).map fun q => (.namedAccess s :: q.1, q.2)
  | ⟨_, .sym '['⟩ :: _ => none
  | ts => some ([], ts)

mutual
/-- An expression (`Expr::parse`). -/
def expr : Nat → Toks → Option (Expr × Toks)
  | 0, _ => none
  | n + 1, ts => do
    let (p, r) ← primary n ts
    let (ps, r) ← postfixes r
    pure (.mk p ps, r)
/-- A primary expression (`PrimaryExpr::parse`). -/
def primary : Nat → Toks → Option (Primary × Toks)
  | 0, _ => none
  | n + 1, ts =>
    match ts with
    | ⟨_, .kw .new⟩ :: r => do
      let (pkg, r) ← pkgName r
      let r ← sym '{' r
      let (as, r) ← delim (arg n) '}' true n r
      let r ← sym '}' r
      pure (.new pkg as, r)
    | ⟨_, .sym '('⟩ :: r => do
      let (e, r) ← expr n r
      let r ← sym ')' r
      pure (.nested e, r)
    | ⟨_, .id s⟩ :: r => some (.ident s, r)
    | _ => none
/-- An instantiation argument (`InstantiationArgument::parse`). -/
def arg : Nat → Toks → Option (Arg × Toks)
  | 0, _ => none
  | n + 1, ts =>
    match ts with
    | ⟨_, .ellipsis⟩ :: r =>
      match r with
      | ⟨_, .sym ','⟩ :: _ | ⟨_, .sym '}'⟩ :: _ => some (.fill, r)
      | _ => (ident r).map fun (id, r) => (.spread id, r)
    | ⟨_, .id s⟩ :: ⟨_, .sym ':'⟩ :: r => (expr n r).map fun (e, r) => (.named (.ident s) e, r)
    | ⟨_, .str s⟩ :: ⟨_, .sym ':'⟩ :: r => (expr n r).map fun (e, r) => (.named (.string s) e, r)
    | ⟨_, .id s⟩ :: r => some (.inferred s, r)
    | _ => none
end

/-- The type of an import (`ImportType::parse`). -/
def importType (n : Nat) (ts : Toks) : Option (ImportType × Toks) :=
  match ts with
  | ⟨_, .kw .async⟩ :: _ | ⟨_, .kw .func⟩ :: _ => (funcType n ts).map fun (f, r) => (.func f, r)
  | ⟨_, .kw .interface⟩ :: _ => (inlineInterface n ts).map fun (i, r) => (.interface i, r)
  | ⟨_, .ppath _ _ _⟩ :: _ => (pkgPath ts).map fun (p, r) => (.package p, r)
  | ⟨_, .id s⟩ :: r => some (.ident s, r)
  | _ => none

/-- A statement (`Statement::parse`). -/
def statement (n : Nat) (ts : Toks) : Option (Statement × Toks) :=
  match ts with
  | ⟨ds, .kw .import⟩ :: r => do
    let (id, r) ← ident r
    let (nm, r) ← (match r with
      | ⟨_, .kw .as⟩ :: r => (externName r).map fun (x, r) => (some x, r)
      | _ => some (none, r))
    let r ← sym ':' r
    let (t, r) ← importType n r
    let r ← sym ';' r
    pure (.import_ ds id nm t, r)
  | ⟨ds, .kw .let⟩ :: r => do
    let (id, r) ← ident r
    let r ← sym '=' r
    let (e, r) ← expr n r
    let r ← sym ';' r
    pure (.let_ ds id e, r)
  | ⟨ds, .kw .export⟩ :: r => do
    let (e, r) ← expr n r
    let (o, r) ← (match r with
      | ⟨_, .ellipsis⟩ :: r => some (ExportOptions.spread, r)
      | ⟨_, .kw .as⟩ :: r => (externName r).map fun (x, r) => (ExportOptions.rename x, r)
      | _ => some (ExportOptions.none, r))
    let r ← sym ';' r
    pure (.export_ ds e o, r)
  | _ => (typeStatement n ts).map fun (s, r) => (.type s, r)

/-- Statements until the end of the tokens. -/
def statements (n : Nat) : Nat → Toks → Option (List Statement)
  | _, [] => some []
  | 0, _ :: _ => none
  | k + 1, ts@(_ :: _) => do
    let (s, r) ← statement n ts
    let ss ← statements n k r
    pure (s :: ss)

/-- A document: docs, `package name (targets path)?;`, statements. -/
def document (ts : Toks) : Option Document := do
  let n := 3 * ts.length + 3
  let r ← expect (.kw .package) ts
  let (pkg, r) ← pkgName r
  let (tg, r) ← (match r with
    | ⟨_, .kw .targets⟩ :: r => (pkgPath r).map fun (p, r) => (some p, r)
    | _ => some (none, r))
  let r ← sym ';' r
  let ss ← statements n n r
  pure { docs := docsOf ts, package := pkg, targets := tg, statements := ss }

end Parse

/-- Parse a WAC document from its text. -/
def parse (s : String) : Option Document := (lex s.toList).bind Parse.document

end Silmaril.Wasm.Wac.Text
