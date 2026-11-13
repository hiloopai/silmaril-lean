module

public import Silmaril.Wasm.Wit.Text.Print.Defs

/-!
# WIT text: the parser

A recursive-descent parser from tokens (`Silmaril.Wasm.Wit.Text.Lex`) to the AST of
`Silmaril.Wasm.Wit.Syntax`, following the grammar of `WIT.md` (component-model
`8505ba73dda2775b9438c0b8d169b96a556f864a`). Every parser takes fuel (`n`) and the
tokens, and returns the result and the remaining tokens; recursive parsers (types,
comma lists, item lists) spend one unit per step, and `document` starts with the number
of tokens plus one, which is always enough.

What the parser accepts beyond what the printer writes, and what it forgets:

* trailing commas in every comma list, `resource r {}` (as `resource r;`),
  `include p with {}` (as `include p;`), `result<_>` is rejected;
* doc comments before `use`, `include` and top-level `use` (dropped: the AST has no
  place for them);
* items and nested packages in any order at top level (the AST keeps the items of the
  main package and the nested packages apart, each in source order).

`docs` strips one leading space of every `///` line and joins the lines with newlines.
A file must start with its `package` declaration (after doc comments).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Text

open Silmaril.Wasm.Component.Wat (parseNat)

namespace Parse

/-- Consume one token. -/
def expect (t : Tok) : List Tok → Option (List Tok)
  | x :: r => if x = t then some r else none
  | [] => none

/-! ## Docs, versions, gates -/

/-- The leading doc lines. -/
def docLines : List Tok → List String × List Tok
  | .doc s :: r => (s :: (docLines r).1, (docLines r).2)
  | r => ([], r)

/-- Drop one leading space. -/
def stripSp : List Char → List Char
  | ' ' :: l => l
  | l => l

/-- The docs of doc lines. -/
def mkDocs : List String → Docs
  | [] => {}
  | ls => { contents := some (String.ofList (joinOn '\n' (ls.map fun s => stripSp s.toList))) }

/-- Leading doc comments. -/
def docs (ts : List Tok) : Docs × List Tok := (mkDocs (docLines ts).1, (docLines ts).2)

/-- Split at the first occurrence of a character. -/
def splitFirst (c : Char) : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | d :: ds => if d = c then ([], some ds) else (d :: (splitFirst c ds).1, (splitFirst c ds).2)

/-- The identifiers of a dot-separated part. -/
def dotIds (p : Option (List Char)) : List String :=
  match p with
  | none => []
  | some p => (splitOn '.' p).map String.ofList

/-- Read a version. -/
def parseVer (cs : List Char) : Option Version :=
  match splitOn '.' (splitFirst '-' (splitFirst '+' cs).1).1 with
  | [a, m, q] =>
    match parseNat a, parseNat m, parseNat q with
    | some a, some m, some q =>
      some { major := a, minor := m, patch := q,
             pre := dotIds (splitFirst '-' (splitFirst '+' cs).1).2,
             build := dotIds (splitFirst '+' cs).2 }
    | _, _, _ => none
  | _ => none

/-- A version token. -/
def version : List Tok → Option (Version × List Tok)
  | .num s :: r => (parseVer s.toList).map (·, r)
  | _ => none

mutual
/-- Gates: `@since(version = v)`, `@unstable(feature = f)`, `@deprecated(version = v)`. -/
def gates : List Tok → Option (List Gate × List Tok)
  | [] => some ([], [])
  | t :: r => if t = .sym '@' then gatesAt r else some ([], t :: r)
/-- Gates after an `@`. -/
def gatesAt : List Tok → Option (List Gate × List Tok)
  | .id "since" :: .sym '(' :: .id "version" :: .sym '=' :: .num v :: .sym ')' :: r =>
    match parseVer v.toList, gates r with
    | some v, some (gs, r) => some (.since v :: gs, r)
    | _, _ => none
  | .id "unstable" :: .sym '(' :: .id "feature" :: .sym '=' :: .id f :: .sym ')' :: r =>
    (gates r).map fun p => (.unstable f :: p.1, p.2)
  | .id "deprecated" :: .sym '(' :: .id "version" :: .sym '=' :: .num v :: .sym ')' :: r =>
    match parseVer v.toList, gates r with
    | some v, some (gs, r) => some (.deprecated v :: gs, r)
    | _, _ => none
  | _ => none
end

/-! ## Types -/

/-- The primitive type of a keyword. -/
def primOf : Kw → Option Ty
  | .bool => some .bool | .s8 => some .s8 | .s16 => some .s16 | .s32 => some .s32
  | .s64 => some .s64 | .u8 => some .u8 | .u16 => some .u16 | .u32 => some .u32
  | .u64 => some .u64 | .f32 => some .f32 | .f64 => some .f64 | .char => some .char
  | .string => some .string | .errorContext => some .errorContext
  | _ => none

/-- Consume `>` after a parsed value. -/
def close {α : Type} (f : α → Ty) : Option (α × List Tok) → Option (Ty × List Tok)
  | some (a, .sym '>' :: r) => some (f a, r)
  | _ => none

mutual
/-- A type. -/
def ty : Nat → List Tok → Option (Ty × List Tok)
  | 0, _ => none
  | n + 1, ts =>
    match ts with
    | .id s :: r => some (.named s, r)
    | .kw .list :: .sym '<' :: r =>
      match ty n r with
      | some (t, .sym '>' :: r) => some (.list t, r)
      | some (t, .sym ',' :: .num m :: .sym '>' :: r) =>
        (parseNat m.toList).map fun m => (.fixedList t m, r)
      | _ => none
    | .kw .map :: .sym '<' :: r =>
      match ty n r with
      | some (a, .sym ',' :: r) => close (Ty.map a) (ty n r)
      | _ => none
    | .kw .tuple :: .sym '<' :: r => close Ty.tuple (tys n r)
    | .kw .option :: .sym '<' :: r => close Ty.option (ty n r)
    | .kw .result :: r =>
      if r.head? = some (.sym '<') then
        if r.tail.head? = some (.kw .underscore) then
          match r.tail.tail with
          | .sym ',' :: r => close (fun e => Ty.result none (some e)) (ty n r)
          | _ => none
        else
          match ty n r.tail with
          | some (t, .sym '>' :: r) => some (.result (some t) none, r)
          | some (t, .sym ',' :: r) => close (fun e => Ty.result (some t) (some e)) (ty n r)
          | _ => none
      else some (.result none none, r)
    | .kw .own :: .sym '<' :: .id s :: .sym '>' :: r => some (.own s, r)
    | .kw .borrow :: .sym '<' :: .id s :: .sym '>' :: r => some (.borrow s, r)
    | .kw .future :: r =>
      if r.head? = some (.sym '<') then close (fun t => Ty.future (some t)) (ty n r.tail)
      else some (.future none, r)
    | .kw .stream :: r =>
      if r.head? = some (.sym '<') then close (fun t => Ty.stream (some t)) (ty n r.tail)
      else some (.stream none, r)
    | .kw w :: r => (primOf w).map (·, r)
    | _ => none
/-- Types separated by commas, up to `>`. -/
def tys : Nat → List Tok → Option (List Ty × List Tok)
  | 0, _ => none
  | n + 1, ts =>
    if ts.head? = some (.sym '>') then some ([], ts)
    else
      match ty n ts with
      | some (t, r) =>
        if r.head? = some (.sym ',') then (tys n r.tail).map fun p => (t :: p.1, p.2)
        else some ([t], r)
      | none => none
end

/-! ## Lists -/

/-- Items separated (and optionally terminated) by commas, up to `close`. -/
def sepBy {α : Type} (p : Nat → List Tok → Option (α × List Tok)) (cl : Tok) :
    Nat → List Tok → Option (List α × List Tok)
  | 0, _ => none
  | n + 1, ts =>
    if ts.head? = some cl then some ([], ts)
    else
      match p n ts with
      | some (a, r) =>
        if r.head? = some (.sym ',') then (sepBy p cl n r.tail).map fun q => (a :: q.1, q.2)
        else some ([a], r)
      | none => none

/-- Items up to `}`. -/
def many {α : Type} (p : Nat → List Tok → Option (α × List Tok)) :
    Nat → List Tok → Option (List α × List Tok)
  | 0, _ => none
  | n + 1, ts =>
    if ts.head? = some (.sym '}') ∨ ts = [] then some ([], ts)
    else
      match p n ts with
      | some (a, r) => (many p n r).map fun q => (a :: q.1, q.2)
      | none => none

/-- `p` followed by token `t`. -/
def andThen {α : Type} (t : Tok) : Option (α × List Tok) → Option (α × List Tok)
  | some (a, r) => (expect t r).map (a, ·)
  | none => none

/-! ## Functions and type definitions -/

/-- A name. -/
def name : List Tok → Option (Name × List Tok)
  | .id s :: r => some (s, r)
  | _ => none

/-- `name: type`. -/
def param (n : Nat) : List Tok → Option ((Name × Ty) × List Tok)
  | .id s :: .sym ':' :: r => (ty n r).map fun p => ((s, p.1), p.2)
  | _ => none

/-- `(params)` and an optional `-> result`. -/
def sig (n : Nat) : List Tok → Option ((List (Name × Ty) × Option Ty) × List Tok)
  | .sym '(' :: r =>
    match sepBy param (.sym ')') n r with
    | some (ps, .sym ')' :: .arrow :: r) => (ty n r).map fun p => ((ps, some p.1), p.2)
    | some (ps, .sym ')' :: r) => some ((ps, none), r)
    | _ => none
  | _ => none

/-- `async? func(params) -> result`. -/
def func (n : Nat) : List Tok → Option (Func × List Tok)
  | .kw .async :: .kw .func :: r =>
    (sig n r).map fun p => ({ params := p.1.1, result := p.1.2, async := true }, p.2)
  | .kw .func :: r => (sig n r).map fun p => ({ params := p.1.1, result := p.1.2 }, p.2)
  | _ => none

/-- A record field. -/
def field (n : Nat) (ts : List Tok) : Option (Field × List Tok) :=
  match (docs ts).2 with
  | .id s :: .sym ':' :: r => (ty n r).map fun p => ({ name := s, ty := p.1, docs := (docs ts).1 }, p.2)
  | _ => none

/-- A variant case. -/
def case (n : Nat) (ts : List Tok) : Option (Case × List Tok) :=
  match (docs ts).2 with
  | .id s :: r =>
    if r.head? = some (.sym '(') then
      andThen (.sym ')') ((ty n r.tail).map fun p =>
        ({ name := s, ty := some p.1, docs := (docs ts).1 }, p.2))
    else some ({ name := s, docs := (docs ts).1 }, r)
  | _ => none

/-- An enum case or a flag. -/
def label (_n : Nat) (ts : List Tok) : Option (Label × List Tok) :=
  match (docs ts).2 with
  | .id s :: r => some ({ name := s, docs := (docs ts).1 }, r)
  | _ => none

/-- A function of a resource block. -/
def resFunc (n : Nat) (ts : List Tok) : Option (ResourceFunc × List Tok) :=
  match gates (docs ts).2 with
  | some (gs, .kw .ctor :: r) =>
    andThen (.sym ';') ((sig n r).map fun p =>
      ({ kind := .ctor, func := { params := p.1.1, result := p.1.2 }, docs := (docs ts).1,
         gates := gs }, p.2))
  | some (gs, .id s :: .sym ':' :: .kw .static :: r) =>
    andThen (.sym ';') ((func n r).map fun p =>
      ({ kind := .static s, func := p.1, docs := (docs ts).1, gates := gs }, p.2))
  | some (gs, .id s :: .sym ':' :: r) =>
    andThen (.sym ';') ((func n r).map fun p =>
      ({ kind := .method s, func := p.1, docs := (docs ts).1, gates := gs }, p.2))
  | _ => none

/-- A braced body `{ items }` read by `body`, then `}`. -/
def braced {α : Type} (body : List Tok → Option (α × List Tok)) :
    List Tok → Option (α × List Tok)
  | .sym '{' :: r => andThen (.sym '}') (body r)
  | _ => none

/-- A type definition after its docs and gates. -/
def typeDefBody (n : Nat) : List Tok → Option ((Name × TypeDefKind) × List Tok)
  | .kw .type :: .id s :: .sym '=' :: r =>
    andThen (.sym ';') ((ty n r).map fun p => ((s, .alias p.1), p.2))
  | .kw .record :: .id s :: r =>
    (braced (sepBy field (.sym '}') n) r).map fun p => ((s, .record p.1), p.2)
  | .kw .variant :: .id s :: r =>
    (braced (sepBy case (.sym '}') n) r).map fun p => ((s, .variant p.1), p.2)
  | .kw .enum :: .id s :: r =>
    (braced (sepBy label (.sym '}') n) r).map fun p => ((s, .enum p.1), p.2)
  | .kw .flags :: .id s :: r =>
    (braced (sepBy label (.sym '}') n) r).map fun p => ((s, .flags p.1), p.2)
  | .kw .resource :: .id s :: r =>
    if r.head? = some (.sym ';') then some ((s, .resource []), r.tail)
    else (braced (many resFunc n) r).map fun p => ((s, .resource p.1), p.2)
  | _ => none

/-! ## Paths and `use` -/

/-- `@version`, if present. -/
def optVersion (ts : List Tok) : Option (Option Version × List Tok) :=
  if ts.head? = some (.sym '@') then (version ts.tail).map fun p => (some p.1, p.2)
  else some (none, ts)

/-- A package name `ns:name@version`. -/
def pkgName : List Tok → Option (PackageName × List Tok)
  | .id a :: .sym ':' :: .id b :: r =>
    (optVersion r).map fun p => ({ ns := a, name := b, version := p.1 }, p.2)
  | _ => none

/-- The rest of a foreign path after `ns:`. -/
def foreign (a : Name) : List Tok → Option (UsePath × List Tok)
  | .id b :: .sym '/' :: .id c :: r =>
    (optVersion r).map fun p => (.foreign { ns := a, name := b, version := p.1 } c, p.2)
  | _ => none

/-- A use path. -/
def path : List Tok → Option (UsePath × List Tok)
  | .id a :: r => if r.head? = some (.sym ':') then foreign a r.tail else some (.local a, r)
  | _ => none

/-- `name` or `name as alias`. -/
def useName (_n : Nat) : List Tok → Option (UseName × List Tok)
  | .id a :: r =>
    match r with
    | .kw .as :: .id b :: r => some ({ name := a, as := some b }, r)
    | r => some ({ name := a }, r)
  | _ => none

/-- `path.{names};` after `use`. -/
def useBody (n : Nat) (gs : List Gate) (ts : List Tok) : Option (Use × List Tok) :=
  match path ts with
  | some (p, .sym '.' :: r) =>
    andThen (.sym ';') ((braced (sepBy useName (.sym '}') n) r).map fun q =>
      ({ path := p, names := q.1, gates := gs }, q.2))
  | _ => none

/-- A named function `name: func(…);` after its docs and gates. -/
def funcDef (n : Nat) (d : Docs) (gs : List Gate) : List Tok → Option (FuncDef × List Tok)
  | .id s :: .sym ':' :: r =>
    andThen (.sym ';') ((func n r).map fun p => ({ name := s, func := p.1, docs := d, gates := gs }, p.2))
  | _ => none

/-- An interface item. -/
def ifaceItem (n : Nat) (ts : List Tok) : Option (IfaceItem × List Tok) :=
  match gates (docs ts).2 with
  | some (gs, r) =>
    if r.head? = some (.kw .use) then (useBody n gs r.tail).map fun p => (.use p.1, p.2)
    else
      match r with
      | .id s :: r => (funcDef n (docs ts).1 gs (.id s :: r)).map fun p => (.func p.1, p.2)
      | r => (typeDefBody n r).map fun p =>
        (.type { name := p.1.1, kind := p.1.2, docs := (docs ts).1, gates := gs }, p.2)
  | none => none

/-! ## Worlds and packages -/

/-- What a world imports or exports. -/
def extern (n : Nat) : List Tok → Option (Extern × List Tok)
  | .id a :: .sym ':' :: .kw .interface :: r =>
    (braced (many ifaceItem n) r).map fun p => (.iface a p.1, p.2)
  | .id a :: .sym ':' :: .id b :: r => andThen (.sym ';') ((foreign a (.id b :: r)).map
      fun p => (.path p.1, p.2))
  | .id a :: .sym ':' :: r => andThen (.sym ';') ((func n r).map fun p => (.func a p.1, p.2))
  | .id a :: .sym ';' :: r => some (.path (.local a), r)
  | _ => none

/-- `a as b`. -/
def includeName (_n : Nat) : List Tok → Option (IncludeName × List Tok)
  | .id a :: .kw .as :: .id b :: r => some ({ name := a, as := b }, r)
  | _ => none

/-- `path;` or `path with { names }` after `include`. -/
def includeBody (n : Nat) (gs : List Gate) (ts : List Tok) : Option (Include × List Tok) :=
  match path ts with
  | some (p, .sym ';' :: r) => some ({ path := p, gates := gs }, r)
  | some (p, .kw .with :: r) =>
    (braced (sepBy includeName (.sym '}') n) r).map fun q =>
      ({ path := p, names := q.1, gates := gs }, q.2)
  | _ => none

/-- A world item. -/
def worldItem (n : Nat) (ts : List Tok) : Option (WorldItem × List Tok) :=
  match gates (docs ts).2 with
  | some (gs, r) =>
    if r.head? = some (.kw .import) then (extern n r.tail).map fun p =>
      (.import { ext := p.1, docs := (docs ts).1, gates := gs }, p.2)
    else if r.head? = some (.kw .export) then (extern n r.tail).map fun p =>
      (.export { ext := p.1, docs := (docs ts).1, gates := gs }, p.2)
    else if r.head? = some (.kw .use) then (useBody n gs r.tail).map fun p => (.use p.1, p.2)
    else if r.head? = some (.kw .include) then
      (includeBody n gs r.tail).map fun p => (.include p.1, p.2)
    else (typeDefBody n r).map fun p =>
      (.type { name := p.1.1, kind := p.1.2, docs := (docs ts).1, gates := gs }, p.2)
  | none => none

/-- `use path as name;` after `use`. -/
def topUseBody (gs : List Gate) (ts : List Tok) : Option (TopUse × List Tok) :=
  match path ts with
  | some (p, .sym ';' :: r) => some ({ path := p, gates := gs }, r)
  | some (p, .kw .as :: .id a :: .sym ';' :: r) => some ({ path := p, as := some a, gates := gs }, r)
  | _ => none

/-- A package item. -/
def packageItem (n : Nat) (ts : List Tok) : Option (PackageItem × List Tok) :=
  match gates (docs ts).2 with
  | some (gs, .kw .interface :: .id s :: r) => (braced (many ifaceItem n) r).map fun p =>
      (.iface { name := s, items := p.1, docs := (docs ts).1, gates := gs }, p.2)
  | some (gs, .kw .world :: .id s :: r) => (braced (many worldItem n) r).map fun p =>
      (.world { name := s, items := p.1, docs := (docs ts).1, gates := gs }, p.2)
  | some (gs, .kw .use :: r) => (topUseBody gs r).map fun p => (.use p.1, p.2)
  | _ => none

/-- A top-level item or a nested package. -/
def topItem (n : Nat) (ts : List Tok) : Option ((PackageItem ⊕ Package) × List Tok) :=
  if (docs ts).2.head? = some (.kw .package) then
    match pkgName (docs ts).2.tail with
    | some (nm, r) => (braced (many packageItem n) r).map fun p =>
        (.inr { name := nm, items := p.1, docs := (docs ts).1 }, p.2)
    | none => none
  else (packageItem n ts).map fun p => (.inl p.1, p.2)

/-- The items of the main package. -/
def lefts {α β : Type} : List (α ⊕ β) → List α
  | [] => []
  | .inl a :: xs => a :: lefts xs
  | .inr _ :: xs => lefts xs

/-- The nested packages. -/
def rights {α β : Type} : List (α ⊕ β) → List β
  | [] => []
  | .inl _ :: xs => rights xs
  | .inr b :: xs => b :: rights xs

/-- A document. -/
def document (ts : List Tok) : Option Document :=
  match (docs ts).2 with
  | .kw .package :: r =>
    match pkgName r with
    | some (nm, .sym ';' :: r) =>
      match many topItem (ts.length + 1) r with
      | some (xs, []) =>
        some { main := { name := nm, items := lefts xs, docs := (docs ts).1 },
               nested := rights xs }
      | _ => none
    | _ => none
  | _ => none

end Parse

/-- Parse a WIT document. -/
def parse (s : String) : Option Document := (lex s.toList).bind Parse.document

end Silmaril.Wasm.Wit.Text
