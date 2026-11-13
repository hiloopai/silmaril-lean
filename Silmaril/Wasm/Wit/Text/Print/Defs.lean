module

public import Silmaril.Wasm.Wit.Syntax.Defs
public import Silmaril.Wasm.Wit.Text.Lex.Defs
public import Silmaril.Wasm.Component.Wat.Defs

/-!
# WIT text: the printer

The layout (`List PTok`) of every syntactic category of `Silmaril.Wasm.Wit.Syntax`, in
the concrete syntax of `WIT.md`:

* doc comments as `///` lines (one per line of `Docs.contents`, after one space);
* gates `@since(version = v)`, `@unstable(feature = f)`, `@deprecated(version = v)`,
  each on its own line, after the doc comments and before the item;
* records, variants, enums and flags with one member per line and a trailing comma;
  parameters, tuple members, `use` names and `include` names on one line;
* `resource r;` for a resource without functions;
* `include p;` for an include without renamings;
* a document as `package ns:name@v;`, the items, then the nested
  `package ns:name { … }` blocks.

Versions are printed as one number literal (`verChars`); natural numbers by
`Silmaril.Wasm.Component.Wat.natChars`. `printable` says which documents the printer can
spell: identifiers are `idOk` (ASCII kebab-like words) and versions are `verOk`
(non-empty pre-release and build identifiers of letters, digits and `-`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Text

open Silmaril.Wasm.Component.Wat (natChars)

/-! ## Splitting and joining -/

/-- Join pieces with a separator character. -/
def joinOn (c : Char) : List (List Char) → List Char
  | [] => []
  | [x] => x
  | x :: xs => x ++ c :: joinOn c xs

/-- Split at every occurrence of a character (`splitOn c [] = [[]]`). -/
def splitOn (c : Char) : List Char → List (List Char)
  | [] => [[]]
  | d :: ds =>
    if d = c then [] :: splitOn c ds
    else match splitOn c ds with
      | w :: ws => (d :: w) :: ws
      | [] => [[d]]

/-! ## Versions -/

/-- The characters of a version: `major.minor.patch(-pre)?(+build)?`. -/
def verChars (v : Version) : List Char :=
  natChars v.major ++ '.' :: natChars v.minor ++ '.' :: natChars v.patch ++
    (if v.pre = [] then [] else '-' :: joinOn '.' (v.pre.map String.toList)) ++
    (if v.build = [] then [] else '+' :: joinOn '.' (v.build.map String.toList))

/-- The token of a version. -/
def verTok (v : Version) : Tok := .num (String.ofList (verChars v))

/-- A version the printer can spell. -/
def verOk (v : Version) : Bool :=
  (v.pre ++ v.build).all fun s => !s.toList.isEmpty && s.toList.all wordCont

/-! ## Token helpers -/

/-- A keyword. -/
abbrev k (w : Kw) : PTok := (.kw w, .none)
/-- A symbol. -/
abbrev y (c : Char) : PTok := (.sym c, .none)
/-- A symbol followed by a space. -/
abbrev ys (c : Char) : PTok := (.sym c, .sp)
/-- A symbol at the end of a line. -/
abbrev yn (c : Char) : PTok := (.sym c, .nl)
/-- An identifier. -/
abbrev i (n : Name) : PTok := (.id n, .none)

/-! ## Docs and gates -/

/-- Doc comments: one `///` line per line of the contents, after one space. -/
def prDocs (d : Docs) : List PTok :=
  match d.contents with
  | none => []
  | some s => (splitOn '\n' s.toList).map fun l => (.doc (String.ofList (' ' :: l)), .nl)

/-- A gate, on its own line. -/
def prGate : Gate → List PTok
  | .since v => [y '@', i "since", y '(', (.id "version", .sp), ys '=', (verTok v, .none), yn ')']
  | .unstable f => [y '@', i "unstable", y '(', (.id "feature", .sp), ys '=', i f, yn ')']
  | .deprecated v =>
    [y '@', i "deprecated", y '(', (.id "version", .sp), ys '=', (verTok v, .none), yn ')']

/-- Gates. -/
def prGates (gs : List Gate) : List PTok := gs.flatMap prGate

/-! ## Types -/

/-- The keyword of a primitive type. -/
def primKw : Ty → Option Kw
  | .bool => some .bool | .s8 => some .s8 | .s16 => some .s16 | .s32 => some .s32
  | .s64 => some .s64 | .u8 => some .u8 | .u16 => some .u16 | .u32 => some .u32
  | .u64 => some .u64 | .f32 => some .f32 | .f64 => some .f64 | .char => some .char
  | .string => some .string | .errorContext => some .errorContext
  | _ => none

mutual
/-- A type. -/
def prTy : Ty → List PTok
  | .bool => [k .bool] | .s8 => [k .s8] | .s16 => [k .s16] | .s32 => [k .s32]
  | .s64 => [k .s64] | .u8 => [k .u8] | .u16 => [k .u16] | .u32 => [k .u32]
  | .u64 => [k .u64] | .f32 => [k .f32] | .f64 => [k .f64] | .char => [k .char]
  | .string => [k .string] | .errorContext => [k .errorContext]
  | .named n => [i n]
  | .list t => [k .list, y '<'] ++ prTy t ++ [y '>']
  | .fixedList t n => [k .list, y '<'] ++ prTy t ++
      [ys ',', (.num (String.ofList (natChars n)), .none), y '>']
  | .map a b => [k .map, y '<'] ++ prTy a ++ [ys ','] ++ prTy b ++ [y '>']
  | .tuple ts => [k .tuple, y '<'] ++ prTys ts ++ [y '>']
  | .option t => [k .option, y '<'] ++ prTy t ++ [y '>']
  | .result ok err => k .result ::
      match ok, err with
      | none, none => []
      | some _, none => [y '<'] ++ prOpt ok ++ [y '>']
      | none, some _ => [y '<', k .underscore, ys ','] ++ prOpt err ++ [y '>']
      | some _, some _ => [y '<'] ++ prOpt ok ++ [ys ','] ++ prOpt err ++ [y '>']
  | .own r => [k .own, y '<', i r, y '>']
  | .borrow r => [k .borrow, y '<', i r, y '>']
  | .future t => k .future :: prArg t
  | .stream t => k .stream :: prArg t
/-- An optional type: nothing or the type. -/
def prOpt : Option Ty → List PTok
  | none => []
  | some t => prTy t
/-- The optional argument of `future` and `stream`. -/
def prArg : Option Ty → List PTok
  | none => []
  | some t => [y '<'] ++ prTy t ++ [y '>']
/-- Types separated by commas. -/
def prTys : List Ty → List PTok
  | [] => []
  | [t] => prTy t
  | t :: ts => prTy t ++ [ys ','] ++ prTys ts
end

/-! ## Functions and type definitions -/

/-- Items separated by `, `. -/
def prSep {α : Type} (pr : α → List PTok) : List α → List PTok
  | [] => []
  | [x] => pr x
  | x :: xs => pr x ++ [ys ','] ++ prSep pr xs

/-- Items each followed by `,` and a new line. -/
def prTerm {α : Type} (pr : α → List PTok) : List α → List PTok
  | [] => []
  | x :: xs => pr x ++ [yn ','] ++ prTerm pr xs

/-- A parameter `name: type`. -/
def prParam (p : Name × Ty) : List PTok := [i p.1, ys ':'] ++ prTy p.2

/-- `(params)` and an optional `-> result`. -/
def prSig (params : List (Name × Ty)) (result : Option Ty) : List PTok :=
  [y '('] ++ prSep prParam params ++
    match result with
    | none => [y ')']
    | some t => [ys ')', (.arrow, .sp)] ++ prTy t

/-- A function type `async? func(params) -> result`. -/
def prFunc (f : Func) : List PTok :=
  (if f.async then [k .async] else []) ++ k .func :: prSig f.params f.result

/-- A record field. -/
def prField (f : Field) : List PTok := prDocs f.docs ++ [i f.name, ys ':'] ++ prTy f.ty

/-- A variant case. -/
def prCase (c : Case) : List PTok :=
  prDocs c.docs ++ i c.name ::
    match c.ty with
    | none => []
    | some t => [y '('] ++ prTy t ++ [y ')']

/-- An enum case or a flag. -/
def prLabel (l : Label) : List PTok := prDocs l.docs ++ [i l.name]

/-- A function of a resource block. -/
def prResFunc (f : ResourceFunc) : List PTok :=
  prDocs f.docs ++ prGates f.gates ++
    match f.kind with
    | .ctor => k .ctor :: prSig f.func.params f.func.result ++ [yn ';']
    | .method n => [i n, ys ':'] ++ prFunc f.func ++ [yn ';']
    | .static n => [i n, ys ':', k .static] ++ prFunc f.func ++ [yn ';']

/-- A type definition (without docs and gates). -/
def prTypeDefBody (name : Name) : TypeDefKind → List PTok
  | .alias t => [k .type, i name, (.sym '=', .sp)] ++ prTy t ++ [yn ';']
  | .record fs => [k .record, i name, yn '{'] ++ prTerm prField fs ++ [yn '}']
  | .variant cs => [k .variant, i name, yn '{'] ++ prTerm prCase cs ++ [yn '}']
  | .enum ls => [k .enum, i name, yn '{'] ++ prTerm prLabel ls ++ [yn '}']
  | .flags ls => [k .flags, i name, yn '{'] ++ prTerm prLabel ls ++ [yn '}']
  | .resource [] => [k .resource, i name, yn ';']
  | .resource fs => [k .resource, i name, yn '{'] ++ fs.flatMap prResFunc ++ [yn '}']

/-- A type definition. -/
def prTypeDef (d : TypeDef) : List PTok :=
  prDocs d.docs ++ prGates d.gates ++ prTypeDefBody d.name d.kind

/-! ## Paths and `use` -/

/-- A package name `ns:name@version`. -/
def prPkgName (p : PackageName) : List PTok :=
  [i p.ns, y ':', i p.name] ++
    match p.version with
    | none => []
    | some v => [y '@', (verTok v, .none)]

/-- A use path: `name` or `ns:pkg/name@version`. -/
def prPath : UsePath → List PTok
  | .local n => [i n]
  | .foreign p n => [i p.ns, y ':', i p.name, y '/', i n] ++
    match p.version with
    | none => []
    | some v => [y '@', (verTok v, .none)]

/-- `name` or `name as alias`. -/
def prUseName (u : UseName) : List PTok :=
  match u.as with
  | none => [i u.name]
  | some a => [i u.name, k .as, i a]

/-- `use path.{names};` (with its gates). -/
def prUse (u : Use) : List PTok :=
  prGates u.gates ++ [k .use] ++ prPath u.path ++ [y '.', y '{'] ++
    prSep prUseName u.names ++ [y '}', yn ';']

/-- A named function `name: func(…);`. -/
def prFuncDef (f : FuncDef) : List PTok :=
  prDocs f.docs ++ prGates f.gates ++ [i f.name, ys ':'] ++ prFunc f.func ++ [yn ';']

/-- An interface item. -/
def prIfaceItem : IfaceItem → List PTok
  | .type d => prTypeDef d
  | .use u => prUse u
  | .func f => prFuncDef f

/-- Interface items. -/
def prIfaceItems (is : List IfaceItem) : List PTok := is.flatMap prIfaceItem

/-! ## Worlds and packages -/

/-- What a world imports or exports. -/
def prExtern : Extern → List PTok
  | .func n f => [i n, ys ':'] ++ prFunc f ++ [yn ';']
  | .iface n is => [i n, ys ':', k .interface, yn '{'] ++ prIfaceItems is ++ [yn '}']
  | .path p => prPath p ++ [yn ';']

/-- `a as b`. -/
def prIncludeName (n : IncludeName) : List PTok := [i n.name, k .as, i n.as]

/-- `include path;` or `include path with { a as b, … }`. -/
def prInclude (n : Include) : List PTok :=
  prGates n.gates ++ k .include :: prPath n.path ++
    match n.names with
    | [] => [yn ';']
    | ns => [k .with, y '{'] ++ prSep prIncludeName ns ++ [yn '}']

/-- A world item. -/
def prWorldItem : WorldItem → List PTok
  | .import e => prDocs e.docs ++ prGates e.gates ++ k .import :: prExtern e.ext
  | .export e => prDocs e.docs ++ prGates e.gates ++ k .export :: prExtern e.ext
  | .use u => prUse u
  | .type d => prTypeDef d
  | .include n => prInclude n

/-- `interface name { items }`. -/
def prInterface (n : Interface) : List PTok :=
  prDocs n.docs ++ prGates n.gates ++ [k .interface, i n.name, yn '{'] ++
    prIfaceItems n.items ++ [yn '}']

/-- `world name { items }`. -/
def prWorld (w : World) : List PTok :=
  prDocs w.docs ++ prGates w.gates ++ [k .world, i w.name, yn '{'] ++
    w.items.flatMap prWorldItem ++ [yn '}']

/-- `use path as name;` -/
def prTopUse (u : TopUse) : List PTok :=
  prGates u.gates ++ k .use :: prPath u.path ++
    match u.as with
    | none => [yn ';']
    | some a => [k .as, i a, yn ';']

/-- A package item. -/
def prPackageItem : PackageItem → List PTok
  | .iface n => prInterface n
  | .world w => prWorld w
  | .use u => prTopUse u

/-- A nested package `package ns:name { items }`. -/
def prNested (p : Package) : List PTok :=
  prDocs p.docs ++ k .package :: prPkgName p.name ++ [yn '{'] ++
    p.items.flatMap prPackageItem ++ [yn '}']

/-- A document: `package ns:name;`, the items, the nested packages. -/
def prDocument (d : Document) : List PTok :=
  prDocs d.main.docs ++ k .package :: prPkgName d.main.name ++ [yn ';'] ++
    d.main.items.flatMap prPackageItem ++ d.nested.flatMap prNested

/-! ## What the printer can spell -/

/-- A printable gate. -/
def gateOk : Gate → Bool
  | .since v | .deprecated v => verOk v
  | .unstable f => idOk f

mutual
/-- A printable type: its names are `idOk`. -/
def tyOk : Ty → Bool
  | .named n | .own n | .borrow n => idOk n
  | .list t | .fixedList t _ | .option t => tyOk t
  | .map a b => tyOk a && tyOk b
  | .tuple ts => tysOk ts
  | .result a b => optOk a && optOk b
  | .future t | .stream t => optOk t
  | _ => true
/-- `tyOk` of an optional type. -/
def optOk : Option Ty → Bool
  | none => true
  | some t => tyOk t
/-- `tyOk` of every type. -/
def tysOk : List Ty → Bool
  | [] => true
  | t :: ts => tyOk t && tysOk ts
end

/-- A printable function type. -/
def funcOk (f : Func) : Bool := f.params.all (fun p => idOk p.1 && tyOk p.2) && optOk f.result

/-- A printable resource function. -/
def resFuncOk (f : ResourceFunc) : Bool :=
  f.gates.all gateOk && funcOk f.func &&
    match f.kind with
    | .ctor => true
    | .method n | .static n => idOk n

/-- A printable type definition body. -/
def typeDefKindOk : TypeDefKind → Bool
  | .alias t => tyOk t
  | .record fs => fs.all fun f => idOk f.name && tyOk f.ty
  | .variant cs => cs.all fun c => idOk c.name && optOk c.ty
  | .enum ls | .flags ls => ls.all fun l => idOk l.name
  | .resource fs => fs.all resFuncOk

/-- A printable type definition. -/
def typeDefOk (d : TypeDef) : Bool := idOk d.name && d.gates.all gateOk && typeDefKindOk d.kind

/-- A printable package name. -/
def pkgNameOk (p : PackageName) : Bool :=
  idOk p.ns && idOk p.name && match p.version with
    | none => true
    | some v => verOk v

/-- A printable use path. -/
def pathOk : UsePath → Bool
  | .local n => idOk n
  | .foreign p n => pkgNameOk p && idOk n

/-- A printable `use`. -/
def useOk (u : Use) : Bool :=
  u.gates.all gateOk && pathOk u.path &&
    u.names.all fun n => idOk n.name && match n.as with
      | none => true
      | some a => idOk a

/-- A printable interface item. -/
def ifaceItemOk : IfaceItem → Bool
  | .type d => typeDefOk d
  | .use u => useOk u
  | .func f => idOk f.name && f.gates.all gateOk && funcOk f.func

/-- A printable import or export. -/
def externOk : Extern → Bool
  | .func n f => idOk n && funcOk f
  | .iface n is => idOk n && is.all ifaceItemOk
  | .path p => pathOk p

/-- A printable include. -/
def includeOk (n : Include) : Bool :=
  n.gates.all gateOk && pathOk n.path && n.names.all fun m => idOk m.name && idOk m.as

/-- A printable world item. -/
def worldItemOk : WorldItem → Bool
  | .import e | .export e => e.gates.all gateOk && externOk e.ext
  | .use u => useOk u
  | .type d => typeDefOk d
  | .include n => includeOk n

/-- A printable package item. -/
def packageItemOk : PackageItem → Bool
  | .iface n => idOk n.name && n.gates.all gateOk && n.items.all ifaceItemOk
  | .world w => idOk w.name && w.gates.all gateOk && w.items.all worldItemOk
  | .use u => u.gates.all gateOk && pathOk u.path && match u.as with
    | none => true
    | some a => idOk a

/-- A printable package. -/
def packageOk (p : Package) : Bool := pkgNameOk p.name && p.items.all packageItemOk

/-- A document the printer can spell: identifiers are `idOk` and versions `verOk`.
Docs need nothing. -/
def printable (d : Document) : Bool := packageOk d.main && d.nested.all packageOk

/-! ## The normal form -/

/-- A resource function in normal form: a constructor is not `async` (the text has no
`async constructor`). -/
def ResourceFunc.norm (f : ResourceFunc) : ResourceFunc :=
  match f.kind with
  | .ctor => { f with func := { f.func with async := false } }
  | _ => f

/-- A type definition body in normal form. -/
def TypeDefKind.norm : TypeDefKind → TypeDefKind
  | .resource fs => .resource (fs.map ResourceFunc.norm)
  | k => k

/-- A type definition in normal form. -/
def TypeDef.norm (d : TypeDef) : TypeDef := { d with kind := TypeDefKind.norm d.kind }

/-- An interface item in normal form. -/
def IfaceItem.norm : IfaceItem → IfaceItem
  | .type d => .type (TypeDef.norm d)
  | i => i

/-- An import or export in normal form. -/
def Extern.norm : Extern → Extern
  | .iface n is => .iface n (is.map IfaceItem.norm)
  | e => e

/-- A world item in normal form. -/
def WorldItem.norm : WorldItem → WorldItem
  | .import e => .import { e with ext := Extern.norm e.ext }
  | .export e => .export { e with ext := Extern.norm e.ext }
  | .type d => .type (TypeDef.norm d)
  | i => i

/-- A package item in normal form. -/
def PackageItem.norm : PackageItem → PackageItem
  | .iface n => .iface { n with items := n.items.map IfaceItem.norm }
  | .world w => .world { w with items := w.items.map WorldItem.norm }
  | i => i

/-- A package in normal form. -/
def Package.norm (p : Package) : Package := { p with items := p.items.map PackageItem.norm }

/-- The normal form of a document: what `parse (print d)` gives. The only
information the text loses is `async` on constructors. -/
def Document.norm (d : Document) : Document :=
  { main := Package.norm d.main, nested := d.nested.map Package.norm }

/-- Print a document. -/
def print (d : Document) : String := String.ofList (render 0 (prDocument d))

end Silmaril.Wasm.Wit.Text
