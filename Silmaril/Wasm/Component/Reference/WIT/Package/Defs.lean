module

public import Silmaril.Wasm.Component.Reference.WIT.Defs

/-!
# WIT packages, interfaces and worlds

WIT source-level declarations as Lean data, following the pinned component-model design
`WIT.md` (revision `a25fc0b`): §Package Names, §WIT Interfaces, §WIT Worlds (including
§Union of Worlds with `include`), §WIT Packages and `use` (including §Top-level `use`),
§WIT Functions, §WIT Types, §WIT Identifiers, §Lexical structure (§Keywords, §Feature Gates),
§Item: `world` / `include` / `interface` / `use` / type items / `resource`, §Types, §Handles and
§Name resolution. Label spelling and name uniqueness follow `Explainer.md` §Import and Export
Definitions (the `label`, `words` and `interfacename` productions) and §Name Uniqueness.

Contents:
* identifiers: the kebab-case `label` and `words` productions as decidable predicates
  (`IsLabel`, `IsWords`) over a structural fragment split, the WIT keyword list, and the
  strong-uniqueness canonical keys (`NameKey`);
* package names with 🪺 nested namespaces/packages and SemVer 2.0 versions, use paths,
  feature gates (`@since`, `@unstable`, `@deprecated`) as data, type definitions (alias, record,
  variant, enum, flags, resource with constructor/methods/static functions), interface items
  (`use`, types, functions, with the `async` marker of `FuncType.async_`), worlds (imports and
  exports of interfaces, functions, inline interfaces and 🏷️ `name: path` imports, `use`, types,
  `include … with`), top-level `use`, and packages;
* resolution (`resolveName`, `resolveType`, `closeType`, `Interface.closedFunctions`) of source
  names to nominal `TypeId`s / `ResourceId`s and to canonical-ABI-ready `ClosedType ResourceId`,
  with a `ResolveError` on unknown names, non-resources in handles, and cycles;
* a well-formedness predicate `Package.WellFormed`, decidable, with an executable diagnostic
  list `Package.errors` and `Package.errors_eq_nil_iff`.

Resource identity is the defining `(owner, name)` pair: a resource reached through `use`
chains resolves to the interface that defines it. This is the per-definition identity of the
WIT resolver; the per-import duplication that happens when a world imports the same interface
under two plain names (`WIT.md` §Package Format) belongs to the world-to-component-type
translation, which is not modelled here.

Not modelled or not claimed: no parser (the renderer is `WIT/Render.lean`); resource
getters/setters 📡, `@external-id` 🏷️, and nested `package … { }` blocks are omitted; include
expansion (union, interface de-duplication, `with` renaming) and implicit transitive imports of
`use`d interfaces (§Transitive imports and worlds) are not computed, so world name uniqueness
ignores included items (include *cycles* are rejected); the gate *compatibility* rules (§Rules for feature gate usage: an item
referring to or contained in a gated item must be compatibly gated) are not checked; versions
in qualified paths must match a dependency's version exactly (no semver-compatible matching);
dependencies in the environment are not themselves checked. The resolution fuel is a size bound
which suffices for acyclic packages; this sufficiency, and agreement with `wit-parser`, are not
proved. Where `WIT.md` is silent, we follow the stricter binary rules: names are strongly unique
(`Explainer.md` §Name Uniqueness, stronger than WIT's case-insensitive uniqueness, so e.g.
`[method]r.r` is rejected), tuples are nonempty, and `borrow` may not occur in function results
or `future`/`stream` payloads (`Binary.md` type rules), and `stream<char>` is rejected
(`Binary.md` §Type Definitions, a temporary TODO there). Gate rules follow wit-parser 0.259
rather than the text of `WIT.md` (see `Gate.Valid`): `@unstable` is allowed in an unversioned
package, `@since` requires a package version no older than it, and `@deprecated` requires
`@since` or `@unstable`. Handle names follow `type` aliases to resources, as in wit-parser
(`WIT.md` §Handles only mentions resource items).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT

universe u v w

/-! ## Identifiers -/

/-- `[0-9a-z]` -/
def isLowerAlnum (c : Char) : Bool := decide ('a' ≤ c ∧ c ≤ 'z') || decide ('0' ≤ c ∧ c ≤ '9')

/-- `[0-9A-Z]` -/
def isUpperAlnum (c : Char) : Bool := decide ('A' ≤ c ∧ c ≤ 'Z') || decide ('0' ≤ c ∧ c ≤ '9')

def isAsciiLetter (c : Char) : Bool := decide ('a' ≤ c ∧ c ≤ 'z') || decide ('A' ≤ c ∧ c ≤ 'Z')

/-- Split a character sequence at every `-`. Structural, so the kernel can evaluate it. -/
def splitHyphens : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = '-' then [] :: splitHyphens cs else
      match splitHyphens cs with
      | [] => [[c]]
      | f :: fs => (c :: f) :: fs

/-- `word ::= [0-9a-z]+` -/
def IsWord (f : List Char) : Prop := f ≠ [] ∧ ∀ c ∈ f, isLowerAlnum c = true

/-- `acronym ::= [0-9A-Z]+` -/
def IsAcronym (f : List Char) : Prop := f ≠ [] ∧ ∀ c ∈ f, isUpperAlnum c = true

def IsFragment (f : List Char) : Prop := IsWord f ∨ IsAcronym f

/-- `first-fragment ::= first-word | first-acronym`, i.e. a fragment starting with a letter. -/
def IsFirstFragment : List Char → Prop
  | [] => False
  | c :: cs => isAsciiLetter c = true ∧ IsFragment (c :: cs)

/-- `first-word ::= [a-z] [0-9a-z]*` -/
def IsFirstWord : List Char → Prop
  | [] => False
  | c :: cs => isAsciiLetter c = true ∧ IsWord (c :: cs)

def LabelFragments : List (List Char) → Prop
  | [] => False
  | f :: fs => IsFirstFragment f ∧ ∀ g ∈ fs, IsFragment g

def WordsFragments : List (List Char) → Prop
  | [] => False
  | f :: fs => IsFirstWord f ∧ ∀ g ∈ fs, IsWord g

/-- The kebab-case `label ::= first-fragment ('-' fragment)*` of `Explainer.md` §Import and
Export Definitions, which WIT identifiers (`WIT.md` §WIT Identifiers) reuse. A label may be a
keyword; the text format then writes it `%`-escaped (see `keywords`). -/
def IsLabel (s : String) : Prop := LabelFragments (splitHyphens s.toList)

/-- `words ::= first-word ('-' word)*`: the lowercase-only form required of namespaces and
package names inside an `interfacename`. -/
def IsWords (s : String) : Prop := WordsFragments (splitHyphens s.toList)

instance : DecidablePred IsWord := fun _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsAcronym := fun _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsFragment := fun _ => inferInstanceAs (Decidable (_ ∨ _))

instance : DecidablePred IsFirstFragment
  | [] => isFalse fun h => h
  | _ :: _ => inferInstanceAs (Decidable (_ ∧ _))

instance : DecidablePred IsFirstWord
  | [] => isFalse fun h => h
  | _ :: _ => inferInstanceAs (Decidable (_ ∧ _))

instance : DecidablePred LabelFragments
  | [] => isFalse fun h => h
  | _ :: _ => inferInstanceAs (Decidable (_ ∧ _))

instance : DecidablePred WordsFragments
  | [] => isFalse fun h => h
  | _ :: _ => inferInstanceAs (Decidable (_ ∧ _))

instance : DecidablePred IsLabel := fun _ => inferInstanceAs (Decidable (LabelFragments _))
instance : DecidablePred IsWords := fun _ => inferInstanceAs (Decidable (WordsFragments _))

/-- The executable label checker. -/
def isLabel (s : String) : Bool := decide (IsLabel s)

/-- The reserved words of `WIT.md` §Keywords, verbatim. They are valid labels but must be
written `%`-escaped as WIT identifiers. -/
def keywords : List String :=
  ["as", "async", "bool", "borrow", "char", "constructor", "enum", "export", "f32", "f64",
   "flags", "from", "func", "future", "import", "include", "interface", "list", "map", "option",
   "own", "package", "record", "resource", "result", "s16", "s32", "s64", "s8", "static",
   "stream", "string", "tuple", "type", "u16", "u32", "u64", "u8", "use", "variant", "with",
   "world"]

/-- Words the renderer escapes: `keywords`, plus `error-context` (the WIT spelling of the
error-context type, absent from `WIT.md` §Types), the only further keyword of the wit-parser
0.259 lexer (`src/ast/lex.rs`) that is also a valid label. -/
def reservedWords : List String := keywords ++ ["error-context"]

/-- Step 1 of `Explainer.md` §Name Uniqueness: remove hyphens and lowercase acronyms. -/
def canonChars : List Char → List Char
  | [] => []
  | c :: cs => if c = '-' then canonChars cs else c.toLower :: canonChars cs

def canonLabel (s : String) : List Char := canonChars s.toList

/-! ## Versions and package names -/

/-- A Semantic Versioning 2.0 version. Pre-release and build identifiers are kept as strings;
`SemVer.Valid` checks their spelling. -/
structure SemVer where
  major : Nat
  minor : Nat
  patch : Nat
  pre : List String := []
  build : List String := []
  deriving Repr, DecidableEq

def isIdentChar (c : Char) : Bool := isLowerAlnum c || isUpperAlnum c || decide (c = '-')
def isDigitChar (c : Char) : Bool := decide ('0' ≤ c ∧ c ≤ '9')

def noLeadingZero : List Char → Bool
  | '0' :: _ :: _ => false
  | _ => true

/-- SemVer build identifier: `[0-9A-Za-z-]+`. -/
def IsBuildIdent (s : String) : Prop := s.toList ≠ [] ∧ ∀ c ∈ s.toList, isIdentChar c = true

/-- SemVer pre-release identifier: a build identifier whose numeric form has no leading zero. -/
def IsPreIdent (s : String) : Prop :=
  IsBuildIdent s ∧ ((∀ c ∈ s.toList, isDigitChar c = true) → noLeadingZero s.toList = true)

instance : DecidablePred IsBuildIdent := fun _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsPreIdent := fun _ => inferInstanceAs (Decidable (_ ∧ _))

def SemVer.Valid (v : SemVer) : Prop := (∀ s ∈ v.pre, IsPreIdent s) ∧ ∀ s ∈ v.build, IsBuildIdent s

instance : DecidablePred SemVer.Valid := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Numeric value of a digit string (callers check that it is all digits). -/
def digitsValue : List Char → Nat → Nat
  | [], acc => acc
  | c :: cs, acc => digitsValue cs (acc * 10 + (c.toNat - '0'.toNat))

/-- Strict SemVer 2.0 §11 precedence of two pre-release identifiers: numeric identifiers
compare numerically and sort below alphanumeric ones, which compare in ASCII order. -/
def preIdentLt (a b : String) : Bool :=
  let na := a.toList.all isDigitChar
  let nb := b.toList.all isDigitChar
  match na, nb with
  | true, true => decide (digitsValue a.toList 0 < digitsValue b.toList 0)
  | true, false => true
  | false, true => false
  | false, false => decide (a < b)

/-- Strict precedence of pre-release identifier lists that are both non-empty or both empty:
the first differing identifier decides, and a proper prefix is smaller. -/
def preListLt : List String → List String → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => preIdentLt a b || (a == b && preListLt as bs)

/-- SemVer 2.0 §11 precedence `≤`. Build metadata is ignored (the `semver` crate used by
wit-parser only breaks ties with it). -/
def SemVer.le (v w : SemVer) : Bool :=
  if v.major ≠ w.major then decide (v.major < w.major)
  else if v.minor ≠ w.minor then decide (v.minor < w.minor)
  else if v.patch ≠ w.patch then decide (v.patch < w.patch)
  else match v.pre, w.pre with
    | [], [] => true
    | [], _ :: _ => false
    | _ :: _, [] => true
    | ps, qs => !preListLt qs ps

/-- `P` holds of the value, if any. -/
def OptAll {α : Type u} (P : α → Prop) : Option α → Prop
  | none => True
  | some a => P a

instance {α : Type u} (P : α → Prop) [DecidablePred P] : DecidablePred (OptAll P)
  | none => isTrue trivial
  | some a => inferInstanceAs (Decidable (P a))

/-- `package-decl ::= 'package' (id ':')+ id ('/' id)* ('@' valid-semver)?` (`WIT.md` §Package
declaration). `nestedNs` and `nestedPkgs` are the 🪺 nested namespaces and packages; for
`foo:bar:baz/quux@1.0.0`, `ns = foo`, `nestedNs = [bar]`, `name = baz`, `nestedPkgs = [quux]`. -/
structure PackageName where
  ns : String
  nestedNs : List String := []
  name : String
  nestedPkgs : List String := []
  version : Option SemVer := none
  deriving Repr, DecidableEq

/-- Namespaces and the package are `words`; nested packages are projections (`label`s);
`Explainer.md` §Import and Export Definitions, `interfacename`. -/
def PackageName.Valid (p : PackageName) : Prop :=
  IsWords p.ns ∧ (∀ n ∈ p.nestedNs, IsWords n) ∧ IsWords p.name ∧ (∀ n ∈ p.nestedPkgs, IsLabel n) ∧
    OptAll SemVer.Valid p.version

instance : DecidablePred PackageName.Valid := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- `use-path` (`WIT.md` §Item: `toplevel-use`): a bare interface name, resolved in the current
package or through a top-level `use`, or an interface of a (possibly other) package. The
version, if any, belongs to `package`. -/
inductive UsePath where
  | ident (name : String)
  | qualified (package : PackageName) (interface : String)
  deriving Repr, DecidableEq

/-! ## Feature gates -/

/-- The gates of one item (`WIT.md` §Feature Gates, §Feature gate syntax). -/
structure Gate where
  since : Option SemVer := none
  unstable : Option String := none
  deprecated : Option SemVer := none
  deriving Repr, DecidableEq

/-- The `@since` version condition against the package version `pkg`: the package is versioned
and `since` is not an unreleased version of it. -/
def SinceOk (pkg : Option SemVer) (since : SemVer) : Prop :=
  match pkg with
  | none => False
  | some pv => since.le pv = true

instance (pkg : Option SemVer) : DecidablePred (SinceOk pkg) := fun _ =>
  match pkg with
  | none => isFalse fun h => h
  | some _ => inferInstanceAs (Decidable (_ = _))

/-- Gate rules as enforced by wit-parser 0.259 (wasm-tools 1.259), which we follow where it
departs from the text of `WIT.md` §Rules for feature gate usage:
* not both `@since` and `@unstable`; `@deprecated` needs `@since` or `@unstable`
  (`ast/resolve.rs`, stability attribute parsing);
* `@since(version = v)` needs a versioned package whose version is at least `v`
  (`resolve/mod.rs`, `include_stability`: "feature gate cannot reference unreleased version").

Deviation from `WIT.md`: `WIT.md` says any package containing a feature gate must be
versioned; like wit-parser we allow `@unstable` (with or without `@deprecated`) in an
unversioned package, and do not compare the `@deprecated` version with the package version. -/
def Gate.Valid (pkg : Option SemVer) (g : Gate) : Prop :=
  ¬(g.since.isSome = true ∧ g.unstable.isSome = true) ∧
    (g.deprecated.isSome = true → g.since.isSome = true ∨ g.unstable.isSome = true) ∧
    OptAll (SinceOk pkg) g.since ∧
    OptAll IsLabel g.unstable ∧ OptAll SemVer.Valid g.since ∧ OptAll SemVer.Valid g.deprecated

instance (pkg : Option SemVer) : DecidablePred (Gate.Valid pkg) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-! ## Declarations -/

/-- A WIT type expression (`WIT.md` §Types). A bare `id` is `.ref id`: the resolver decides
whether it names a type or (as an owned handle) a resource. `borrow<id>` is `.borrow id`;
`.own id` is an explicit owned handle, rendered as `id`. The `record`, `variant`, `enum` and
`flags` constructors are not type expressions in WIT; well-formedness rejects them here. -/
abbrev TypeExpr := NamedType String

/-- A WIT function type; `async_` is the `async` marker (`WIT.md` §Item: `interface`). -/
abbrev FuncSig := FuncType String String

/-- A member of a `resource` block (`WIT.md` §Item: `resource`). A constructor with no
`result` is infallible (implicit result the resource); otherwise the result is written. -/
inductive ResourceMember where
  | constructor (params : List (String × TypeExpr)) (result : Option TypeExpr := none)
      (gate : Gate := {})
  | method (name : String) (type : FuncSig) (gate : Gate := {})
  | static (name : String) (type : FuncSig) (gate : Gate := {})
  deriving Repr

def ResourceMember.gate : ResourceMember → Gate
  | .constructor _ _ g | .method _ _ g | .static _ _ g => g

/-- The body of a named type definition (`WIT.md` §Items: type). -/
inductive TypeDefKind where
  | typeAlias (type : TypeExpr)
  | record (fields : List (String × TypeExpr))
  | variant (cases : List (String × Option TypeExpr))
  | enum (cases : List String)
  | flags (labels : List String)
  | resource (members : List ResourceMember := [])
  deriving Repr

/-- `use path.{a, b as c};` (`WIT.md` §Item: `use`). Each name is `(original, rename)`. -/
structure UseDecl where
  path : UsePath
  names : List (String × Option String)
  deriving Repr, DecidableEq

/-- Local name and original name of each binding. -/
def UseDecl.bindings (u : UseDecl) : List (String × String) :=
  u.names.map fun b => (b.2.getD b.1, b.1)

/-- `interface-items` (`WIT.md` §Item: `interface`), each with its gate. -/
inductive InterfaceItem where
  | use (decl : UseDecl) (gate : Gate := {})
  | typeDef (name : String) (kind : TypeDefKind) (gate : Gate := {})
  | func (name : String) (type : FuncSig) (gate : Gate := {})
  deriving Repr

structure Interface where
  name : String
  items : List InterfaceItem := []
  gate : Gate := {}
  deriving Repr

/-- The `extern-type` of a world import or export (`WIT.md` §Item: `world`):
`import path;`, `import name: func…;`, `import name: interface { … }`, and 🏷️
`import name: path;`. -/
inductive WorldExtern where
  | interface (path : UsePath)
  | func (name : String) (type : FuncSig)
  | inline (name : String) (items : List InterfaceItem)
  | implements (name : String) (path : UsePath)
  deriving Repr

/-- `world-items` (`WIT.md` §Item: `world`, §Item: `include`), each with its gate. -/
inductive WorldItem where
  | import_ (ext : WorldExtern) (gate : Gate := {})
  | export_ (ext : WorldExtern) (gate : Gate := {})
  | use (decl : UseDecl) (gate : Gate := {})
  | typeDef (name : String) (kind : TypeDefKind) (gate : Gate := {})
  | include (path : UsePath) (renames : List (String × String) := []) (gate : Gate := {})
  deriving Repr

structure World where
  name : String
  items : List WorldItem := []
  gate : Gate := {}
  deriving Repr

/-- `toplevel-use-item ::= 'use' use-path ('as' id)? ';'` -/
structure TopUse where
  path : UsePath
  rename : Option String := none
  deriving Repr, DecidableEq

/-- The name a top-level `use` binds. -/
def TopUse.localName (u : TopUse) : String :=
  u.rename.getD (match u.path with | .ident n => n | .qualified _ i => i)

/-- One WIT package: its name, file-level `use`s, interfaces and worlds. -/
structure Package where
  name : PackageName
  uses : List TopUse := []
  interfaces : List Interface := []
  worlds : List World := []
  deriving Repr

/-! ## Desugared names -/

/-- Function export names after resource desugaring (`Explainer.md` `plainname`, without 📡). -/
inductive FuncName where
  | plain (name : String)
  | constructor (resource : String)
  | method (resource name : String)
  | static (resource name : String)
  deriving Repr, DecidableEq

def FuncName.render : FuncName → String
  | .plain n => n
  | .constructor r => "[constructor]" ++ r
  | .method r n => "[method]" ++ r ++ "." ++ n
  | .static r n => "[static]" ++ r ++ "." ++ n

/-- Canonical keys for strong uniqueness (`Explainer.md` §Name Uniqueness): after removing
hyphens and lowercasing, `[…]l.l` becomes `l`, and all annotations but `[constructor]` are
dropped. Interface names keep their structure, with each segment canonicalised. -/
inductive NameKey where
  | plain (label : List Char)
  | constructor (label : List Char)
  | interface (namespaces packages : List (List Char)) (version : Option SemVer)
  deriving Repr, DecidableEq

def FuncName.key : FuncName → NameKey
  | .plain n => .plain (canonLabel n)
  | .constructor r => .constructor (canonLabel r)
  | .method r n | .static r n =>
    if canonLabel r = canonLabel n then .plain (canonLabel r)
    else .plain (canonLabel r ++ '.' :: canonLabel n)

def interfaceKey (p : PackageName) (i : String) : NameKey :=
  .interface ((p.ns :: p.nestedNs).map canonLabel) ((p.name :: p.nestedPkgs ++ [i]).map canonLabel)
    p.version

/-- Desugaring of `WIT.md` §Item: `resource`: `[constructor]r` returns `r` (or the written
`result`), `[method]r.m` takes `self: borrow<r>` first. -/
def ResourceMember.desugar (r : String) : ResourceMember → FuncName × FuncSig
  | .constructor ps res _ => (.constructor r, { params := ps, result := some (res.getD (.ref r)) })
  | .method m f _ => (.method r m, { f with params := ("self", .borrow r) :: f.params })
  | .static m f _ => (.static r m, f)

def InterfaceItem.functions : InterfaceItem → List (FuncName × FuncSig)
  | .func n f _ => [(.plain n, f)]
  | .typeDef r (.resource ms) _ => ms.map (ResourceMember.desugar r)
  | _ => []

/-- All functions an interface exports, desugared, in declaration order. -/
def interfaceFunctions (items : List InterfaceItem) : List (FuncName × FuncSig) :=
  items.flatMap InterfaceItem.functions

/-! ## Resolution -/

abbrev Env := List Package

/-- Where a named type is defined. `inline` is an interface written inline in a world
(`import name: interface { … }`). -/
inductive Owner where
  | interface (package : PackageName) (name : String)
  | world (package : PackageName) (world : String)
  | inline (package : PackageName) (world : String) (name : String)
  deriving Repr, DecidableEq

/-- The nominal identity of a named type definition. -/
structure TypeId where
  owner : Owner
  name : String
  deriving Repr, DecidableEq

/-- Resource identity: the `TypeId` of the defining `resource` item. -/
abbrev ResourceId := TypeId

/-- A name-resolution scope: the `use`s and type definitions of one interface or world. -/
structure Scope where
  package : Package
  owner : Owner
  uses : List UseDecl
  defs : List (String × TypeDefKind)

def interfaceUses : List InterfaceItem → List UseDecl
  | [] => []
  | .use u _ :: is => u :: interfaceUses is
  | _ :: is => interfaceUses is

def interfaceDefs : List InterfaceItem → List (String × TypeDefKind)
  | [] => []
  | .typeDef n k _ :: is => (n, k) :: interfaceDefs is
  | _ :: is => interfaceDefs is

def worldUses : List WorldItem → List UseDecl
  | [] => []
  | .use u _ :: is => u :: worldUses is
  | _ :: is => worldUses is

def worldDefs : List WorldItem → List (String × TypeDefKind)
  | [] => []
  | .typeDef n k _ :: is => (n, k) :: worldDefs is
  | _ :: is => worldDefs is

def Interface.scope (p : Package) (i : Interface) : Scope :=
  ⟨p, .interface p.name i.name, interfaceUses i.items, interfaceDefs i.items⟩

def World.scope (p : Package) (w : World) : Scope :=
  ⟨p, .world p.name w.name, worldUses w.items, worldDefs w.items⟩

def inlineScope (p : Package) (w : World) (name : String) (items : List InterfaceItem) : Scope :=
  ⟨p, .inline p.name w.name name, interfaceUses items, interfaceDefs items⟩

inductive ResolveError where
  | unknownPackage (name : PackageName)
  | unknownInterface (path : UsePath)
  | unknownWorld (path : UsePath)
  | unknownType (owner : Owner) (name : String)
  | notResource (type : TypeId)
  /-- Resolution fuel ran out: a cyclic type or `use` chain. -/
  | cyclic (owner : Owner) (name : String)
  deriving Repr, DecidableEq

def lookupAssoc {α : Type u} : List (String × α) → String → Option α
  | [], _ => none
  | (k, a) :: rest, n => if k = n then some a else lookupAssoc rest n

def findInterface : List Interface → String → Option Interface
  | [], _ => none
  | i :: is, n => if i.name = n then some i else findInterface is n

def findWorld : List World → String → Option World
  | [], _ => none
  | w :: ws, n => if w.name = n then some w else findWorld ws n

def findPackage : List Package → PackageName → Option Package
  | [], _ => none
  | p :: ps, n => if p.name = n then some p else findPackage ps n

def findTopUse : List TopUse → String → Option UsePath
  | [], _ => none
  | u :: us, n => if u.localName = n then some u.path else findTopUse us n

/-- The interface a `use` binding refers to, and the original name there. -/
def findUse : List UseDecl → String → Option (UsePath × String)
  | [], _ => none
  | u :: us, n =>
    match lookupAssoc u.bindings n with
    | some o => some (u.path, o)
    | none => findUse us n

/-- Interfaces of `package` in `p :: env`. -/
def qualifiedInterface (env : Env) (p : Package) (q : PackageName) (i : String) :
    Except ResolveError (Package × Interface) :=
  match findPackage (p :: env) q with
  | none => .error (.unknownPackage q)
  | some p' =>
    match findInterface p'.interfaces i with
    | some it => .ok (p', it)
    | none => .error (.unknownInterface (.qualified q i))

/-- Resolve an interface `use-path`: a bare name is an interface of `p` or a top-level `use`
alias (`WIT.md` §WIT Packages and `use`, §Top-level `use`). -/
def resolveInterface (env : Env) (p : Package) : UsePath → Except ResolveError (Package × Interface)
  | .qualified q i => qualifiedInterface env p q i
  | .ident n =>
    match findInterface p.interfaces n with
    | some i => .ok (p, i)
    | none =>
      match findTopUse p.uses n with
      | some (.qualified q i) => qualifiedInterface env p q i
      | some (.ident m) =>
        match findInterface p.interfaces m with
        | some i => .ok (p, i)
        | none => .error (.unknownInterface (.ident m))
      | none => .error (.unknownInterface (.ident n))

/-- Resolve an `include` target to a world. -/
def resolveWorld (env : Env) (p : Package) : UsePath → Except ResolveError (Package × World)
  | .ident n =>
    match findWorld p.worlds n with
    | some w => .ok (p, w)
    | none => .error (.unknownWorld (.ident n))
  | .qualified q n =>
    match findPackage (p :: env) q with
    | none => .error (.unknownPackage q)
    | some p' =>
      match findWorld p'.worlds n with
      | some w => .ok (p', w)
      | none => .error (.unknownWorld (.qualified q n))

/-- Resolve a type name in a scope to its defining item, chasing `use` bindings across
interfaces (`WIT.md` §Name resolution). Returns the identity, the definition, and the
defining scope. -/
def resolveName (env : Env) : Nat → Scope → String →
    Except ResolveError (TypeId × TypeDefKind × Scope)
  | 0, sc, n => .error (.cyclic sc.owner n)
  | fuel + 1, sc, n =>
    match lookupAssoc sc.defs n with
    | some k => .ok (⟨sc.owner, n⟩, k, sc)
    | none =>
      match findUse sc.uses n with
      | none => .error (.unknownType sc.owner n)
      | some (path, orig) => do
        let (p, i) ← resolveInterface env sc.package path
        resolveName env fuel (Interface.scope p i) orig

/-- Resolve the name in a handle (`own`/`borrow`, `WIT.md` §Handles) to a resource identity.
Like wit-parser 0.259 (`ast/resolve.rs`, `validate_resource`), type aliases `type h = r` are
followed to the resource they name. -/
def resolveResource (env : Env) : Nat → Scope → String → Except ResolveError ResourceId
  | 0, sc, n => .error (.cyclic sc.owner n)
  | fuel + 1, sc, n => do
    let (id, k, sc') ← resolveName env (fuel + 1) sc n
    match k with
    | .resource _ => pure id
    | .typeAlias (.ref m) | .typeAlias (.own m) =>
      match resolveResource env fuel sc' m with
      | .ok r => pure r
      | .error (.notResource _) => throw (.notResource id)
      | .error e => throw e
    | _ => throw (.notResource id)

section Bind

variable {Ref : Type u} {Res : Type v} {Ref' Res' : Type w} {m : Type w → Type w} [Monad m]
  (onRef : Ref → m (ValType Ref' Res')) (onOwn onBorrow : Res → m (ValType Ref' Res'))

mutual
  /-- Substitute references and handles, monadically. -/
  def ValType.bindM : ValType Ref Res → m (ValType Ref' Res')
    | .prim p => pure (.prim p)
    | .ref r => onRef r
    | .list t => .list <$> ValType.bindM t
    | .fixedList t n => (.fixedList · n) <$> ValType.bindM t
    | .record fs => .record <$> ValType.bindFieldsM fs
    | .tuple ts => .tuple <$> ValType.bindListM ts
    | .variant cs => .variant <$> ValType.bindCasesM cs
    | .enum cs => pure (.enum cs)
    | .flags ls => pure (.flags ls)
    | .option t => .option <$> ValType.bindM t
    | .result a b => .result <$> ValType.bindOptM a <*> ValType.bindOptM b
    | .map k t => .map k <$> ValType.bindM t
    | .own r => onOwn r
    | .borrow r => onBorrow r
    | .future t => .future <$> ValType.bindOptM t
    | .stream t => .stream <$> ValType.bindOptM t
    | .errorContext => pure .errorContext

  def ValType.bindFieldsM : List (String × ValType Ref Res) → m (List (String × ValType Ref' Res'))
    | [] => pure []
    | (l, t) :: fs => (fun t' fs' => (l, t') :: fs') <$> ValType.bindM t <*> ValType.bindFieldsM fs

  def ValType.bindListM : List (ValType Ref Res) → m (List (ValType Ref' Res'))
    | [] => pure []
    | t :: ts => List.cons <$> ValType.bindM t <*> ValType.bindListM ts

  def ValType.bindCasesM :
      List (String × Option (ValType Ref Res)) → m (List (String × Option (ValType Ref' Res')))
    | [] => pure []
    | (l, t) :: cs =>
      (fun t' cs' => (l, t') :: cs') <$> ValType.bindOptM t <*> ValType.bindCasesM cs

  def ValType.bindOptM : Option (ValType Ref Res) → m (Option (ValType Ref' Res'))
    | none => pure none
    | some t => some <$> ValType.bindM t
end

end Bind

section Checks

variable {Ref : Type u} {Res : Type v}

mutual
  /-- A `borrow` in a forbidden position: anywhere when `forbid`, and always inside
  `future`/`stream` payloads (`Binary.md` type rules). -/
  def ValType.badBorrow (forbid : Bool) : ValType Ref Res → Bool
    | .prim _ | .ref _ | .enum _ | .flags _ | .own _ | .errorContext => false
    | .borrow _ => forbid
    | .list t | .fixedList t _ | .option t | .map _ t => ValType.badBorrow forbid t
    | .record fs => ValType.badBorrowFields forbid fs
    | .tuple ts => ValType.badBorrowList forbid ts
    | .variant cs => ValType.badBorrowCases forbid cs
    | .result a b => ValType.badBorrowOpt forbid a || ValType.badBorrowOpt forbid b
    | .future t | .stream t => ValType.badBorrowOpt true t

  def ValType.badBorrowFields (forbid : Bool) : List (String × ValType Ref Res) → Bool
    | [] => false
    | (_, t) :: fs => ValType.badBorrow forbid t || ValType.badBorrowFields forbid fs

  def ValType.badBorrowList (forbid : Bool) : List (ValType Ref Res) → Bool
    | [] => false
    | t :: ts => ValType.badBorrow forbid t || ValType.badBorrowList forbid ts

  def ValType.badBorrowCases (forbid : Bool) : List (String × Option (ValType Ref Res)) → Bool
    | [] => false
    | (_, t) :: cs => ValType.badBorrowOpt forbid t || ValType.badBorrowCases forbid cs

  def ValType.badBorrowOpt (forbid : Bool) : Option (ValType Ref Res) → Bool
    | none => false
    | some t => ValType.badBorrow forbid t
end

mutual
  /-- A `stream<char>` anywhere in the type. `Binary.md` §Type Definitions: "Validation of
  `stream` rejects `(stream char)` as a temporary TODO" (wasmparser 0.259 `validator/component.rs`:
  "`stream<char>` is not valid at this time"). -/
  def ValType.streamChar : ValType Ref Res → Bool
    | .prim _ | .ref _ | .enum _ | .flags _ | .own _ | .borrow _ | .errorContext => false
    | .stream (some (.prim .char)) => true
    | .list t | .fixedList t _ | .option t | .map _ t => ValType.streamChar t
    | .record fs => ValType.streamCharFields fs
    | .tuple ts => ValType.streamCharList ts
    | .variant cs => ValType.streamCharCases cs
    | .result a b => ValType.streamCharOpt a || ValType.streamCharOpt b
    | .future t | .stream t => ValType.streamCharOpt t

  def ValType.streamCharFields : List (String × ValType Ref Res) → Bool
    | [] => false
    | (_, t) :: fs => ValType.streamChar t || ValType.streamCharFields fs

  def ValType.streamCharList : List (ValType Ref Res) → Bool
    | [] => false
    | t :: ts => ValType.streamChar t || ValType.streamCharList ts

  def ValType.streamCharCases : List (String × Option (ValType Ref Res)) → Bool
    | [] => false
    | (_, t) :: cs => ValType.streamCharOpt t || ValType.streamCharCases cs

  def ValType.streamCharOpt : Option (ValType Ref Res) → Bool
    | none => false
    | some t => ValType.streamChar t
end

mutual
  /-- A type expression is expressible in WIT: no anonymous `record`/`variant`/`enum`/`flags`
  (`WIT.md` §WIT Types), no empty tuple, no zero-length fixed list (`WIT.md` §Types). -/
  def ValType.exprShaped : ValType Ref Res → Bool
    | .prim _ | .ref _ | .own _ | .borrow _ | .errorContext => true
    | .record _ | .variant _ | .enum _ | .flags _ => false
    | .fixedList t n => decide (0 < n) && ValType.exprShaped t
    | .list t | .option t | .map _ t => ValType.exprShaped t
    | .tuple [] => false
    | .tuple (t :: ts) => ValType.exprShaped t && ValType.exprShapedList ts
    | .result a b => ValType.exprShapedOpt a && ValType.exprShapedOpt b
    | .future t | .stream t => ValType.exprShapedOpt t

  def ValType.exprShapedList : List (ValType Ref Res) → Bool
    | [] => true
    | t :: ts => ValType.exprShaped t && ValType.exprShapedList ts

  def ValType.exprShapedOpt : Option (ValType Ref Res) → Bool
    | none => true
    | some t => ValType.exprShaped t
end

end Checks

/-- Resolve names to nominal identities, keeping type references (`ref`) and turning resource
names into `own`/`borrow` of their `ResourceId`. -/
def resolveType (env : Env) (fuel : Nat) (sc : Scope) (t : TypeExpr) :
    Except ResolveError (ValType TypeId ResourceId) :=
  t.bindM
    (fun n => do
      let (id, k, _) ← resolveName env fuel sc n
      pure (match k with | .resource _ => .own id | _ => .ref id))
    (fun r => .own <$> resolveResource env fuel sc r)
    (fun r => .borrow <$> resolveResource env fuel sc r)

/-- Resolve and expand every named type to its structure, giving the reference-free type
the canonical ABI consumes. Resources stay nominal. Each expansion step consumes fuel, so
exhaustion reports a cyclic definition (`WIT.md` §Name resolution: types cannot be recursive). -/
def closeType (env : Env) : Nat → Scope → TypeExpr → Except ResolveError (ClosedType ResourceId)
  | 0, sc, t =>
    t.bindM (fun n => .error (.cyclic sc.owner n))
      (fun r => .own <$> resolveResource env 0 sc r)
      (fun r => .borrow <$> resolveResource env 0 sc r)
  | fuel + 1, sc, t =>
    t.bindM
      (fun n => do
        let (id, k, sc') ← resolveName env (fuel + 1) sc n
        match k with
        | .typeAlias a => closeType env fuel sc' a
        | .record fs => .record <$> fs.mapM fun f => (f.1, ·) <$> closeType env fuel sc' f.2
        | .variant cs =>
          .variant <$> cs.mapM fun c => (c.1, ·) <$> c.2.mapM (closeType env fuel sc')
        | .enum cs => pure (.enum cs)
        | .flags ls => pure (.flags ls)
        | .resource _ => pure (.own id))
      (fun r => .own <$> resolveResource env (fuel + 1) sc r)
      (fun r => .borrow <$> resolveResource env (fuel + 1) sc r)

/-- A function type with every name closed. -/
def closeFunc (env : Env) (fuel : Nat) (sc : Scope) (f : FuncSig) :
    Except ResolveError (FuncType Empty ResourceId) := do
  let params ← f.params.mapM fun p => (p.1, ·) <$> closeType env fuel sc p.2
  let result ← f.result.mapM (closeType env fuel sc)
  pure { params, result, async_ := f.async_ }

/-- Items of all packages: a size bound used as resolution fuel. -/
def Package.weight (p : Package) : Nat :=
  (p.interfaces.map fun i => i.items.length).sum +
    (p.worlds.map fun w => w.items.length + (w.items.map fun
      | .import_ (.inline _ is) _ | .export_ (.inline _ is) _ => is.length
      | _ => 0).sum).sum + 1

def Package.fuel (env : Env) (p : Package) : Nat := ((p :: env).map Package.weight).sum

/-- The closed, desugared functions of an interface: canonical-ABI-ready signatures whose
handles carry resource identities. -/
def Interface.closedFunctions (env : Env) (p : Package) (i : Interface) :
    Except ResolveError (List (String × FuncType Empty ResourceId)) :=
  (interfaceFunctions i.items).mapM fun f =>
    (f.1.render, ·) <$> closeFunc env (p.fuel env) (i.scope p) f.2

/-! ## Well-formedness -/

inductive WfError where
  | packageName (name : PackageName)
  | label (name : String)
  /-- A scope (list of canonical keys) that is not strongly unique. -/
  | duplicateName (scope : List NameKey)
  | gate (gate : Gate)
  /-- An empty `record`/`variant`/`enum`/`flags`, or more than 32 flags. -/
  | typeDefShape (name : String)
  /-- An anonymous `record`/`variant`/`enum`/`flags`, empty tuple, or zero-length list. -/
  | typeExprShape (owner : Owner)
  | resolve (error : ResolveError)
  /-- A `borrow` in a function result or a `future`/`stream` payload. -/
  | borrowPlacement (owner : Owner)
  /-- A `stream<char>`, after alias expansion (`Binary.md` §Type Definitions). -/
  | streamChar (owner : Owner)
  /-- A written constructor result that is not `result<r, …>`. -/
  | constructorResult (resource : String)
  | useCycle (interface : String)
  /-- A world that (transitively) `include`s itself (`WIT.md` §Name resolution). -/
  | includeCycle (world : String)
  deriving Repr, DecidableEq

/-- A resolution-dependent check. -/
inductive Obligation where
  /-- A type expression; `result` marks function results, where `borrow` is forbidden. -/
  | type (scope : Scope) (type : TypeExpr) (result : Bool)
  | use (scope : Scope) (decl : UseDecl)
  | interface (package : Package) (path : UsePath)
  | world (package : Package) (path : UsePath)
  | constructor (resource : String) (result : Option TypeExpr)

def firstFailure {α : Type u} (f : α → Option WfError) : List α → Option WfError
  | [] => none
  | a :: as => match f a with | some e => some e | none => firstFailure f as

def Obligation.failure (env : Env) (fuel : Nat) : Obligation → Option WfError
  | .type sc t res =>
    if !t.exprShaped then some (.typeExprShape sc.owner) else
      match closeType env fuel sc t with
      | .error e => some (.resolve e)
      | .ok c =>
        if c.badBorrow res then some (.borrowPlacement sc.owner)
        else if c.streamChar then some (.streamChar sc.owner) else none
  | .use sc u =>
    match resolveInterface env sc.package u.path with
    | .error e => some (.resolve e)
    | .ok (p, i) => firstFailure (fun b =>
        match resolveName env fuel (i.scope p) b.1 with
        | .error e => some (.resolve e)
        | .ok _ => none) u.names
  | .interface p path =>
    match resolveInterface env p path with
    | .error e => some (.resolve e)
    | .ok _ => none
  | .world p path =>
    match resolveWorld env p path with
    | .error e => some (.resolve e)
    | .ok _ => none
  | .constructor _ none => none
  | .constructor r (some (.result (some (.ref r')) _))
  | .constructor r (some (.result (some (.own r')) _)) =>
    if r' = r then none else some (.constructorResult r)
  | .constructor r (some _) => some (.constructorResult r)

/-- Everything a package declares that well-formedness inspects, collected in one pass. -/
structure Facts where
  labels : List String := []
  packageNames : List PackageName := []
  scopes : List (List NameKey) := []
  gates : List Gate := []
  typeDefs : List (String × TypeDefKind) := []
  obligations : List Obligation := []

instance : Append Facts where
  append a b := ⟨a.labels ++ b.labels, a.packageNames ++ b.packageNames, a.scopes ++ b.scopes,
    a.gates ++ b.gates, a.typeDefs ++ b.typeDefs, a.obligations ++ b.obligations⟩

def Facts.concat : List Facts → Facts
  | [] => {}
  | f :: fs => f ++ Facts.concat fs

def UsePath.facts : UsePath → Facts
  | .ident n => { labels := [n] }
  | .qualified q i => { labels := [i], packageNames := [q] }

def funcFacts (sc : Scope) (f : FuncSig) : Facts :=
  { labels := f.params.map (·.1)
    scopes := [f.params.map fun p => .plain (canonLabel p.1)]
    obligations := f.params.map (fun p => .type sc p.2 false) ++
      f.result.toList.map (.type sc · true) }

def useFacts (sc : Scope) (u : UseDecl) (g : Gate) : Facts :=
  u.path.facts ++
    { labels := u.names.flatMap (fun b => b.1 :: b.2.toList)
      gates := [g]
      obligations := [.use sc u] }

def memberFacts (sc : Scope) (r : String) (m : ResourceMember) : Facts :=
  let (fn, f) := m.desugar r
  funcFacts sc f ++
    { labels := (match fn with | .method _ n | .static _ n => [n] | _ => []), gates := [m.gate],
      obligations := match m with | .constructor _ res _ => [.constructor r res] | _ => [] }

def typeDefFacts (sc : Scope) (n : String) (k : TypeDefKind) (g : Gate) : Facts :=
  let base : Facts := { labels := [n], gates := [g], typeDefs := [(n, k)] }
  base ++ match k with
    | .typeAlias t => { obligations := [.type sc t false] }
    | .record fs =>
      { labels := fs.map (·.1), scopes := [fs.map fun f => .plain (canonLabel f.1)]
        obligations := fs.map fun f => .type sc f.2 false }
    | .variant cs =>
      { labels := cs.map (·.1), scopes := [cs.map fun c => .plain (canonLabel c.1)]
        obligations := cs.flatMap fun c => c.2.toList.map (.type sc · false) }
    | .enum cs | .flags cs => { labels := cs, scopes := [cs.map fun c => .plain (canonLabel c)] }
    | .resource ms => Facts.concat (ms.map (memberFacts sc n))

def InterfaceItem.facts (sc : Scope) : InterfaceItem → Facts
  | .use u g => useFacts sc u g
  | .typeDef n k g => typeDefFacts sc n k g
  | .func n f g => { labels := [n], gates := [g] } ++ funcFacts sc f

/-- Keys of everything an interface exports: types, `use`d names and desugared functions. -/
def interfaceKeys (items : List InterfaceItem) : List NameKey :=
  (interfaceDefs items).map (fun d => .plain (canonLabel d.1)) ++
    (interfaceUses items).flatMap (fun u => u.bindings.map fun b => .plain (canonLabel b.1)) ++
    (interfaceFunctions items).map (·.1.key)

def interfaceBodyFacts (sc : Scope) (items : List InterfaceItem) : Facts :=
  Facts.concat (items.map (InterfaceItem.facts sc)) ++ { scopes := [interfaceKeys items] }

/-- The import/export name an extern contributes, for uniqueness. -/
def WorldExtern.key (p : Package) : WorldExtern → NameKey
  | .interface (.qualified q i) => interfaceKey q i
  | .interface (.ident n) =>
    match findInterface p.interfaces n, findTopUse p.uses n with
    | none, some (.qualified q i) => interfaceKey q i
    | none, some (.ident m) => interfaceKey p.name m
    | _, _ => interfaceKey p.name n
  | .func n _ | .inline n _ | .implements n _ => .plain (canonLabel n)

def WorldExtern.facts (p : Package) (w : World) (sc : Scope) : WorldExtern → Facts
  | .interface path => path.facts ++ { obligations := [.interface p path] }
  | .func n f => { labels := [n] } ++ funcFacts sc f
  | .inline n items => { labels := [n] } ++ interfaceBodyFacts (inlineScope p w n items) items
  | .implements n path => { labels := [n] } ++ path.facts ++ { obligations := [.interface p path] }

def WorldItem.facts (p : Package) (w : World) (sc : Scope) : WorldItem → Facts
  | .import_ e g | .export_ e g => { gates := [g] } ++ e.facts p w sc
  | .use u g => useFacts sc u g
  | .typeDef n k g => typeDefFacts sc n k g
  | .include path rs g =>
    path.facts ++
      { labels := rs.flatMap (fun r => [r.1, r.2])
        gates := [g]
        obligations := [.world p path] }

/-- Import names, including `use`d and locally defined types (which the world imports), and
export names; `WIT.md` §WIT Worlds: imports and exports are separate scopes. -/
def worldImportKeys (p : Package) : List WorldItem → List NameKey
  | [] => []
  | .import_ e _ :: is => e.key p :: worldImportKeys p is
  | .use u _ :: is => u.bindings.map (fun b => .plain (canonLabel b.1)) ++ worldImportKeys p is
  | .typeDef n k _ :: is =>
    .plain (canonLabel n) :: (InterfaceItem.typeDef n k).functions.map (·.1.key) ++
      worldImportKeys p is
  | _ :: is => worldImportKeys p is

def worldExportKeys (p : Package) : List WorldItem → List NameKey
  | [] => []
  | .export_ e _ :: is => e.key p :: worldExportKeys p is
  | _ :: is => worldExportKeys p is

def Interface.facts (p : Package) (i : Interface) : Facts :=
  { labels := [i.name], gates := [i.gate] } ++ interfaceBodyFacts (i.scope p) i.items

def World.facts (p : Package) (w : World) : Facts :=
  { labels := [w.name], gates := [w.gate],
    scopes := [worldImportKeys p w.items, worldExportKeys p w.items] } ++
    Facts.concat (w.items.map (WorldItem.facts p w (w.scope p)))

def Package.facts (p : Package) : Facts :=
  { packageNames := [p.name]
    labels := p.uses.flatMap fun u => u.rename.toList
    scopes := [p.interfaces.map (fun i => .plain (canonLabel i.name)) ++
      p.worlds.map (fun w => .plain (canonLabel w.name)) ++
      p.uses.map fun u => .plain (canonLabel u.localName)]
    obligations := p.uses.map fun u => .interface p u.path } ++
    Facts.concat (p.uses.map fun u => u.path.facts) ++
    Facts.concat (p.interfaces.map (Interface.facts p)) ++
    Facts.concat (p.worlds.map (World.facts p))

/-- Sizes and cardinalities of named type definitions (`WIT.md` §Items: type; the 32-flag
bound of `ValType.WellFormed`). -/
def TypeDefKind.Shaped : TypeDefKind → Prop
  | .typeAlias _ | .resource _ => True
  | .record fs => fs ≠ []
  | .variant cs => cs ≠ []
  | .enum cs => cs ≠ []
  | .flags ls => ls ≠ [] ∧ ls.length ≤ 32

instance : DecidablePred TypeDefKind.Shaped
  | .typeAlias _ | .resource _ => isTrue trivial
  | .record _ | .variant _ | .enum _ => inferInstanceAs (Decidable (¬_ = _))
  | .flags _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Interfaces of `p` that a local interface `use`s. -/
def Package.interfaceDeps (p : Package) (n : String) : List String :=
  match findInterface p.interfaces n with
  | none => []
  | some i => (interfaceUses i.items).filterMap fun u =>
      match u.path with
      | .ident m => some m
      | .qualified q m => if q = p.name then some m else none

/-- Whether interface `a` reaches `b` through local `use`s within `fuel` steps. Exhaustion
counts as reaching, so a false answer at fuel `interfaces.length + 1` means no cycle. -/
def Package.reaches (p : Package) : Nat → String → String → Bool
  | 0, _, _ => true
  | fuel + 1, a, b => (p.interfaceDeps a).any fun c => decide (c = b) || p.reaches fuel c b

/-- Worlds of `p` that a local world `include`s. -/
def Package.worldDeps (p : Package) (n : String) : List String :=
  match findWorld p.worlds n with
  | none => []
  | some w => w.items.filterMap fun
      | .include (.ident m) _ _ => some m
      | .include (.qualified q m) _ _ => if q = p.name then some m else none
      | _ => none

/-- Whether world `a` reaches `b` through local `include`s within `fuel` steps; exhaustion
counts as reaching, as for `Package.reaches`. -/
def Package.worldReaches (p : Package) : Nat → String → String → Bool
  | 0, _, _ => true
  | fuel + 1, a, b => (p.worldDeps a).any fun c => decide (c = b) || p.worldReaches fuel c b

/-- Well-formedness of a package against its dependencies `env` (`WIT.md` §Name resolution,
§WIT Identifiers, §Feature Gates, §Item: `resource`, §WIT Worlds; `Explainer.md` §Name
Uniqueness; `Binary.md` borrow rules). -/
structure Package.WellFormed (env : Env) (p : Package) : Prop where
  packageNames : ∀ n ∈ p.facts.packageNames, n.Valid
  labels : ∀ l ∈ p.facts.labels, IsLabel l
  unique : ∀ s ∈ p.facts.scopes, s.Nodup
  gates : ∀ g ∈ p.facts.gates, g.Valid p.name.version
  shapes : ∀ d ∈ p.facts.typeDefs, d.2.Shaped
  resolved : ∀ o ∈ p.facts.obligations, o.failure env (p.fuel env) = none
  acyclic : ∀ i ∈ p.interfaces, p.reaches (p.interfaces.length + 1) i.name i.name = false
  acyclicWorlds : ∀ w ∈ p.worlds, p.worldReaches (p.worlds.length + 1) w.name w.name = false

theorem Package.wellFormed_iff (env : Env) (p : Package) :
    p.WellFormed env ↔
      (∀ n ∈ p.facts.packageNames, n.Valid) ∧ (∀ l ∈ p.facts.labels, IsLabel l) ∧
      (∀ s ∈ p.facts.scopes, s.Nodup) ∧ (∀ g ∈ p.facts.gates, g.Valid p.name.version) ∧
      (∀ d ∈ p.facts.typeDefs, d.2.Shaped) ∧
      (∀ o ∈ p.facts.obligations, o.failure env (p.fuel env) = none) ∧
      (∀ i ∈ p.interfaces, p.reaches (p.interfaces.length + 1) i.name i.name = false) ∧
      (∀ w ∈ p.worlds, p.worldReaches (p.worlds.length + 1) w.name w.name = false) :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8⟩,
    fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨a, b, c, d, e, f, g, h⟩⟩

instance (env : Env) (p : Package) : Decidable (p.WellFormed env) :=
  decidable_of_iff _ (Package.wellFormed_iff env p).symm

/-- Executable diagnostics: every violated condition, one error per offending item. -/
def Package.errors (env : Env) (p : Package) : List WfError :=
  let f := p.facts
  (f.packageNames.filter (fun n => !decide n.Valid)).map .packageName ++
    (f.labels.filter (fun l => !decide (IsLabel l))).map .label ++
    (f.scopes.filter (fun s => !decide s.Nodup)).map .duplicateName ++
    (f.gates.filter (fun g => !decide (g.Valid p.name.version))).map .gate ++
    (f.typeDefs.filter (fun d => !decide d.2.Shaped)).map (.typeDefShape ·.1) ++
    f.obligations.filterMap (·.failure env (p.fuel env)) ++
    (p.interfaces.filter (fun i => p.reaches (p.interfaces.length + 1) i.name i.name)).map
      (.useCycle ·.name) ++
    (p.worlds.filter (fun w => p.worldReaches (p.worlds.length + 1) w.name w.name)).map
      (.includeCycle ·.name)

end Silmaril.Wasm.Component.WIT
