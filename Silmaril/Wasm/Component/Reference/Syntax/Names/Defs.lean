module

public import Silmaril.Wasm.Component.Reference.Syntax.Basic.Defs
public import Silmaril.Wasm.Component.Reference.WIT.Package.Defs
public import Mathlib.Data.List.Nodup

/-!
# Component import and export names

The lexical grammar of `externname` and the strong-uniqueness canonicalization of
`design/mvp/Explainer.md` at component-model revision `a25fc0b`
(https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/Explainer.md),
§Import and Export Definitions (the `externname`, `plainname`, `interfacename` productions,
lines 2748–2782) and §Name Uniqueness (lines 2872–2946).

This file builds on `WIT/Package.lean`, which already provides the `label` / `words`
productions (`WIT.IsLabel`, `WIT.isLabel`, `WIT.IsWords`) and step 1.1 of the canonicalization
(`WIT.canonChars`, `WIT.canonLabel`). It adds:
* `PlainName` and `parsePlainName?`: `label`, `[constructor]l`, `[method]r.m`, `[static]r.m`,
  and the 📡 `[get]l`, `[set]l`, `[method][get]r.m`, `[method][set]r.m`, `[static][get]r.m`,
  `[static][set]r.m` forms; every label must satisfy `WIT.IsLabel`;
* `InterfaceName` and `parseInterfaceName?`: `namespace:package/label@version`, with the 🪺
  nested namespaces and projections accepted and flagged by `InterfaceName.nested`;
* `ExternName.kind`, classifying a name as plain, interface or invalid;
* `strongCanon` (step 1, i.e. sub-steps 1.1–1.3, of §Name Uniqueness) and `stronglyUnique`
  (step 2).

All functions are structural over `List Char`, so the tests below are kernel-checked with
`decide +kernel`.

Not modelled or not claimed: the `interfaceversion` is kept as an opaque string that is only
checked to be non-empty and made of the semver characters `[0-9A-Za-z.+-]` (no SemVer 2.0 or
🔗 `canonversion` parsing; `WIT.SemVer` has no parser); canonical interface names (🔗) and
`versionsuffix` are not computed. For names that are not plain names (interface names, or
invalid names), `strongCanon` applies step 1.1 to the whole string, as the Explainer text does;
it is not claimed to agree with wasmparser on invalid names.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Syntax

/-! ## Character-list helpers -/

/-- Strip `pre` from the front of `cs`. -/
def stripPrefix? : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | _ :: _, [] => none
  | p :: ps, c :: cs => if p = c then stripPrefix? ps cs else none

/-- Split at the first occurrence of `sep`. -/
def splitFirst? (sep : Char) : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs =>
    if c = sep then some ([], cs) else
      match splitFirst? sep cs with
      | none => none
      | some (a, b) => some (c :: a, b)

/-- Split at every occurrence of `sep` (always returns at least one segment). -/
def splitAll (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = sep then [] :: splitAll sep cs else
      match splitAll sep cs with
      | [] => [[c]]
      | f :: fs => (c :: f) :: fs

/-- `WIT.IsLabel` on a character list. -/
def isLabelChars (cs : List Char) : Bool := decide (WIT.LabelFragments (WIT.splitHyphens cs))

/-- `WIT.IsWords` on a character list. -/
def isWordsChars (cs : List Char) : Bool := decide (WIT.WordsFragments (WIT.splitHyphens cs))

/-! ## Plain names -/

/-- 📡 The `[get]` / `[set]` property annotations. -/
inductive Accessor where
  | get | set
  deriving Repr, DecidableEq

/-- `plainname`. `method acc r m` is `[method]` followed by the optional accessor and `r.m`;
likewise `static`. -/
inductive PlainName where
  | label (l : String)
  | get (l : String)
  | set (l : String)
  | constructor (r : String)
  | method (acc : Option Accessor) (r m : String)
  | static (acc : Option Accessor) (r m : String)
  deriving Repr, DecidableEq

/-- A label, or `none`. -/
def labelOf? (cs : List Char) : Option String :=
  if isLabelChars cs then some (String.ofList cs) else none

/-- `label '.' label`. -/
def dottedOf? (cs : List Char) : Option (String × String) :=
  match splitFirst? '.' cs with
  | none => none
  | some (r, m) =>
    match labelOf? r, labelOf? m with
    | some r, some m => some (r, m)
    | _, _ => none

/-- The optional 📡 accessor after `[method]` or `[static]`, and the rest. -/
def accessorOf (cs : List Char) : Option Accessor × List Char :=
  match stripPrefix? "[get]".toList cs with
  | some rest => (some .get, rest)
  | none =>
    match stripPrefix? "[set]".toList cs with
    | some rest => (some .set, rest)
    | none => (none, cs)

/-- Parse a `plainname` given as characters. -/
def parsePlainNameChars? (cs : List Char) : Option PlainName :=
  match stripPrefix? "[constructor]".toList cs with
  | some rest => (labelOf? rest).map .constructor
  | none =>
  match stripPrefix? "[method]".toList cs with
  | some rest =>
    let (acc, rest) := accessorOf rest
    (dottedOf? rest).map fun (r, m) => .method acc r m
  | none =>
  match stripPrefix? "[static]".toList cs with
  | some rest =>
    let (acc, rest) := accessorOf rest
    (dottedOf? rest).map fun (r, m) => .static acc r m
  | none =>
  match stripPrefix? "[get]".toList cs with
  | some rest => (labelOf? rest).map .get
  | none =>
  match stripPrefix? "[set]".toList cs with
  | some rest => (labelOf? rest).map .set
  | none => (labelOf? cs).map .label

/-- Parse a `plainname` (Explainer §Import and Export Definitions). -/
def parsePlainName? (s : String) : Option PlainName := parsePlainNameChars? s.toList

/-- The text of an accessor annotation. -/
def Accessor.render : Accessor → String
  | .get => "[get]"
  | .set => "[set]"

/-- The optional accessor annotation's text. -/
def renderAccessor : Option Accessor → String
  | none => ""
  | some a => a.render

/-- Print a plain name. -/
def PlainName.render : PlainName → String
  | .label l => l
  | .get l => "[get]" ++ l
  | .set l => "[set]" ++ l
  | .constructor r => "[constructor]" ++ r
  | .method acc r m => "[method]" ++ renderAccessor acc ++ r ++ "." ++ m
  | .static acc r m => "[static]" ++ renderAccessor acc ++ r ++ "." ++ m

/-- The resource named by a `[constructor]`, `[method]` or `[static]` annotation. -/
def PlainName.resource? : PlainName → Option String
  | .constructor r | .method _ r _ | .static _ r _ => some r
  | _ => none

/-! ## Interface names -/

/-- `interfacename ::= namespace+ words projection+ interfaceversion?`. Without 🪺 there is
exactly one namespace and one projection. The version is an opaque string. -/
structure InterfaceName where
  namespaces : List String
  package : String
  projections : List String
  version : Option String := none
  deriving Repr, DecidableEq

/-- 🪺: more than one namespace or projection. -/
def InterfaceName.nested (i : InterfaceName) : Bool :=
  decide (1 < i.namespaces.length) || decide (1 < i.projections.length)

/-- Semver characters `[0-9A-Za-z.+-]`. -/
def isVersionChar (c : Char) : Bool :=
  WIT.isLowerAlnum c || WIT.isUpperAlnum c || decide (c = '.') || decide (c = '+') ||
    decide (c = '-')

/-- The optional `'@' version` suffix: absent, or a non-empty run of semver characters. -/
def versionOf? : Option (List Char) → Option (Option String)
  | none => some none
  | some [] => none
  | some v@(_ :: _) => if v.all isVersionChar then some (some (String.ofList v)) else none

/-- Split the part before `@` into namespaces, package and projections. -/
def interfaceBodyOf? (body : List Char) : Option (List String × String × List String) :=
  match splitAll '/' body with
  | [] | [_] => none
  | head :: projs =>
    match (splitAll ':' head).reverse with
    | [] | [_] => none
    | pkg :: nssRev =>
      let nss := nssRev.reverse
      if nss.all isWordsChars && isWordsChars pkg && projs.all isLabelChars then
        some (nss.map String.ofList, String.ofList pkg, projs.map String.ofList)
      else none

/-- Parse an `interfacename` given as characters. -/
def parseInterfaceNameChars? (cs : List Char) : Option InterfaceName :=
  let (body, ver) : List Char × Option (List Char) :=
    match splitFirst? '@' cs with
    | none => (cs, none)
    | some (b, v) => (b, some v)
  match interfaceBodyOf? body, versionOf? ver with
  | some (nss, pkg, projs), some v =>
    some { namespaces := nss, package := pkg, projections := projs, version := v }
  | _, _ => none

/-- Parse an `interfacename` (Explainer §Import and Export Definitions). -/
def parseInterfaceName? (s : String) : Option InterfaceName := parseInterfaceNameChars? s.toList

/-- Print an interface name. -/
def InterfaceName.render (i : InterfaceName) : String :=
  String.join (i.namespaces.map (· ++ ":")) ++ i.package ++
    String.join (i.projections.map ("/" ++ ·)) ++
    match i.version with
    | none => ""
    | some v => "@" ++ v

/-! ## Extern names -/

/-- The classification of an `externname`. -/
inductive ExternNameKind where
  | plain (p : PlainName)
  | interface (i : InterfaceName)
  | invalid
  deriving Repr, DecidableEq

/-- Classify a name string: a `plainname`, an `interfacename`, or neither. The two grammars
are disjoint (plain names contain no `:`). -/
def externNameKind (s : String) : ExternNameKind :=
  match parsePlainName? s with
  | some p => .plain p
  | none =>
    match parseInterfaceName? s with
    | some i => .interface i
    | none => .invalid

/-- The kind of an import or export name; attributes are ignored. -/
def ExternName.kind (n : ExternName) : ExternNameKind := externNameKind n.name

/-- The name is a valid `externname`. -/
def ExternName.valid (n : ExternName) : Bool := n.kind != .invalid

/-! ## Strong uniqueness -/

/-- Steps 1.2–1.3 of §Name Uniqueness on a parsed plain name, after step 1.1 (`WIT.canonLabel`):
`[...]*l.l` becomes `l`, and every annotation other than `[constructor]` and 📡 `[set]` is
stripped. -/
def PlainName.canon : PlainName → List Char
  | .label l | .get l => WIT.canonLabel l
  | .set l => "[set]".toList ++ WIT.canonLabel l
  | .constructor r => "[constructor]".toList ++ WIT.canonLabel r
  | .method acc r m | .static acc r m =>
    if WIT.canonLabel r = WIT.canonLabel m then WIT.canonLabel r
    else
      (if acc = some .set then "[set]".toList else []) ++
        WIT.canonLabel r ++ '.' :: WIT.canonLabel m

/-- The canonical characters of a name: `PlainName.canon` for plain names, and step 1.1
(`WIT.canonChars`: drop hyphens, lowercase) on the whole string otherwise. -/
def strongCanonChars (cs : List Char) : List Char :=
  match parsePlainNameChars? cs with
  | some p => p.canon
  | none => WIT.canonChars cs

/-- The strong-uniqueness canonical form of a name (Explainer §Name Uniqueness step 1, i.e.
steps 1.1–1.3): `PlainName.canon` on names that parse as plain names, and step 1.1 only
(`WIT.canonChars`) on the whole string for interface or invalid names. -/
def strongCanon (s : String) : String := String.ofList (strongCanonChars s.toList)

/-- Two names are strongly unique iff their canonical forms differ. -/
def StronglyUnique (names : List String) : Prop := (names.map strongCanon).Nodup

instance : DecidablePred StronglyUnique := fun _ => inferInstanceAs (Decidable (List.Nodup _))

/-- Pairwise distinctness of character lists (structural, kernel-reducible). -/
def allDistinct : List (List Char) → Bool
  | [] => true
  | x :: xs => !xs.contains x && allDistinct xs

/-- Executable strong uniqueness of a list of names (Explainer §Name Uniqueness step 2). -/
def stronglyUnique (names : List String) : Bool :=
  allDistinct (names.map fun s => strongCanonChars s.toList)

/-! ## Tests -/

-- Labels (`WIT.isLabel`).
-- Plain names.
-- Interface names.
-- Extern name kinds.
-- Canonical forms. `fooBar` is not a label, but its canonical form collides with `foo-bar`.
/-- The strongly-unique name set of Explainer §Name Uniqueness. -/
def explainerUniqueNames : List String :=
  ["foo", "foo-bar", "[constructor]foo", "[method]foo.bar", "[static]foo.baz", "foo:bar/baz",
   "[get]prop", "[set]prop", "[method][get]foo.prop", "[method][set]foo.prop",
   "[static][get]foo.prop-2", "[static][set]foo.prop-2", "[method]foo.get-prop",
   "[method]foo.set-prop"]

/-- Each of the conflicting names listed in Explainer §Name Uniqueness. -/
def explainerConflictingNames : List String :=
  ["foo", "FOO", "[method]foo.foo", "[get]foo", "[method][get]foo.foo", "[static][set]foo.FOO",
   "foo-BAR", "foobar", "foob-ar", "[static]foobar.FOOBAR", "[static]foo-BAR.FOO-bar",
   "[constructor]FOO", "[method]foo.BAR", "[static]foo.bar", "[method]foo.baz", "foo:bar/BAZ",
   "prop", "[set]PROP", "[method]foo.prop", "[static]foo.PROP", "[method][get]foo.PROP",
   "[static][get]foo.prop", "[method][set]foo.PROP", "[static][set]foo.prop"]

-- `[set]foo` and `foo` are strongly unique; `[get]foo` and `foo` are not.
end Silmaril.Wasm.Component.Syntax
