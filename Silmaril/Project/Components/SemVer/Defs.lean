module

public import Silmaril.Project.Components.Defs
public import Silmaril.Wasm.Wit.Text.Parse.Defs
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Data.List.Lex
public import Mathlib.Data.String.Basic
public import Mathlib.Order.WithBot

/-!
# Registry references and SemVer precedence

Registries name a release `namespace:name@version` (WIT package names, wasm-pkg-tools, warg,
OCI tags), with a [SemVer 2.0.0](https://semver.org/spec/v2.0.0.html) version. This module adds:

* **Precedence** (SemVer §11). `key` maps a version to a lexicographic key: major, minor
  and patch numerically, then the pre-release, where *no* pre-release is the top element
  (`1.0.0-rc.1 < 1.0.0`), and a pre-release is a list of identifiers compared lexicographically
  (a prefix is smaller), numeric identifiers numerically and below alphanumeric ones, which are
  compared character by character (ASCII order). Build metadata is ignored. `Prec a b` (`a` precedes `b`) is
  `key a < key b`, so it is a strict order (`Silmaril.Project.Components.SemVer.Thms`).
* **Compatibility**, the rule wit-component and Cargo's `^` use to match a requested version
  against an available one: two release versions (no pre-release) are compatible when they
  have the same major version `≥ 1`, or major `0` and the same minor version `≥ 1`, or are
  `0.0.p` with the same `p` (`track`). `Upgrade a b`: `b` is compatible with `a`
  and does not precede it.
* **Parsing references.** `parseVersion?` reads SemVer text with the WIT text parser's
  `parseVer`; `parseRef?` reads `ns:name` or `ns:name@version` and accepts only valid package
  names (`Wit.PackageName.Valid`). Both invert the printers on valid input
  (`parseRef?_ref`, `parseVersion?_str`).

String order is not precedence: `"0.2.12" < "0.2.6"` character by character, while `0.2.6` precedes
`0.2.12` (`SemVer.Thms`, `str_lt_but_prec`). The wasmtime v50.0.1 preview1 adapter imports
`wasi:filesystem/preopens@0.2.6` next to `@0.2.12` interfaces; the two versions are compatible,
and the embedded world's `0.2.12` is the newer one.

A Silmaril addition.
-/

@[expose] public section
namespace Silmaril.Project.Components.SemVer

open Silmaril.Wasm Silmaril.Project.Components

/-! ## Precedence -/

/-- The key of a pre-release identifier: numeric identifiers (digits only) by value, below
alphanumeric ones. -/
abbrev PreKey : Type := Lex (Nat ⊕ List Char)

/-- A numeric pre-release identifier: non-empty, digits only. -/
def isNumericId (s : String) : Bool := !s.toList.isEmpty && s.toList.all Char.isDigit

/-- The precedence key of a pre-release identifier. -/
def preKey (s : String) : PreKey :=
  if isNumericId s then toLex (.inl ((Silmaril.Wasm.Component.Wat.parseNat s.toList).getD 0))
  else toLex (.inr s.toList)

/-- The precedence key of a version: `(major, minor, patch, pre)` lexicographically, with no
pre-release as the top element. -/
abbrev VersionKey : Type := Lex (Nat × Lex (Nat × Lex (Nat × WithTop (List PreKey))))

/-- The pre-release part of the key. -/
def preKeys (pre : List String) : WithTop (List PreKey) :=
  if pre = [] then ⊤ else ((pre.map preKey : List PreKey) : WithTop (List PreKey))

/-- The precedence key of a version (build metadata ignored). -/
def key (v : Wit.Version) : VersionKey :=
  toLex (v.major, toLex (v.minor, toLex (v.patch, preKeys v.pre)))

/-- **SemVer precedence**: `a` precedes `b`. -/
def Prec (a b : Wit.Version) : Prop := key a < key b

/-- `a` precedes `b` or has the same precedence. -/
def PrecLe (a b : Wit.Version) : Prop := key a ≤ key b

instance (a b : Wit.Version) : Decidable (Prec a b) := inferInstanceAs (Decidable (_ < _))
instance (a b : Wit.Version) : Decidable (PrecLe a b) := inferInstanceAs (Decidable (_ ≤ _))

/-! ## Compatibility -/

/-- The compatibility track of a version: `(major, 0, 0)` for major `≥ 1`, `(0, minor, 0)` for
`0.minor.x` with minor `≥ 1`, and `(0, 0, patch)` otherwise. -/
def track (v : Wit.Version) : Nat × Nat × Nat :=
  if v.major ≠ 0 then (v.major, 0, 0) else if v.minor ≠ 0 then (0, v.minor, 0) else (0, 0, v.patch)

/-- **Compatible versions**: two releases (no pre-release) on one track. -/
def Compatible (a b : Wit.Version) : Prop :=
  a.pre = [] ∧ b.pre = [] ∧ track a = track b

instance (a b : Wit.Version) : Decidable (Compatible a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **`b` is an upgrade of `a`**: compatible, and `a` precedes `b` or has its precedence. -/
def Upgrade (a b : Wit.Version) : Prop := Compatible a b ∧ PrecLe a b

instance (a b : Wit.Version) : Decidable (Upgrade a b) := inferInstanceAs (Decidable (_ ∧ _))

/-! ## Parsing -/

/-- SemVer text to a version (the WIT text parser's `parseVer`; build and pre-release
identifiers are not checked, see `parseValidVersion?`). -/
def parseVersion? (s : String) : Option Wit.Version := Wit.Text.Parse.parseVer s.toList

/-- SemVer text to a valid version. -/
def parseValidVersion? (s : String) : Option Wit.Version :=
  (parseVersion? s).bind fun v => if v.Valid then some v else none

/-- A reference `ns:name` or `ns:name@version`, as characters. -/
def parseRefChars (cs : List Char) : Option Wit.PackageName :=
  match Wit.Text.Parse.splitFirst ':' cs with
  | (_, none) => none
  | (ns, some rest) =>
    match Wit.Text.Parse.splitFirst '@' rest with
    | (name, none) => some ⟨String.ofList ns, String.ofList name, none⟩
    | (name, some v) =>
      (Wit.Text.Parse.parseVer v).map fun v => ⟨String.ofList ns, String.ofList name, some v⟩

/-- **A registry reference** `ns:name` or `ns:name@version`, as a valid package name. -/
def parseRef? (s : String) : Option Wit.PackageName :=
  (parseRefChars s.toList).bind fun p => if p.Valid then some p else none

/-- The reference `ns:name@version` of a package name (`Release.ref` of a release). -/
def refOf (p : Wit.PackageName) : String :=
  p.ns ++ ":" ++ p.name ++ (match p.version with
    | some v => "@" ++ Wit.Version.str v
    | none => "")

/-- A release from a reference and a digest. -/
def releaseOfRef? (s : String) (d : Digest) : Option Release :=
  (parseRef? s).map fun p => ⟨p, d⟩

/-- A binary package name `ns:name@version` (version as text), parsed. -/
def binVersion? (p : Wit.Binary.PackageName) : Option Wit.Version :=
  p.version.bind parseVersion?

end Silmaril.Project.Components.SemVer

end
