module

public import Silmaril.Logic.ACL2.Defs

public section

namespace Silmaril.Logic.ACL2

/-- Reader names after case folding and escapes, before package lookup. -/
inductive SymbolRef where
  | unqualified (symbol : String)
  | internal (package symbol : String)
  | external (package symbol : String)
  | keyword (symbol : String)
  deriving DecidableEq, Repr

inductive PackageError where
  | unknownPackage (package : String)
  | outsideBootstrapProfile (name : Name)
  | notExternal (name : Name)
  | unsupportedKeywordExternal (symbol : String)
  | unsupportedPackageName (package : String)
  | packageConflict (package : String)
  | importConflict (package : String) (first second : Name)
  | nonHomeImport (supplied actual : Name)
  | reservedImport (name : Name)
  deriving DecidableEq, Repr

/-- The supported stock package subset and a finite, monotone table of user packages.
Each user package maps a printed name to at most one canonical import. -/
structure PackageEnv where
  private mk ::
  private packages : List (String × List Name)

namespace PackageEnv

def initial : PackageEnv := PackageEnv.mk []

private def commonLispNames : List String :=
  ["QUOTE", "IN-PACKAGE", "DEFUN", "NIL", "T", "CONS", "CAR", "CDR", "CONSP", "EQUAL", "IF"]

private def acl2Names : List String := ["DEFPKG"]

private def bootstrapPackages : List String := ["ACL2", "COMMON-LISP", "KEYWORD"]

/-- The explicit imports of a previously admitted user package, in first-occurrence order. -/
def userImports (env : PackageEnv) (pkg : String) : Option (List Name) :=
  (env.packages.find? fun entry => entry.1 == pkg).map Prod.snd

def known (env : PackageEnv) (pkg : String) : Bool :=
  bootstrapPackages.contains pkg || (env.userImports pkg).isSome

/-- A package selection validates the exact string supplied by `in-package`. -/
def select (env : PackageEnv) (pkg : String) : Except PackageError String :=
  if env.known pkg then .ok pkg else .error (.unknownPackage pkg)

private def intern (env : PackageEnv) (pkg symbol : String) (external : Bool) :
    Except PackageError Name := do
  let written : Name := ⟨pkg, symbol⟩
  if let some imports := env.userImports pkg then
    -- ACL2's defpkg imports symbols, but does not export them.
    if external then throw (.notExternal written)
    return (imports.find? fun name => name.symbol == symbol).getD written
  else if pkg == "KEYWORD" then
    -- A single colon depends on whether the keyword has previously been interned.
    if external then throw (.unsupportedKeywordExternal symbol)
    return written
  else if pkg == "COMMON-LISP" then
    if commonLispNames.contains symbol then return written
    throw (.outsideBootstrapProfile written)
  else if pkg == "ACL2" then
    if external then throw (.notExternal written)
    if commonLispNames.contains symbol then return ⟨"COMMON-LISP", symbol⟩
    if acl2Names.contains symbol then return written
    throw (.outsideBootstrapProfile written)
  else
    throw (.unknownPackage pkg)

/-- Resolve a reference to its home symbol. The active package only supplies the
qualifier for unqualified references. Interning new user symbols needs no mutable
state in this profile because their home is determined by the immutable imports. -/
def resolve (env : PackageEnv) (active : String) : SymbolRef → Except PackageError Name
  | .unqualified s => env.intern active s false
  | .internal pkg s => env.intern pkg s false
  | .external pkg s => env.intern pkg s true
  | .keyword s => env.intern "KEYWORD" s false

private def validUserPackage (pkg : String) : Bool :=
  let cs := pkg.toList
  (cs.head?.any Char.isUpper) && cs.all (fun c => c.isUpper || c.isDigit || c == '-') &&
    !(pkg.startsWith "ACL2-") &&
    !(["LISP", "CL", "CL-USER", "COMMON-LISP-USER", "USER", "BIB"].contains pkg)

private def addImport (env : PackageEnv) (pkg : String) (imports : List Name) (name : Name) :
    Except PackageError (List Name) := do
  if name.symbol == "ACL2-PKG-WITNESS" then throw (.reservedImport name)
  let actual ← env.resolve name.package (.internal name.package name.symbol)
  if actual ≠ name then throw (.nonHomeImport name actual)
  match imports.find? (fun old => old.symbol == name.symbol) with
  | none => return name :: imports
  | some old =>
    if old = name then return imports
    throw (.importConflict pkg old name)

/-- Admit an already evaluated `defpkg` import list. Redundancy compares sets of canonical
imports. Every imported home must already be resolvable, and a differing redeclaration fails.
The host's package and event-name freshness outside this profile is an external obligation. -/
def defpkg (env : PackageEnv) (pkg : String) (imports : List Name) :
    Except PackageError PackageEnv := do
  if bootstrapPackages.contains pkg then throw (.packageConflict pkg)
  if !validUserPackage pkg then throw (.unsupportedPackageName pkg)
  let imports ← imports.foldlM (env.addImport pkg) []
  if let some old := env.userImports pkg then
    if old.length = imports.length && old.all (fun name => imports.any (fun n => decide (n = name))) then
      return env
    throw (.packageConflict pkg)
  return PackageEnv.mk ((pkg, imports.reverse) :: env.packages)

end PackageEnv

end Silmaril.Logic.ACL2
