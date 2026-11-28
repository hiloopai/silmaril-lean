module

import Silmaril.ProofFormats.ACL2.Packages.Defs
import Silmaril.Logic.ACL2.Books.Thms
meta import Silmaril.ProofFormats.ACL2.Packages.Defs

open Silmaril.Logic.ACL2 Silmaril.ProofFormats.ACL2

private def requireOk {α : Type} (label : String) (result : Except PackageSourceError α) : IO α :=
  match result with
  | .ok value => pure value
  | .error err => throw (IO.userError s!"{label}: {repr err}")

private def check (label : String) (holds : Bool) : IO Unit :=
  unless holds do throw (IO.userError label)

private def reject {α : Type} (label : String) (expected : PackageSourceError)
    (result : Except PackageSourceError α) : IO Unit :=
  match result with
  | .error actual => check s!"{label}: unexpected {repr actual}" (decide (expected = actual))
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly accepted")

private def checkRead (reader : PackageReader) (source : String) (expected : ResolvedDatum) :
    IO Unit := do
  let actual ← requireOk source (reader.read source)
  check s!"{source}: unexpected {repr actual}" (decide (expected = actual))

private def homePkg : String := "SILMARIL-C2-HOME"
private def usePkg : String := "SILMARIL-C2-USE"
private def otherPkg : String := "SILMARIL-C2-OTHER"
private def takeFirst : Name := ⟨homePkg, "takeFirst"⟩
private def packageFirst : Name := ⟨usePkg, "PACKAGE-FIRST"⟩
private def car : Name := ⟨"COMMON-LISP", "CAR"⟩
private def resolved (name : Name) : ResolvedDatum := .atom (.symbol name)

public def main : IO Unit := do
  let setup ← IO.FS.readFile "tests/acl2/packages/setup.lsp"
  let homeSource ← IO.FS.readFile "tests/acl2/packages/package-home.lisp"
  let useSource ← IO.FS.readFile "tests/acl2/packages/package-use.lisp"
  let packages ← requireOk "setup" (PackageReader.start.readSetup setup)
  let useReader ← requireOk "in-package" (packages.readSetup "(in-package \"SILMARIL-C2-USE\")")
  check "active package" (useReader.active == usePkg)
  checkRead useReader "|takeFirst|" (resolved takeFirst)
  checkRead useReader "silmaril-c2-use::|takeFirst|" (resolved takeFirst)
  checkRead useReader "silmaril-c2-home::TAKEF\\irst" (resolved ⟨homePkg, "TAKEFiRST"⟩)
  checkRead useReader "silmaril-c2-home::takefirst" (resolved ⟨homePkg, "TAKEFIRST"⟩)
  checkRead useReader "silmaril-c2-other::|takeFirst|" (resolved ⟨otherPkg, "takeFirst"⟩)
  checkRead useReader "acl2::car" (resolved car)
  checkRead useReader "common-lisp:car" (resolved car)
  checkRead useReader "car" (resolved ⟨usePkg, "CAR"⟩)
  checkRead useReader "nil" (resolved ⟨usePkg, "NIL"⟩)
  checkRead useReader "'|takeFirst|"
    (.cons (resolved ⟨"COMMON-LISP", "QUOTE"⟩) (.cons (resolved takeFirst) .nil))
  checkRead useReader "(|takeFirst| . common-lisp:nil)" (.cons (resolved takeFirst) .nil)
  checkRead useReader ":|Irq:0|" (resolved ⟨"KEYWORD", "Irq:0"⟩)
  reject "ACL2 internal import" (.package (.notExternal ⟨"ACL2", "CAR"⟩))
    (useReader.read "acl2:car")
  reject "user internal import" (.package (.notExternal ⟨usePkg, "takeFirst"⟩))
    (useReader.read "silmaril-c2-use:|takeFirst|")
  reject "keyword interning history" (.package (.unsupportedKeywordExternal "FOO"))
    (useReader.read "keyword:foo")
  reject "unknown qualifier" (.package (.unknownPackage "MISSING")) (useReader.read "missing::car")
  reject "unknown bootstrap home" (.package (.outsideBootstrapProfile ⟨"ACL2", "LIST"⟩))
    (useReader.read "acl2::list")
  reject "exact package selector" (.package (.unknownPackage "silmaril-c2-use"))
    (packages.readSetup "(in-package \"silmaril-c2-use\")")
  reject "read-time evaluation" .reader (packages.read "#.(car nil)")
  reject "computed import list" (.package (.outsideBootstrapProfile ⟨"ACL2", "LIST"⟩))
    (packages.readSetup "(defpkg \"NEW\" (list 'car))")
  reject "computed import expression" .unsupportedCommand
    (packages.readSetup "(defpkg \"NEW\" (cons 'car nil))")
  reject "uninterned import" .reader (packages.readSetup "(defpkg \"NEW\" '(#:fresh))")
  reject "reserved witness import" (.package (.reservedImport ⟨homePkg, "ACL2-PKG-WITNESS"⟩))
    (packages.readSetup "(defpkg \"NEW\" '(silmaril-c2-home::acl2-pkg-witness))")
  reject "import collision"
    (.package (.importConflict "NEW" takeFirst ⟨otherPkg, "takeFirst"⟩))
    (packages.readSetup "(defpkg \"NEW\" '(silmaril-c2-use::|takeFirst| silmaril-c2-other::|takeFirst|))")
  reject "package redefinition" (.package (.packageConflict usePkg))
    (packages.readSetup "(defpkg \"SILMARIL-C2-USE\" '(defun))")
  reject "cannot refer to a later package" (.package (.unknownPackage "FUTURE"))
    (packages.readSetup "(defpkg \"NEW\" '(future::x)) (defpkg \"FUTURE\" nil)")
  reject "cannot forge the home of an import" (.package (.nonHomeImport ⟨usePkg, "takeFirst"⟩ takeFirst))
    ((packages.env.defpkg "NEW" [⟨usePkg, "takeFirst"⟩]).mapError .package)
  let extended ← requireOk "redundancy and transitive imports" (packages.readSetup
    "(defpkg \"SILMARIL-C2-USE\" '(silmaril-c2-home::|takeFirst| defun defun))
     (in-package \"SILMARIL-C2-USE\")
     (acl2::defpkg \"SILMARIL-C2-ALIAS\" '(|takeFirst|))")
  checkRead extended "silmaril-c2-alias::|takeFirst|" (resolved takeFirst)

  let home ← requireOk "home book" (admitPackageBook packages.env World.initial homeSource)
  match home.body with
  | .car (.var i) =>
    check "home definition has one formal and calls COMMON-LISP::CAR"
      (decide (home.name = takeFirst) && home.arity == 1 && i.val == 0)
  | _ => throw (IO.userError "unexpected home definition body")
  let use ← requireOk "consumer book" (admitPackageBook packages.env home.world useSource)
  match use.body with
  | .app (n := 1) target args =>
    check "consumer preserves the imported callee's home and arity"
      (decide (use.name = packageFirst ∧ target.val = takeFirst) && use.arity == 1)
    match args 0 with
    | .var i => check "consumer passes its first formal" (i.val == 0)
    | _ => throw (IO.userError "unexpected call argument")
  | _ => throw (IO.userError "unexpected consumer definition body")
  let book : Book World.initial use.world := .cons home.event (.cons use.event (.nil _))
  let _extension : World.initial.Extension use.world := book.extension
  let _checked : use.world.Checked := book.checked (World.checked_bare _)
  reject "wrong home package" (.unknownFunction ⟨otherPkg, "takeFirst"⟩)
    (admitPackageBook packages.env home.world
      (useSource.replace "(|takeFirst| x)" "(silmaril-c2-other::|takeFirst| x)"))
  reject "wrong user arity" (.wrongArity takeFirst 1 2)
    (admitPackageBook packages.env home.world (useSource.replace "(|takeFirst| x)" "(|takeFirst| x x)"))
  reject "wrong primitive identity" (.unknownFunction ⟨otherPkg, "CAR"⟩)
    (admitPackageBook packages.env World.initial (homeSource.replace "(car x)" "(silmaril-c2-other::car x)"))
  reject "wrong primitive arity" (.wrongArity car 1 2)
    (admitPackageBook packages.env World.initial (homeSource.replace "(car x)" "(car x x)"))
  reject "forward call" (.unknownFunction takeFirst)
    (admitPackageBook packages.env World.initial useSource)
  reject "self call" (.unknownFunction packageFirst)
    (admitPackageBook packages.env home.world (useSource.replace "(|takeFirst| x)" "(package-first x)"))
  reject "formal collision by resolved identity" .invalidFormals
    (admitPackageBook packages.env home.world (useSource.replace "(x)" "(x silmaril-c2-use::x)"))
  reject "a different home is a different variable" (.unboundVariable ⟨otherPkg, "X"⟩)
    (admitPackageBook packages.env home.world (useSource.replace "(|takeFirst| x)" "silmaril-c2-other::x"))
  reject "fresh definition cannot relabel an imported name" (.invalidDefinitionName takeFirst)
    (admitPackageBook packages.env home.world (useSource.replace "package-first" "|takeFirst|"))
  reject "logical name collision" (.unavailableName packageFirst)
    (admitPackageBook packages.env use.world useSource)
  IO.println "Checked ACL2 package setup, reader identities, and two typed nonrecursive definitions."
