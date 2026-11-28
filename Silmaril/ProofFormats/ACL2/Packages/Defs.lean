module

public import Silmaril.Formats.SExp.CommonLisp.Defs
public import Silmaril.Logic.ACL2.Packages.Defs
public import Silmaril.Logic.ACL2.Books.Defs

public section

namespace Silmaril.ProofFormats.ACL2

open Silmaril.Formats Silmaril.Logic.ACL2

/-- The subset of read atoms needed for package setup and the nonrecursive core.
The resolved datum represents `COMMON-LISP::NIL` by the empty list. -/
inductive ResolvedAtom where
  | symbol (name : Name)
  | string (value : String)
  deriving DecidableEq, Repr

abbrev ResolvedDatum := SExp2 ResolvedAtom

inductive PackageSourceError where
  | reader
  | package (error : PackageError)
  | unsupportedCommand
  | unsupportedDefinition
  | unsupportedTerm
  | invalidDefinitionName (name : Name)
  | invalidFormals
  | unavailableName (name : Name)
  | unboundVariable (name : Name)
  | unknownFunction (name : Name)
  | wrongArity (name : Name) (expected actual : Nat)
  deriving DecidableEq, Repr

/-- Adapt the existing Common Lisp atom encoding to the package resolver. -/
def symbolRef? : CommonLisp.Atom → Option SymbolRef
  | .symbol s => some (.unqualified s)
  | .qualified p s true => some (.internal p s)
  | .qualified p s false => some (.external p s)
  | .keyword s => some (.keyword s)
  | _ => none

/-- Keep the existing tokenizer and phrase grammar. Common Lisp's apostrophe inserts
the home `QUOTE` directly, regardless of accessibility in the active package. -/
private def packageLexer : SExpReader.Lexer CommonLisp.Atom Unit (List Char) where
  size := List.length
  step chars :=
    match CommonLisp.step chars with
    | .token (.prefix (.symbol "QUOTE")) rest =>
      .token (.prefix (.qualified "COMMON-LISP" "QUOTE" true)) rest
    | .token (.atom (.string s)) rest => .token (.atom (.string s)) rest
    | .token (.atom a) rest => if (symbolRef? a).isSome then .token (.atom a) rest else .error
    | .token (.open none closer dotted) rest => .token (.open none closer dotted) rest
    | .token (.close closer) rest => .token (.close closer) rest
    | .token .dot rest => .token .dot rest
    | .eof => .eof
    | _ => .error

private def parsePackageSource (source : String) : Except PackageSourceError (List CommonLisp.Datum) := do
  let chars := source.toList
  if !chars.all (fun c => CommonLisp.isWhite c || (c.toNat ≥ 32 && c.toNat ≤ 126)) then
    throw .reader
  let some forms := SExpReader.readAll packageLexer chars | throw .reader
  return forms

private def resolveDatum (env : PackageEnv) (active : String) :
    CommonLisp.Datum → Except PackageSourceError ResolvedDatum
  | .nil => pure .nil
  | .cons x xs => return .cons (← resolveDatum env active x) (← resolveDatum env active xs)
  | .atom (.string s) => pure (.atom (.string s))
  | .atom a => do
    let some ref := symbolRef? a | throw .reader
    let name ← (env.resolve active ref).mapError .package
    if name = ⟨"COMMON-LISP", "NIL"⟩ then return .nil
    return .atom (.symbol name)

private def properList? : ResolvedDatum → Option (List ResolvedDatum)
  | .nil => some []
  | .cons x xs => (x :: ·) <$> properList? xs
  | .atom _ => none

/-- A package snapshot paired with the package for the next form in an ACL2 command stream. -/
structure PackageReader where
  private mk ::
  env : PackageEnv
  active : String

namespace PackageReader

def start (env : PackageEnv := .initial) : PackageReader := PackageReader.mk env "ACL2"

def select (reader : PackageReader) (pkg : String) : Except PackageSourceError PackageReader := do
  let active ← (reader.env.select pkg).mapError .package
  return PackageReader.mk reader.env active

/-- Read a single datum using the current package, with no command execution. -/
def read (reader : PackageReader) (source : String) : Except PackageSourceError ResolvedDatum := do
  let [form] ← parsePackageSource source | throw .reader
  resolveDatum reader.env reader.active form

private def importName : ResolvedDatum → Except PackageSourceError Name
  | .nil => pure ⟨"COMMON-LISP", "NIL"⟩
  | .atom (.symbol n) => pure n
  | _ => throw .unsupportedCommand

private def setupForm (reader : PackageReader) (datum : CommonLisp.Datum) :
    Except PackageSourceError PackageReader := do
  let form ← resolveDatum reader.env reader.active datum
  match properList? form with
  | some [.atom (.symbol ⟨"COMMON-LISP", "IN-PACKAGE"⟩), .atom (.string pkg)] =>
    reader.select pkg
  | some [.atom (.symbol ⟨"ACL2", "DEFPKG"⟩), .atom (.string pkg), imports] =>
    let imports ← match properList? imports with
      | some [] => pure []
      | some [.atom (.symbol ⟨"COMMON-LISP", "QUOTE"⟩), xs] => do
        let some names := properList? xs | throw .unsupportedCommand
        names.mapM importName
      | _ => throw .unsupportedCommand
    let env ← (reader.env.defpkg pkg imports).mapError .package
    return PackageReader.mk env reader.active
  | _ => throw .unsupportedCommand

/-- Process package commands in order. Imports must be `NIL` or a literal quoted
proper list of symbols. Each form is resolved in the environment before that form. -/
def readSetup (reader : PackageReader) (source : String) :
    Except PackageSourceError PackageReader := do
  let forms ← parsePackageSource source
  forms.foldlM setupForm reader

end PackageReader

private def elaborateCall {S : Signature} {n : Nat} (fn : Name) (args : List (Term S n)) :
    Except PackageSourceError (Term S n) :=
  match fn with
  | ⟨"COMMON-LISP", "CAR"⟩ => unary .car
  | ⟨"COMMON-LISP", "CDR"⟩ => unary .cdr
  | ⟨"COMMON-LISP", "CONSP"⟩ => unary .consp
  | ⟨"COMMON-LISP", "CONS"⟩ => binary .cons
  | ⟨"COMMON-LISP", "EQUAL"⟩ => binary .equal
  | ⟨"COMMON-LISP", "IF"⟩ =>
    match args with
    | [x, y, z] => pure (.ite x y z)
    | _ => throw (.wrongArity fn 3 args.length)
  | _ => do
    let some arity := S.arity fn | throw (.unknownFunction fn)
    if let some symbol := S.resolve fn args.length then
      return .app symbol (fun i => args[i.val]'i.isLt)
    throw (.wrongArity fn arity args.length)
where
  unary (op : Term S n → Term S n) :=
    match args with
    | [x] => pure (op x)
    | _ => throw (.wrongArity fn 1 args.length)
  binary (op : Term S n → Term S n → Term S n) :=
    match args with
    | [x, y] => pure (op x y)
    | _ => throw (.wrongArity fn 2 args.length)

mutual
  private def elaborateTerm (S : Signature) (vars : List Name) :
      ResolvedDatum → Except PackageSourceError (Term S vars.length)
    | .nil => pure .nil
    | .atom (.symbol ⟨"COMMON-LISP", "T"⟩) => pure .truth
    | .atom (.symbol name) => do
      if let some i := vars.findIdx? (fun v => decide (v = name)) then
        if h : i < vars.length then return .var ⟨i, h⟩
      throw (.unboundVariable name)
    | .cons (.atom (.symbol ⟨"COMMON-LISP", "QUOTE"⟩)) tail =>
      match properList? tail with
      | some [.nil] => pure .nil
      | some [.atom (.symbol ⟨"COMMON-LISP", "T"⟩)] => pure .truth
      | _ => throw .unsupportedTerm
    | .cons (.atom (.symbol fn)) tail => do elaborateCall fn (← elaborateArgs S vars tail)
    | _ => throw .unsupportedTerm

  private def elaborateArgs (S : Signature) (vars : List Name) :
      ResolvedDatum → Except PackageSourceError (List (Term S vars.length))
    | .nil => pure []
    | .cons x xs => return (← elaborateTerm S vars x) :: (← elaborateArgs S vars xs)
    | .atom _ => throw .unsupportedTerm
end

/-- A definition checked in the existing core. Its body only calls declarations from
the input signature, and its name is fresh in the input logical world. -/
structure PackageDefinition (W : World) where
  name : Name
  arity : Nat
  fresh : W.Fresh name
  body : Term W.signature arity

@[expose] def PackageDefinition.world {W : World} (defn : PackageDefinition W) : World :=
  W.define defn.fresh defn.body

@[expose] def PackageDefinition.event {W : World} (defn : PackageDefinition W) : Event W defn.world :=
  .defun defn.fresh defn.body

private def plainName (name : Name) : Bool :=
  name.symbol.toList.head?.any Char.isAlpha &&
    name.symbol.toList.all (fun c => c.isAlpha || c.isDigit || c == '-')

private def formalName (env : PackageEnv) : ResolvedDatum → Except PackageSourceError Name
  | .atom (.symbol name) =>
    if (env.userImports name.package).isSome && plainName name then pure name
    else throw .invalidFormals
  | _ => throw .invalidFormals

private def admitDefinitionForm (reader : PackageReader) (W : World) (form : ResolvedDatum) :
    Except PackageSourceError (PackageDefinition W) := do
  let some [.atom (.symbol ⟨"COMMON-LISP", "DEFUN"⟩), .atom (.symbol name), formals, body] :=
    properList? form | throw .unsupportedDefinition
  if name.package != reader.active || (reader.env.userImports reader.active).isNone ||
      !plainName name || name.symbol == "ACL2-PKG-WITNESS" then
    throw (.invalidDefinitionName name)
  let some formals := properList? formals | throw .invalidFormals
  let vars ← formals.mapM (formalName reader.env)
  if !(decide vars.Nodup) then throw .invalidFormals
  let body ← elaborateTerm W.signature vars body
  match h₁ : W.signature.arity name, h₂ : W.theoremAt name with
  | none, none => return ⟨name, vars.length, ⟨h₁, h₂⟩, body⟩
  | _, _ => throw (.unavailableName name)

/-- Lower one bare `defun` in a user package into a checked nonrecursive definition.
The supported bodies use formals, `T`/`NIL` (optionally quoted), core primitives,
and calls at the arity declared by the prior world. -/
def PackageReader.admitDefinition (reader : PackageReader) (W : World) (source : String) :
    Except PackageSourceError (PackageDefinition W) := do
  admitDefinitionForm reader W (← reader.read source)

/-- Check a one-definition book source. ACL2 reads the leading selector in the ACL2
package and reads the definition in the selected package. Package setup is separate. -/
def admitPackageBook (env : PackageEnv) (W : World) (source : String) :
    Except PackageSourceError (PackageDefinition W) := do
  let [header, definition] ← parsePackageSource source | throw .unsupportedDefinition
  let header ← resolveDatum env "ACL2" header
  let some [.atom (.symbol ⟨"COMMON-LISP", "IN-PACKAGE"⟩), .atom (.string pkg)] :=
    properList? header | throw .unsupportedDefinition
  let reader ← (PackageReader.start env).select pkg
  admitDefinitionForm reader W (← resolveDatum env reader.active definition)

end Silmaril.ProofFormats.ACL2
