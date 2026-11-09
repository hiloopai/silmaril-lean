module

public import Silmaril.Project.Registry.Value.Defs
public import Silmaril.Project.Registry.Room.Defs

/-!
# Silmaril projects: the attribute forms

Where a Lean declaration exists, its record is an attribute on it, like `@[answers]` on a
theorem. One field syntax `(key := value)` serves the attributes, the commands and (as TOML keys)
records files.

```lean
@[problem "demo.add.correct" (expect := thm) (title := "Addition is correct")]
def addCorrect (left right : Int) : Prop := …        -- any arity; the fields are its judgement

@[problem "demo.cnf.x2" (room := demo.rooms.cnf)]
def x2 : CNF := [[2]]                                -- a sentence of a room

@[conjecture "demo.small_bound" (title := "…")]
def Task.smallBound : Prop := ∀ n, small n → n ≤ 2   -- @[problem … (expect := OPN)]

@[value "demo.config" (format := json) (source := demo.blobs.config_json)]
def config : Json.Ast Json.Decimal := …              -- the value, and this certificate of it
```

* `@[problem "N" (k := v)*]` on `P : α₀ → … → αₙ₋₁ → Prop`. At arity 0 without fields it is
  exactly silmaril's `@[problem "N"]` (this module routes silmaril's syntax here, by a macro); at
  arity `n > 0` it adds the `predicate` record, like `silmaril problem N := P`. The fields are
  the problem's judgement (`expect`, `title`, `doc`, `model`, `spec`, `values`, `artifacts`,
  `sid`); `(expect := thm)` may be written as an identifier. With `(room := R)` the declaration is
  a sentence `φ : R.Sen` and the problem `N` is `fun M => Silmaril.Project.Room.Problem R φ M`, as for
  `silmaril problem N in R := φ`.
* `@[conjecture "N" (k := v)*]`: `@[problem "N" (expect := OPN) (k := v)*]`, for a frozen open goal.
* `@[value "N" (format := F) (source := S) (k := v)*]` on a certificate `c : V`: the value `N`,
  exactly as `[[value]]` (its bytes, `N.parses`), plus the problem `N.is` (`N.Is c`: the file
  parses to `c`) and the proved edge `N.is → N.parses` (a `decomposition`). Solve `N.is` once
  and state facts about `c`; `Value.satisfies_of_is` carries them to `N.Satisfies`. A value
  without a certificate is a `[[value]]` table.

`@[predicate "N"]` is the older spelling of `@[problem "N"]`; it also records arity 0 as a
`predicate`. Records without a Lean declaration (instances, groups, judgements of generated
problems, values without a certificate) stay in TOML, or the `silmaril <kind>` commands.
-/

public meta section

namespace Silmaril.Project

open Lean Meta Elab Command

/-- Run a command elaboration from an attribute handler, in the namespace and `open`s of the
declaration being elaborated (so that generated names are where the commands put them). -/
def runInScope (act : CommandElabM Unit) : CoreM Unit := do
  let ns ← getCurrNamespace
  let opens ← getOpenDecls
  -- outside the exported view, where theorems of this module have their proofs
  withoutExporting <| liftCommandElabM (withScope (fun sc => { sc with currNamespace := ns, openDecls := opens }) act)

/-- The name and fields of an attribute `kind "N" (k := v)*`. -/
def attrArgs (kind : String) (stx : Syntax) : CoreM (String × Fields) := do
  let some name := stx[1].isStrLit? | throwError "expected `@[{kind} \"NAME\" (key := value)*]`"
  return (name, ← elabFields kind stx[2].getArgs)

/-- `@[problem "N" (k := v)*]` on `decl`. -/
def addProblemAttr (decl : Name) (name : String) (fs : Fields) : CommandElabM Unit := do
  match fs.get? "room" with
  | some (.str r) => declareRoomProblem name r (mkCIdent decl) (fs.erase "room")
  | some _ => throwError "@[problem \"{name}\"]: `(room := R)` names a registered room"
  | none =>
    let arity ← liftTermElabM do return (← predicateArgs "problem" (← constType decl)).size
    if arity == 0 then
      -- silmaril's own attribute (`Attribute.add` does not expand macros)
      liftCoreM <| Attribute.add decl `problem (← `(attr| problem $(quote name):str))
    else
      liftCoreM (registerPredicate name decl)
    unless fs.values.isEmpty do runRecord "judgement" name fs

/-- `@[value "N" (format := F) (source := S) (k := v)*]` on the certificate `decl`. -/
def addValueAttr (decl : Name) (name : String) (fs : Fields) : CommandElabM Unit := do
  let fmt ← liftCoreM (fs.str "value" "format")
  let src ← liftCoreM (fs.str "value" "source")
  declareValue name #[(fmt, .auto src, ← getRef)] ((fs.erase "format").erase "source")
  let is := name ++ ".is"
  elabDef false (nameToLean is) #[← problemAttr is] (some (← `(Prop)))
    (← `(Silmaril.Project.Value.Is $(mkCIdent (← fullName name)) $(mkCIdent decl)))
  -- the proved edge: the certificate discharges the parse obligation
  let route := name ++ ".parses_of_is"
  elabDef true (nameToLean route) #[]
    (some (← `($(mkCIdent (← fullName is)) → $(mkCIdent (← fullName (name ++ ".parses"))))))
    (← `(fun h => Silmaril.Project.Value.parses_of_is h))
  let routeDecl ← fullName route
  runRecord "decomposition" none
    { values := #[("proof", .str routeDecl.toString)], consts := #[("proof", routeDecl)] }

/-- `@[problem "N" (k := v)*]` (written `@[problem …]`; this is its implementation). -/
syntax (name := silmaril_problem) "silmaril_problem " str (ppSpace silmarilField)* : attr

/-- `@[problem "N" (k := v)+]`: a problem with fields (its judgement). Without fields,
`@[problem "N"]` is silmaril's syntax; both run `silmaril_problem`. -/
syntax (name := problemWithFields) "problem " str (ppSpace silmarilField)+ : attr

macro_rules
  | `(attr| problem $n:str) => `(attr| silmaril_problem $n:str)

macro_rules
  | `(attr| problem $n:str $fs:silmarilField*) => `(attr| silmaril_problem $n:str $fs:silmarilField*)

/-- `@[conjecture "N" (k := v)*]`: this `Prop` is the open problem `N` (`expect := OPN`). -/
syntax (name := conjecture) "conjecture " str (ppSpace silmarilField)* : attr

/-- `@[value "N" (format := F) (source := S) (k := v)*]`: the file `S` read under `F` is the
value `N`, and this definition is what it parses to (the problem `N.is`). -/
syntax (name := value) "value " str (ppSpace silmarilField)* : attr

initialize registerBuiltinAttribute {
  name := `silmaril_problem
  descr := "state a problem over arguments (any arity), with its judgement fields"
  applicationTime := .afterTypeChecking
  add := fun decl stx kind => do
    unless kind == .global do throwError "@[problem] must be global"
    let (name, fs) ← attrArgs "problem" stx
    runInScope (addProblemAttr decl name fs)
}

initialize registerBuiltinAttribute {
  name := `conjecture
  descr := "state an open problem (a frozen goal): `@[problem … (expect := OPN)]`"
  applicationTime := .afterTypeChecking
  add := fun decl stx kind => do
    unless kind == .global do throwError "@[conjecture] must be global"
    let (name, fs) ← attrArgs "conjecture" stx
    runInScope (addProblemAttr decl name (← fs.push "conjecture" "expect" (.str "OPN")))
}

initialize registerBuiltinAttribute {
  name := `value
  descr := "declare a named value read from an artifact, with this definition as its certificate"
  applicationTime := .afterTypeChecking
  add := fun decl stx kind => do
    unless kind == .global do throwError "@[value] must be global"
    let (name, fs) ← attrArgs "value" stx
    runInScope (addValueAttr decl name fs)
}

end Silmaril.Project
