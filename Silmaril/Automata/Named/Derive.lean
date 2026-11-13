module

public import Silmaril.Automata.Named.Defs
public import Lean.Elab.Command
public import Lean.Elab.Tactic

/-!
# Deriving `FinNamed`: the command `silmaril_finite`

`silmaril_finite T` adds the instance `FinNamed T` for an inductive type `T` without
parameters or indices, not recursive, whose constructor arguments are not dependent and have
`FinNamed` instances themselves (for example `Bool` or another derived type):

* `elems` enumerates the constructors in declaration order, and the arguments of each
  constructor in the order of their own `elems` (the last argument varies fastest);
* `name` is `c`, `c(a₁,…,aₙ)` or, for a structure, `(a₁,…,aₙ)` (see `FinNamed`);
* `complete` is proved by case analysis, and `nodup` (distinct names) by `decide`, so a
  derivation whose names collide fails when the command runs instead of producing a wrong
  instance;
* it also adds `Fintype T := FinNamed.toFintype T`, so the decision procedures of
  `Silmaril.Automata.Decide` apply (do not combine with `deriving Fintype`).

The command elaborates an ordinary `instance` declaration: the kernel checks every proof, and
nothing is trusted beyond the standard axioms.
-/

public meta section

namespace Silmaril.Automata

open Lean Elab Command Meta

/-- `silmaril_finite T`: derive `FinNamed T`. -/
syntax (name := silmaritFiniteCmd) "silmaril_finite " ident : command

/-- The arity of each constructor of `T`, rejecting what the derivation does not support. -/
def finiteCtors (T : Name) : CommandElabM (List (Name × Nat)) := do
  let env ← getEnv
  let some (.inductInfo info) := env.find? T
    | throwError "silmaril_finite: {T} is not an inductive type"
  unless info.numParams == 0 && info.numIndices == 0 do
    throwError "silmaril_finite: {T} has parameters or indices; only plain inductive types are supported"
  if info.isRec then throwError "silmaril_finite: {T} is recursive, so it is not finite"
  info.ctors.mapM fun c => do
    let some (.ctorInfo ci) := env.find? c | throwError "silmaril_finite: {c} is not a constructor"
    let n ← liftTermElabM <| forallTelescope ci.type fun xs _ => do
      for x in xs do
        let ty ← inferType x
        if ty.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then
          throwError "silmaril_finite: {c} has a dependent argument"
      return xs.size
    return (c, n)

@[command_elab silmaritFiniteCmd]
def elabSilmarilFinite : CommandElab := fun stx => do
  let T ← liftCoreM <| realizeGlobalConstNoOverload stx[1]
  let ctors ← finiteCtors T
  let single := ctors.length == 1
  let tId := mkIdent T
  -- elems
  let mut elemParts : Array Term := #[]
  for (c, n) in ctors do
    let xs := (List.range n).map fun i => mkIdent (.mkSimple s!"a{i}")
    let app : Term ← `($(mkIdent c) $(xs.toArray)*)
    let mut t : Term ← `([$app])
    for x in xs.reverse do
      t ← `(List.flatMap (fun $x => $t) Silmaril.Automata.FinNamed.elems)
    elemParts := elemParts.push t
  let elems ← elemParts.foldlM (init := ← `(([] : List $tId))) fun acc t => `($acc ++ $t)
  -- name
  let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  for (c, n) in ctors do
    let xs := (List.range n).map fun i => mkIdent (.mkSimple s!"a{i}")
    let base := if single && n > 0 then "" else c.getString!
    let nm : Term ← if n == 0 then pure (Syntax.mkStrLit base) else do
      let mut body : Term ← `($(Syntax.mkStrLit (base ++ "(")))
      for h : i in [0:n] do
        let x := xs[i]!
        let sep := if i + 1 == n then ")" else ","
        body ← `($body ++ Silmaril.Automata.FinNamed.name $x ++ $(Syntax.mkStrLit sep))
      pure body
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $(mkIdent c) $(xs.toArray)* => $nm))
  let cmd ← `(command|
    instance : Silmaril.Automata.FinNamed $tId where
      elems := $elems
      name := fun x => match x with $alts:matchAlt*
      complete := by
        intro x; cases x <;> simp [Silmaril.Automata.FinNamed.complete]
      nodup := by decide +kernel)
  elabCommand cmd
  elabCommand (← `(command|
    instance : Fintype $tId := Silmaril.Automata.FinNamed.toFintype $tId))

end Silmaril.Automata
