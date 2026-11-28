module

public import Silmaril.Logic.Temporal.TLA.DataElab.Temporal.Semantics
public import Silmaril.Logic.Temporal.TLA.Resolution.Levels.Defs
import all Silmaril.Logic.Temporal.TLA.DataElab.Defs

/-! Level-checked selection of named state predicates, steps and temporal formulas. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.Temporal

open Resolution

public section

inductive Diagnostic where
  | levels (diagnostic : Levels.Diagnostic)
  | data (diagnostic : DataElab.Diagnostic)
  | notClosed (site : Site)
  | temporalPrimitive (id : BindingId)
  | wrongLevel (site : Site) (expectedAtMost actual : Levels.Level)
  | bareAction (site : Site)
  | primeInState (site : Site)
  | unsupportedFormula (site : Site)
  | expectedStatement (site : Site)
  deriving DecidableEq, Repr

structure CheckedState (signature : ExternalSignature) (fragment : Fragment := .core) where
  private mk ::
  predicate : Predicate signature fragment

structure CheckedAction (signature : ExternalSignature) (fragment : Fragment := .core) where
  private mk ::
  predicate : Predicate signature fragment

structure CheckedFormula (signature : ExternalSignature) (fragment : Fragment := .core) where
  private mk ::
  form : Form signature fragment

universe u

variable {V : Type u} {signature : ExternalSignature} {fragment : Fragment}

@[expose] noncomputable def CheckedState.toStatePred (p : CheckedState signature fragment)
    (I : Interpretation V signature fragment) (ρ : RigidEnv V) : StatePred (State V) :=
  p.predicate.toStatePred I ρ

@[expose] noncomputable def CheckedAction.toAction (p : CheckedAction signature fragment)
    (I : Interpretation V signature fragment) (ρ : RigidEnv V) : Action (State V) :=
  p.predicate.toAction I ρ

@[expose] noncomputable def CheckedFormula.toFormula (p : CheckedFormula signature fragment)
    (I : Interpretation V signature fragment) (ρ : RigidEnv V) : Formula (State V) :=
  p.form.toFormula I ρ

end

private structure Context where
  registry : CheckedRegistry
  levels : Levels.CheckedLevels

private structure Scope (signature : ExternalSignature) (fragment : Fragment) where
  locals : DataElab.Context signature fragment := []
  slots : List Nat := []

private def Context.levelAt (ctx : Context) (site : Site) : Except Diagnostic Levels.Level := do
  let some term := ctx.levels.expressionAt site | throw (.notClosed site)
  unless term.dependencies.isEmpty do throw (.notClosed site)
  return term.floor

private def Context.checkAtMost (ctx : Context) (site : Site) (ceiling : Levels.Level) :
    Except Diagnostic Unit := do
  let level ← ctx.levelAt site
  unless level.atMost ceiling do throw (.wrongLevel site ceiling level)

private def Context.target (ctx : Context) (site : Site) : Option BindingId := do
  let mod ← ctx.registry.moduleAt site.moduleId
  (·.target) <$> mod.referenceAt site.path

private def logicAt (ctx : Context) (site : Site) : Option Logic :=
  match ctx.target site with
  | some (.builtin (.symbol .infix "\\land")) => some .and
  | some (.builtin (.symbol .infix "\\lor")) => some .or
  | some (.builtin (.symbol .infix "=>")) => some .implies
  | some (.builtin (.symbol .infix "\\equiv")) => some .equiv
  | _ => none

/-- Modal aliases expand at the resolved declaration's original body site. -/
private def aliasBody (ctx : Context) (site : Site) (expr : Surface.Expr) :
    Option (Site × Surface.Expr) := do
  let .ref (.operator _) [] [] := expr | none
  let target ← ctx.target site
  let (home, body) ← (definitionBody ctx.registry target).toOption
  return (home.child .body, body)

private def exhausted (site : Site) : Diagnostic := .data ⟨site, .expansionLimit⟩

private def lowerData (ctx : Context) {signature : ExternalSignature} {fragment : Fragment}
    (scope : Scope signature fragment) (fuel : Nat)
    (site : Site) (expr : Surface.Expr) (ceiling : Levels.Level) :
    Except Diagnostic (ScopedExpr signature fragment) := do
  ctx.checkAtMost site ceiling
  let visit := DataElab.lower (signature := signature) ctx.registry fragment true false fuel
    [] scope.locals site (.expression expr)
  -- Active temporal slots are dense, so data expansion starts after them.
  let (term, _) ← (StateT.run visit scope.slots.length).mapError Diagnostic.data
  if ceiling = .state then
    if let some prime := term.firstPrime then throw (.primeInState prime)
  if valid : term.isWellFormed scope.slots = true then
    return ⟨term, scope.slots, valid⟩
  else
    throw (.data ⟨site, .invalidExpansion⟩)

private def lowerObservation (ctx : Context) {signature : ExternalSignature} {fragment : Fragment}
    (scope : Scope signature fragment) (fuel : Nat)
    (site : Site) (expr : Surface.Expr) : Except Diagnostic (Observation signature fragment) := do
  ctx.checkAtMost site .state
  if let .tuple items := expr then
    let fuel + 1 := fuel | throw (exhausted site)
    items.zipIdx.mapM fun (item, i) => lowerData ctx scope fuel (site.child (.operand i)) item .state
  else
    return [← lowerData ctx scope fuel site expr .state]

private def lowerPredicate (ctx : Context) {signature : ExternalSignature} {fragment : Fragment}
    (scope : Scope signature fragment)
    (ceiling : Levels.Level)
    (fuel : Nat) (site : Site) (expr : Surface.Expr) : Except Diagnostic (Predicate signature fragment) := do
  let remaining + 1 := fuel | throw (exhausted site)
  ctx.checkAtMost site ceiling
  let visit := lowerPredicate ctx scope ceiling remaining
  let operand := fun i => site.child (.operand i)
  let observation := lowerObservation ctx scope remaining
  if let some (home, body) := aliasBody ctx site expr then
    return ← visit home body
  match expr with
  | .action kind body subscript =>
    return .bracket kind (← visit (operand 0) body) (← observation (operand 1) subscript)
  | .prefix .unchanged arg => return .unchanged (← observation (operand 0) arg)
  | .prefix .enabled arg =>
    return .enabled (← lowerPredicate ctx scope .action remaining (operand 0) arg)
  | .prefix .negation arg => return .neg (← visit (operand 0) arg)
  | .junction kind items =>
    return .junction kind (← items.zipIdx.mapM fun (item, i) => visit (operand i) item)
  | .infix _ left right =>
    if let some op := logicAt ctx site then
      return .binary op (← visit (operand 0) left) (← visit (operand 1) right)
  | _ => pure ()
  return .data (← lowerData ctx scope (remaining + 1) site expr ceiling)
termination_by structural fuel

private def lowerForm (ctx : Context) {signature : ExternalSignature} {fragment : Fragment}
    (scope : Scope signature fragment) (fuel : Nat)
    (site : Site) (expr : Surface.Expr) : Except Diagnostic (Form signature fragment) := do
  let remaining + 1 := fuel | throw (exhausted site)
  let level ← ctx.levelAt site
  if level.atMost .state then
    return .state (← lowerPredicate ctx scope .state (remaining + 1) site expr)
  if level = .action then throw (.bareAction site)
  let visit := lowerForm ctx scope remaining
  let operand := fun i => site.child (.operand i)
  let action := lowerPredicate ctx scope .action remaining
  let observation := lowerObservation ctx scope remaining
  if let some (home, body) := aliasBody ctx site expr then
    return ← visit home body
  let bracket := fun body subscript => do
    let bracketSite := operand 0
    let depth + 1 := remaining | throw (exhausted bracketSite)
    let p ← lowerPredicate ctx scope .action depth (bracketSite.child (.operand 0)) body
    let obs ← lowerObservation ctx scope depth (bracketSite.child (.operand 1)) subscript
    return (p, obs)
  match expr with
  | .temporalQuant kind names body =>
    let binders := names.zipIdx.map fun (_, index) => declarationId site (.binder index)
    let locals := binders.map (fun id => (id, Local.expression (.flexible id))) ++ scope.locals
    let p ← lowerForm ctx { scope with locals } remaining (site.child .body) body
    return binders.foldr (Form.flexQuant kind) p
  | .rigidQuant kind binders body =>
    let groups ← (rigidBinderGroups site binders).mapError .data
    let domains ← groups.mapM fun (groupSite, names, domain) => do
      let range ← domain.mapM fun e => lowerData ctx scope remaining (groupSite.child .domain) e .state
      return (groupSite, names, range)
    let ((locals, reversed), _) ←
      ((bindRigidGroups ctx.registry scope.locals domains).run scope.slots.length).mapError .data
    let inner := ⟨locals, reversed.map Prod.fst ++ scope.slots⟩
    let p ← lowerForm ctx inner remaining (site.child .body) body
    return reversed.foldl (fun form (slot, range) => .rigidQuant kind slot range form) p
  | .prefix .always (.action .square body subscript) =>
    let (p, obs) ← bracket body subscript
    return .alwaysBracket p obs
  | .prefix .eventually (.action .angle body subscript) =>
    let (p, obs) ← bracket body subscript
    return .eventuallyAngle p obs
  | .prefix .always arg => return .always (← visit (operand 0) arg)
  | .prefix .eventually arg => return .eventually (← visit (operand 0) arg)
  | .prefix .negation arg => return .neg (← visit (operand 0) arg)
  | .infix .leadsTo left right => return .leadsTo (← visit (operand 0) left) (← visit (operand 1) right)
  | .infix _ left right =>
    if let some op := logicAt ctx site then
      return .binary op (← visit (operand 0) left) (← visit (operand 1) right)
    throw (.unsupportedFormula site)
  | .junction kind items =>
    return .junction kind (← items.zipIdx.mapM fun (item, i) => visit (operand i) item)
  | .fairness kind subscript body =>
    return .fairness kind (← action (operand 1) body) (← observation (operand 0) subscript)
  | _ => throw (.unsupportedFormula site)
termination_by structural fuel

private def checkedContext (registry : CheckedRegistry) (externalLevels : Levels.ExternalLevels)
    (signature : ExternalSignature) : Except Diagnostic Context := do
  let levels ← (Levels.check registry externalLevels).mapError .levels
  -- A data primitive may be evaluated in a noncontributing argument slot.
  -- Its interpretation still cannot supply a temporal value there.
  for (binding, level) in externalLevels do
    if level.floor = .temporal && (signature binding).isSome then
      throw (.temporalPrimitive binding)
  return ⟨registry, levels⟩

private def select (registry : CheckedRegistry) (externalLevels : Levels.ExternalLevels)
    (signature : ExternalSignature) (id : BindingId) :
    Except Diagnostic (Context × Site × Surface.Expr) := do
  let (home, body) ← (definitionBody registry id).mapError .data
  return (← checkedContext registry externalLevels signature, home.child .body, body)

/-- Select a constant- or state-level source definition. ENABLED binds its own
successor and can appear in a state predicate. -/
public def lowerState (registry : CheckedRegistry) (externalLevels : Levels.ExternalLevels)
    (signature : ExternalSignature) (maxDepth : Nat) (id : BindingId) (fragment : Fragment := .core) :
    Except Diagnostic (CheckedState signature fragment) := do
  let (ctx, site, body) ← select registry externalLevels signature id
  return ⟨← lowerPredicate (signature := signature) ctx {} .state maxDepth site body⟩

/-- Select a constant-, state- or action-level source definition as a raw
two-endpoint relation. -/
public def lowerAction (registry : CheckedRegistry) (externalLevels : Levels.ExternalLevels)
    (signature : ExternalSignature) (maxDepth : Nat) (id : BindingId) (fragment : Fragment := .core) :
    Except Diagnostic (CheckedAction signature fragment) := do
  let (ctx, site, body) ← select registry externalLevels signature id
  return ⟨← lowerPredicate (signature := signature) ctx {} .action maxDepth site body⟩

/-- Select a formula from the same registry that produced its level annotations.
A constant or state predicate can itself be a formula. -/
public def lowerFormula (registry : CheckedRegistry) (externalLevels : Levels.ExternalLevels)
    (signature : ExternalSignature) (maxDepth : Nat) (id : BindingId) (fragment : Fragment := .core) :
    Except Diagnostic (CheckedFormula signature fragment) := do
  let (ctx, site, body) ← select registry externalLevels signature id
  return ⟨← lowerForm (signature := signature) ctx {} maxDepth site body⟩

/-- Lower an anonymous, proof-free theorem expression at its resolved module unit.
The expression is read from the checked registry and lowered at its original body
site. This selects a statement for interpretation, without checking a proof. -/
public def lowerStatement (registry : CheckedRegistry) (externalLevels : Levels.ExternalLevels)
    (signature : ExternalSignature) (maxDepth : Nat) (site : Site) (fragment : Fragment := .core) :
    Except Diagnostic (CheckedFormula signature fragment) := do
  let some source := (registry.moduleAt site.moduleId).bind (·.source)
    | throw (.expectedStatement site)
  let [.unit index] := site.path | throw (.expectedStatement site)
  let some (.theoremDecl ⟨none, .expr body, none⟩) := source.units[index]?
    | throw (.expectedStatement site)
  let ctx ← checkedContext registry externalLevels signature
  return ⟨← lowerForm (signature := signature) ctx {} maxDepth (site.child .body) body⟩

end Silmaril.Logic.Temporal.TLA.DataElab.Temporal
