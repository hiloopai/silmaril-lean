module

public import Silmaril.Logic.Temporal.TLA.Resolution.Defs
public import Silmaril.Logic.Temporal.TLA.Resolution.Levels.Summaries

/-!
# Compositional TLA+ expression levels

Check already-resolved first-order expressions against explicit level rules.
The result classifies source syntax and carries call constraints. See
`docs/projects/tla-expression-levels.md`.
-/

namespace Silmaril.Logic.Temporal.TLA.Resolution.Levels

open Surface

public section

inductive Unsupported where
  | operatorParameter | operatorArgument | expression | declaration | instanceImplicitBinding
  deriving DecidableEq, Repr

inductive DiagnosticKind where
  | unsupported (form : Unsupported)
  | missingExternalSignature (id : BindingId)
  | duplicateExternalSignature (id : BindingId)
  | unexpectedExternalSignature (id : BindingId)
  | signatureArity (id : BindingId) (expected actual : Nat)
  | missingReference
  | missingBinding (id : BindingId)
  | missingSummary (id : BindingId)
  | missingOldValue (id : BindingId)
  | missingInstancePlan
  | substitutionLevel (target : BindingId) (ceiling actual : Level)
  | instanceReplay (home : Site) (cause : DiagnosticKind)
  | inconsistentArity (expected actual : Nat)
  | failedRequirement (requirement : Requirement)
  deriving DecidableEq, Repr

structure Diagnostic where
  /-- The site being checked. A failed call also reports the requirement's origin. -/
  site : Site
  kind : DiagnosticKind
  deriving DecidableEq, Repr

structure CheckedLevels where
  private mk ::
  expressions : List (Site × LevelTerm)
  operators : List (BindingId × OperatorSummary)
  deriving Repr

def CheckedLevels.expressionAt (checked : CheckedLevels) (site : Site) : Option LevelTerm :=
  checked.expressions.lookup site

def CheckedLevels.operatorAt (checked : CheckedLevels) (id : BindingId) : Option OperatorSummary :=
  checked.operators.lookup id

end

private def weighted (floor : Level) (arguments : List ArgumentLevel) : ExternalSignature :=
  ⟨floor, arguments⟩

private def propagating (arity : Nat) (ceiling : Level) : ExternalSignature :=
  weighted .constant (List.replicate arity ⟨ceiling, true⟩)

private def logicalNames : List String := ["\\land", "\\lor", "=>", "\\equiv"]

/-- Named built-in ceilings and weights for the supported level profile. The
checker also applies the syntax guard for temporal modalities and the mixed
action/temporal guard for binary logical connectives. -/
public def builtinSignature (name : Name) : Option ExternalSignature :=
  match name.canonical with
  | .ident "TRUE" | .ident "FALSE" | .ident "BOOLEAN" | .ident "STRING" =>
    some (propagating 0 .constant)
  | .symbol .postfix "'" => some (weighted .action [⟨.state, false⟩])
  | .symbol .prefix "\\lnot" => some (propagating 1 .temporal)
  | .symbol .prefix "SUBSET" | .symbol .prefix "UNION" | .symbol .prefix "DOMAIN" =>
    some (propagating 1 .action)
  | .symbol .prefix "ENABLED" => some (weighted .state [⟨.action, false⟩])
  | .symbol .prefix "UNCHANGED" => some (weighted .action [⟨.state, false⟩])
  | .symbol .prefix "[]" | .symbol .prefix "<>" => some (weighted .temporal [⟨.temporal, false⟩])
  | .symbol .infix "~>" => some (weighted .temporal [⟨.temporal, false⟩, ⟨.temporal, false⟩])
  | .symbol .infix spelling =>
    if spelling ∈ logicalNames then some (propagating 2 .temporal)
    else if spelling ∈ ["=", "/=", "\\subseteq", "\\in", "\\notin", "\\",
        "\\intersect", "\\union", "\\times"] then some (propagating 2 .action)
    else none
  | _ => none

private structure Analysis where
  term : LevelTerm := {}
  requirements : List Requirement := []

private structure CheckerState where
  expressions : List (Site × LevelTerm) := []
  operators : List (BindingId × OperatorSummary) := []

private abbrev CheckM := StateT CheckerState (Except Diagnostic)

private def failAt {α : Type} (site : Site) (kind : DiagnosticKind) : CheckM α :=
  throw ⟨site, kind⟩

private def retain (site : Site) (requirements : List Requirement) :
    CheckM (List Requirement) := do
  let mut pending := []
  for requirement in requirements do
    unless requirement.condition.holds (fun _ => .constant) do
      failAt site (.failedRequirement requirement)
    if requirement.condition.dependsOnFormals then
      pending := requirement :: pending
  return pending.reverse

private def addCondition (analysis : Analysis) (site : Site) (condition : Condition) :
    CheckM Analysis := do
  let pending ← retain site [⟨site, condition⟩]
  return { analysis with requirements := analysis.requirements ++ pending }

private def applySignature (site : Site) (signature : ExternalSignature)
    (operands : List (Site × Analysis)) : CheckM Analysis := do
  unless operands.length = signature.arguments.length do
    failAt site (.inconsistentArity signature.arguments.length operands.length)
  let mut result := LevelTerm.fixed signature.floor
  let mut requirements := operands.flatMap fun (_, operand) => operand.requirements
  for (argument, operandSite, operand) in signature.arguments.zip operands do
    let pending ← retain operandSite [⟨operandSite, .atMost operand.term argument.maximum⟩]
    requirements := requirements ++ pending
    if argument.contributes then
      result := result.join operand.term
  return ⟨result, requirements⟩

private def applySummary (site : Site) (summary : OperatorSummary) (operands : List Analysis) :
    CheckM Analysis := do
  let some (result, requirements) := summary.instantiate (operands.map Analysis.term)
    | failAt site (.inconsistentArity summary.parameters.length operands.length)
  let pending ← retain site requirements
  return ⟨result, operands.flatMap Analysis.requirements ++ pending⟩

private def isMatchingBracket (name : Name) : Expr → Bool
  | .action .square _ _ => name = .symbol .prefix "[]"
  | .action .angle _ _ => name = .symbol .prefix "<>"
  | _ => false

private def applyBuiltin (site : Site) (name : Name) (sourceArgs : List Expr)
    (operands : List (Site × Analysis)) : CheckM Analysis := do
  let some signature := builtinSignature name | failAt site (.unsupported .expression)
  let result ← applySignature site signature operands
  match name, sourceArgs, operands with
  | .symbol .prefix spelling, [source], [(argSite, operand)] =>
    if (spelling = "[]" || spelling = "<>") && !isMatchingBracket name source then
      addCondition result argSite (.nonAction operand.term)
    else return result
  | .symbol .infix "~>", _, _ =>
    operands.foldlM (fun current (argSite, operand) =>
      addCondition current argSite (.nonAction operand.term)) result
  | .symbol .infix spelling, _, _ =>
    if spelling ∈ logicalNames then
      addCondition result site (.noMixedActionTemporal (operands.map fun (_, arg) => arg.term))
    else return result
  | _, _, _ => return result

private structure Context where
  registry : CheckedRegistry
  sourceModule : CheckedModule
  replaying : Bool
  oldValues : List (BindingId × LevelTerm) := []

private def applyBinding (context : Context) (site : Site) (binding : Binding)
    (sourceArgs : List Expr) (operands : List (Site × Analysis)) : CheckM Analysis := do
  match binding.id, binding.kind with
  | .builtin name, _ =>
    if context.replaying && name = .symbol .prefix "ENABLED" then
      failAt site (.unsupported .instanceImplicitBinding)
    applyBuiltin site name sourceArgs operands
  | _, .formal => return ⟨.parameter binding.id, []⟩
  | _, .rigid => return ⟨.fixed .constant, []⟩
  | _, .flexible => return ⟨.fixed .state, []⟩
  | _, _ =>
    let some summary := (← get).operators.lookup binding.id
      | failAt site (.missingSummary binding.id)
    applySummary site summary (operands.map Prod.snd)

private def checkApplication (visit : Site → Expr → CheckM Analysis) (context : Context)
    (site : Site) (args : List (Site × OpArg)) : CheckM Analysis := do
  let some use := context.sourceModule.referenceAt site.path | failAt site .missingReference
  let some binding := context.registry.findBinding use.target | failAt site (.missingBinding use.target)
  unless args.length = binding.slots.length do
    failAt site (.inconsistentArity binding.slots.length args.length)
  let operands ← (binding.slots.zip args).mapM fun (slot, argSite, arg) => do
    if let .operator _ := slot then failAt argSite (.unsupported .operatorArgument)
    let .expr value := arg | failAt argSite (.unsupported .operatorArgument)
    return (value, argSite, ← visit argSite value)
  applyBinding context site binding (operands.map Prod.fst) (operands.map Prod.snd)

private def positionalArguments (site : Site) (child : Nat → Step) (args : List OpArg) :
    List (Site × OpArg) :=
  args.zipIdx.map fun (arg, index) => (site.child (child index), arg)

private def formalId (site : Site) (index : Nat) : BindingId :=
  .declared (site.child (.parameter index))

private def checkOperatorDefinition (visit : Site → Expr → CheckM Analysis) (site : Site)
    (definition : Definition) : CheckM OperatorSummary := do
  let .operator _ head body := definition | failAt site (.unsupported .declaration)
  let arity ← match head with
    | .ident _ params =>
      for (param, index) in params.zipIdx do
        match param with
        | .ident _ 0 => pure ()
        | _ => failAt (site.child (.parameter index)) (.unsupported .operatorParameter)
      pure params.length
    | .infix .. => pure 2
    | _ => pure 1
  let result ← visit (site.child .body) body
  let summary : OperatorSummary :=
    ⟨(List.range arity).map (formalId site), result.term, result.requirements⟩
  modify fun state => { state with operators := (.declared site, summary) :: state.operators }
  return summary

private def checkBounded (visit : Site → Expr → CheckM Analysis) (site : Site) (bounds : List Bound)
    (body : Expr) (bodyCeiling : Level) (temporalQuantifier : Bool := false) : CheckM Analysis := do
  let ranges ← bounds.zipIdx.mapM fun (bound, index) => do
    let domain := (site.child (.bound index)).child .domain
    return (domain, ← visit domain bound.domain)
  let bodySite := site.child .body
  let checkedBody ← visit bodySite body
  let mut result ← applySignature site
    (weighted .constant (⟨bodyCeiling, true⟩ :: List.replicate ranges.length ⟨.action, true⟩))
    ((bodySite, checkedBody) :: ranges)
  if temporalQuantifier then
    for (domain, range) in ranges do
      result ← addCondition result domain (.temporalQuantifierBound checkedBody.term range.term)
  return result

-- Calculate the body's level with self at the bottom, then recheck its uses at
-- the inferred level. Level propagation consists of joins and fixed weights.
private def checkDefinition (visit : Site → Expr → CheckM Analysis) (site : Site)
    (definition : Definition) : CheckM OperatorSummary := do
  let .function _ _ [bound@⟨.names [_], _⟩] body := definition
    | checkOperatorDefinition visit site definition
  let before ← get
  let bindSelf (term : LevelTerm) : CheckM Unit :=
    modify fun state => { state with operators := (.declared site, ⟨[], term, []⟩) :: state.operators }
  bindSelf (.fixed .constant)
  let initial ← checkBounded visit site [bound] body .action
  set before
  bindSelf initial.term
  let result ← checkBounded visit site [bound] body .action
  let summary : OperatorSummary := ⟨[], result.term, result.requirements⟩
  modify fun state =>
    { state with operators := (.declared site, summary) :: state.operators.filter (·.1 ≠ .declared site) }
  return summary

private instance : Inhabited (CheckM Analysis) :=
  ⟨failAt ⟨"", []⟩ (.unsupported .expression)⟩

-- The visitor follows the same child paths as name resolution.
private partial def checkExpr (context : Context) (site : Site) (expression : Expr) :
    CheckM Analysis := do
  let visit := checkExpr context
  let child (step : Step) (expr : Expr) : CheckM (Site × Analysis) := do
    let childSite := site.child step
    return (childSite, ← visit childSite expr)
  let operands (items : List Expr) : CheckM (List (Site × Analysis)) :=
    items.zipIdx.mapM fun (expr, index) => child (.operand index) expr
  let structural (items : List Expr) (ceiling : Level) : CheckM Analysis := do
    applySignature site (propagating items.length ceiling) (← operands items)
  let apply (items : List Expr) : CheckM Analysis :=
    checkApplication visit context site (positionalArguments site .operand (items.map .expr))
  let checked ← match expression with
    | .literal _ => pure ({} : Analysis)
    | .ref (.operator _) args [] =>
      checkApplication visit context site (positionalArguments site .argument args)
    | .ref (.operator head) args (selector :: rest) => do
      let some (_, segments) := qualifiedCall site head args (selector :: rest)
        | failAt site (.unsupported .expression)
      checkApplication visit context site (qualifiedArguments segments)
    | .prefix _ arg | .postfix _ arg => apply [arg]
    | .infix _ left right => apply [left, right]
    | .cartesian items | .setEnum items | .tuple items => structural items .action
    | .junction _ items => do
      let args ← operands items
      let result ← applySignature site (propagating items.length .temporal) args
      addCondition result site (.noMixedActionTemporal (args.map fun (_, arg) => arg.term))
    | .ifThenElse condition yes no => structural [condition, yes, no] .temporal
    | .cases arms other => do
      let pairs ← arms.zipIdx.mapM fun (arm, index) => do
        let armSite := site.child (.arm index)
        let condition := armSite.child (.operand 0)
        let result := armSite.child (.operand 1)
        return [(condition, ← visit condition arm.condition), (result, ← visit result arm.result)]
      let fallback ← other.toList.mapM (child .other)
      let args := pairs.flatten ++ fallback
      applySignature site (propagating args.length .temporal) args
    | .letIn declarations body => do
      let mut requirements := []
      for (decl, index) in declarations.zipIdx do
        let declSite := site.child (.letDecl index)
        let .definition definition := decl | failAt declSite (.unsupported .declaration)
        let summary ← checkDefinition visit declSite definition
        let defaults := summary.parameters.map fun id => (id, LevelTerm.fixed .constant)
        requirements := requirements ++
          (← retain declSite (summary.requirements.map (·.substitute defaults)))
      let result ← visit (site.child .body) body
      pure { result with requirements := requirements ++ result.requirements }
    | .temporalQuant _ _ body => do
      let bodySite := site.child .body
      let checkedBody ← visit bodySite body
      let result ← addCondition checkedBody bodySite (.nonAction checkedBody.term)
      pure { result with term := .fixed .temporal }
    | .rigidQuant _ (.unbounded _) body => visit (site.child .body) body
    | .rigidQuant _ (.bounded bounds) body =>
      checkBounded visit site bounds body .temporal true
    | .choose _ domain predicate => do
      let range ← domain.toList.mapM (child .domain)
      let args := range ++ [← child .body predicate]
      applySignature site (propagating args.length .action) args
    | .setFilter _ domain predicate => do
      let args := [← child .domain domain, ← child .body predicate]
      applySignature site (propagating args.length .action) args
    | .setMap body bounds => checkBounded visit site bounds body .action
    | .function bounds body => checkBounded visit site bounds body .temporal
    | .functionSet domain range => structural [domain, range] .action
    | .index fn args => structural (fn :: args) .action
    | .record fields | .recordSet fields => do
      let args ← fields.zipIdx.mapM fun (field, index) => child (.field index) field.value
      let ceiling := match expression with | .recordSet _ => Level.action | _ => .temporal
      applySignature site (propagating args.length ceiling) args
    | .field record _ => structural [record] .action
    | .except base updates => do
      let (baseSite, initial) ← child (.operand 0) base
      let mut result ← addCondition initial baseSite (.atMost initial.term .action)
      for (update, index) in updates.zipIdx do
        let clause := site.child (.update index)
        let indices ← update.path.zipIdx.flatMapM fun (component, part) => do
          let .index args := component | return []
          args.zipIdx.mapM fun (arg, argIndex) => do
            let argSite := (clause.child (.updateComponent part)).child (.argument argIndex)
            return (argSite, ← visit argSite arg)
        let selector ← applySignature clause (propagating indices.length .action) indices
        -- A clause reads the preceding updated base through its own selector.
        let selected := result.term.join selector.term
        let inner := { context with oldValues := (.declared clause, selected) :: context.oldValues }
        let rhsSite := clause.child .body
        let rhs ← checkExpr inner rhsSite update.value
        let rhs ← addCondition rhs rhsSite (.atMost rhs.term .action)
        result := ⟨selected.join rhs.term,
          result.requirements ++ selector.requirements ++ rhs.requirements⟩
      pure result
    | .oldValue => do
      let some reference := context.sourceModule.referenceAt site.path | failAt site .missingReference
      let some term := context.oldValues.lookup reference.target
        | failAt site (.missingOldValue reference.target)
      pure ⟨term, []⟩
    | .action _ body subscript => do
      let args ← operands [body, subscript]
      applySignature site (weighted .action [⟨.action, false⟩, ⟨.state, false⟩]) args
    | .fairness _ subscript action => do
      if context.replaying then failAt site (.unsupported .instanceImplicitBinding)
      let args ← operands [subscript, action]
      applySignature site (weighted .temporal [⟨.state, false⟩, ⟨.action, false⟩]) args
    | _ => failAt site (.unsupported .expression)
  let result := { checked with requirements := checked.requirements.eraseDups }
  modify fun state => { state with expressions := (site, result.term) :: state.expressions }
  return result

private def summaryFromSignature (site : Site) (signature : ExternalSignature) : OperatorSummary :=
  let params := (List.range signature.arguments.length).map (formalId site)
  let pairs := params.zip signature.arguments
  let term := pairs.foldl (fun result (id, arg) =>
    if arg.contributes then result.join (.parameter id) else result) (.fixed signature.floor)
  let requirements := pairs.zipIdx.filterMap fun ((id, arg), index) =>
    if arg.maximum = .temporal then none
    else some ⟨site.child (.parameter index), .atMost (.parameter id) arg.maximum⟩
  ⟨params, term, requirements⟩

private def registerDeclaration (external : ExternalLevels) (hasSource : Bool) (binding : Binding) :
    CheckM Unit := do
  let .declared site := binding.id | return ()
  let signature ← match binding.kind with
    | .variable => pure (weighted .state [])
    | .constant => pure (propagating binding.slots.length .temporal)
    | .operator =>
      if hasSource then return ()
      for (slot, index) in binding.slots.zipIdx do
        if let .operator _ := slot then
          failAt (site.child (.parameter index)) (.unsupported .operatorParameter)
      let some found := external.lookup binding.id | failAt site (.missingExternalSignature binding.id)
      unless found.arguments.length = binding.slots.length do
        failAt site (.signatureArity binding.id binding.slots.length found.arguments.length)
      pure found
    | _ => return ()
  let summary := summaryFromSignature site signature
  modify fun state => { state with operators := (binding.id, summary) :: state.operators }

private abbrev OperatorTable := List (BindingId × OperatorSummary)

private def replacementLevel (context : Context) (instanceSite : Site) :
    Replacement → CheckM (Site × Analysis)
  | .expression site body => do return (site, ← checkExpr context site body)
  | .binding id => do
    let some binding := context.registry.findBinding id | failAt instanceSite (.missingBinding id)
    return (instanceSite, ← applyBinding context instanceSite binding [] [])

private def checkInstance (context : Context) (base : OperatorTable) (plan : InstancePlan)
    (replay : ModuleId → OperatorTable → CheckM (List Requirement)) :
    CheckM (List Requirement) := do
  let some target := context.registry.moduleAt plan.target | failAt plan.site .missingInstancePlan
  let nonconstant := target.scope.any fun binding =>
    binding.kind = .variable ||
      (base.lookup binding.id).any fun summary => summary.result.floor ≠ .constant
  let mut replacements : OperatorTable := []
  let mut replacementRequirements := []
  for (id, replacement) in plan.substitutions do
    let some targetBinding := context.registry.findBinding id | failAt plan.site (.missingBinding id)
    let (site, actual) ← replacementLevel context plan.site replacement
    let ceiling := if !nonconstant then Level.temporal
      else if targetBinding.kind = .variable then .state else .constant
    unless actual.term.floor.atMost ceiling do
      failAt site (.substitutionLevel id ceiling actual.term.floor)
    let checked ← addCondition actual site (.atMost actual.term ceiling)
    replacementRequirements := replacementRequirements ++ checked.requirements
    replacements := (id, ⟨[], checked.term, []⟩) :: replacements
  -- The replay returns declarations' requirements independently of its summaries.
  -- Restore the host table and annotations after extracting the new members.
  let host ← get
  let nested ←
    try replay plan.target replacements
    catch error => failAt plan.site (.instanceReplay error.site error.kind)
  let declarationRequirements := (replacementRequirements ++ nested).eraseDups
  let replayed := (← get).operators
  let members ← plan.members.mapM fun member => do
    let some home := replayed.lookup member.home | failAt plan.site (.missingSummary member.home)
    let summary : OperatorSummary := {
      home with
      parameters := plan.parameters ++ home.parameters
      requirements := (declarationRequirements ++ home.requirements).eraseDups
    }
    return (member.id, summary)
  set { host with operators := members ++ host.operators }
  -- The declaration itself uses its own formals at their constant baseline.
  -- Carry requirements on enclosing formals back even if no member is used.
  let defaults := plan.parameters.map fun id => (id, LevelTerm.fixed .constant)
  retain plan.site (declarationRequirements.map (·.substitute defaults))

private instance : Inhabited (CheckM (List Requirement)) := ⟨pure []⟩

-- Replay follows dependency edges of the already cycle-checked registry.
private partial def checkModule (registry : CheckedRegistry) (external : ExternalLevels)
    (base replacements : OperatorTable) (replaying : Bool) (id : ModuleId)
    (resolved : CheckedModule) (selectedUnit : Option Nat) : CheckM (List Requirement) := do
  for binding in resolved.bindings do
    if let some summary := replacements.lookup binding.id then
      modify fun state => { state with operators := (binding.id, summary) :: state.operators }
    else
      registerDeclaration external resolved.source.isSome binding
  let some source := resolved.source | return []
  let context : Context := { registry, sourceModule := resolved, replaying }
  let moduleSite : Site := ⟨id, []⟩
  let replay (target : ModuleId) (actual : OperatorTable) : CheckM (List Requirement) := do
    let requirements ← (registry.extendedModules target).mapM fun (dep, mod) =>
      checkModule registry external base actual true dep mod none
    return requirements.flatten
  let mut requirements := []
  for (unit, index) in source.units.zipIdx do
    unless selectedUnit.all (· == index) do continue
    let site := moduleSite.child (.unit index)
    match unit with
    | .definition (.namedInstance ..) | .instantiation .. =>
      let some plan := resolved.instanceAt site.path | failAt site .missingInstancePlan
      requirements := requirements ++ (← checkInstance context base plan replay)
    | .definition definition => discard <| checkDefinition (checkExpr context) site definition
    | .variables _ | .constants _ => pure ()
    | .theoremDecl ⟨none, .expr statement, none⟩ =>
      discard <| checkExpr context (site.child .body) statement
    | _ => failAt site (.unsupported .declaration)
  return requirements

private def validateExternal (registry : CheckedRegistry) (external : ExternalLevels) : CheckM Unit := do
  let mut seen : List BindingId := []
  for (id, _) in external do
    let BindingId.declared site := id
      | failAt ⟨registry.root, []⟩ (.unexpectedExternalSignature id)
    if id ∈ seen then failAt site (.duplicateExternalSignature id)
    let some mod := registry.moduleAt site.moduleId | failAt site (.unexpectedExternalSignature id)
    let some binding := registry.findBinding id | failAt site (.unexpectedExternalSignature id)
    unless mod.source.isNone && binding.kind = .operator do
      failAt site (.unexpectedExternalSignature id)
    seen := id :: seen

private def checkRegistry (registry : CheckedRegistry) (external : ExternalLevels)
    (selectOperator : Bool) :
    Except Diagnostic CheckedLevels := do
  let verify : CheckM Unit := do
    validateExternal registry external
    for (id, mod) in registry.modules do
      unless mod.selectedUnit.isSome == (selectOperator && id == registry.root) do
        failAt ⟨id, []⟩ (.unsupported .declaration)
      discard <| checkModule registry external (← get).operators [] false id mod mod.selectedUnit
  let (_, state) ← verify.run {}
  return ⟨state.expressions.reverse, state.operators.reverse⟩

/-- Check every reachable module and every body in its resolved syntax profile.
Signature-only operator declarations must have a supplied level signature. -/
public def check (registry : CheckedRegistry) (external : ExternalLevels := []) :
    Except Diagnostic CheckedLevels :=
  checkRegistry registry external false

/-- Check the selected root operator and its import closure. Skipped operator
bodies supply no level summaries. A call to one requires a summary and fails. -/
public def checkSelectedOperator (registry : CheckedRegistry) (external : ExternalLevels := []) :
    Except Diagnostic CheckedLevels :=
  checkRegistry registry external true

end Silmaril.Logic.Temporal.TLA.Resolution.Levels
