module

public import Silmaril.Logic.Temporal.TLA.DataElab.Instances.Replay

/-!
# Checked lowering for TLA+ data expressions

Expand a nullary source definition using resolver identities. An expression
actual is an expanded term, and an operator actual retains its lexical context.
See `docs/projects/tla-data-elab.md` for the supported surface and contracts.
-/

namespace Silmaril.Logic.Temporal.TLA.DataElab

open Resolution Instances

universe u

public section

inductive Unsupported where
  | literal | cartesian | caseExpression | tupleBinder | setMapBounds
  | function | functionBounds | functionSet | index | tuple | record | recordSet | field
  | except | actionOrTemporal | proofOrQualifiedReference | labeled | letDeclaration
  deriving DecidableEq, Repr

inductive DiagnosticKind where
  | expectedNullaryDefinition (id : BindingId)
  | missingReference (role : ReferenceRole)
  | missingBinding (id : BindingId)
  | unavailableDefinition (id : BindingId)
  | missingLexicalBinding (id : BindingId)
  | invalidApplication (id : BindingId)
  | invalidBinder (id : BindingId)
  | missingPrimitive (id : BindingId)
  | primitiveArity (id : BindingId) (expected registered : Nat)
  | unsupportedPrimitiveSignature (id : BindingId)
  | unsupportedBuiltin (id : BindingId)
  | unsupported (form : Unsupported)
  | duplicateField (name : String)
  | primeRequiresLevels
  | nestedPrime (inner : Site)
  | primeCrossesOldValue
  | instanceReplay (kind : Replay.DiagnosticKind)
  | expansionLimit
  | invalidExpansion
  deriving DecidableEq, Repr

structure Diagnostic where
  site : Site
  kind : DiagnosticKind
  deriving DecidableEq, Repr

/-- A lowered expression. Its expanded syntax is available to subsequent passes. -/
structure CheckedExpr (signature : ExternalSignature) (fragment : Fragment := .core) where
  private mk ::
  term : Term signature fragment
  wellFormed : term.isWellFormed [] = true

/-- Interpret a checked expression at one valuation. Witness reads use the slots
introduced by enclosing binders. No state transition is inferred here. -/
@[expose] noncomputable def CheckedExpr.eval {V : Type u} {signature : ExternalSignature} {fragment : Fragment}
    (expression : CheckedExpr signature fragment) (ops : Operations V fragment) (B : Booleans V)
    (external : ExternalInterpretation V signature) (valuation : Valuation V) : V :=
  expression.term.eval ops B external valuation (fun _ => (Operations.base ops).enum [])

end

variable {signature : ExternalSignature} {fragment : Fragment}

private abbrev LowerM := StateT Nat (Except Diagnostic)

private def fail {α : Type} (site : Site) (kind : DiagnosticKind) : LowerM α :=
  throw ⟨site, kind⟩

private def freshWitness : LowerM Nat := do
  let slot ← get
  set (slot + 1)
  return slot

private inductive Local (signature : ExternalSignature) (fragment : Fragment) where
  | expression (term : Term signature fragment)
  | closure (home : Site) (body : Surface.Expr) (captured : List (BindingId × Local signature fragment))
  | named (binding : Binding)

private abbrev Context (signature : ExternalSignature) (fragment : Fragment) :=
  List (BindingId × Local signature fragment)

private abbrev Visit (signature : ExternalSignature) (fragment : Fragment) :=
  Context signature fragment → Site → Surface.Expr → LowerM (Term signature fragment)

private abbrev GlobalApply (signature : ExternalSignature) (fragment : Fragment) :=
  Site → Binding → List (Local signature fragment) → LowerM (Term signature fragment)

private inductive Request (signature : ExternalSignature) (fragment : Fragment) where
  | expression (expr : Surface.Expr)
  | invoke (binding : Binding) (args : List (Local signature fragment))

private def expressionBindings (frame : Replay.Frame signature fragment) :
    Context signature fragment :=
  frame.map fun (id, term) => (id, .expression term)

private def declarationId (site : Site) (step : Step) : BindingId := .declared (site.child step)

private def sourceBody (source : Surface.Module) (path : Path) : Option Surface.Expr := do
  let [.unit index] := path | none
  let .definition (.operator _ _ body) ← source.units[index]? | none
  return body

private def useBinding (registry : CheckedRegistry) (site : Site) (role : ReferenceRole)
    (allowPrime : Bool := false) : LowerM Binding := do
  let some reference := (registry.moduleAt site.moduleId).bind (·.referenceAt site.path)
    | fail site (.missingReference role)
  unless reference.role = role do fail site (.missingReference role)
  if !allowPrime && reference.target = .builtin (.symbol .postfix "'") then
    fail site .primeRequiresLevels
  let some binding := registry.findBinding reference.target
    | fail site (.missingBinding reference.target)
  return binding

private def lowerPrime (site : Site) (operand : Term signature fragment) :
    LowerM (Term signature fragment) :=
  match operand.firstPrime with
  | some inner => fail site (.nestedPrime inner)
  | none =>
    if fragment = .collections && !operand.validPrimeOperand then fail site .primeCrossesOldValue
    else pure (.prime site operand)

private def lowerBuiltin (site : Site) (name : Name) (args : List (Term signature fragment)) :
    LowerM (Term signature fragment) :=
  match name, args with
  | .symbol .postfix "'", [operand] => lowerPrime site operand
  | .symbol .prefix "UNCHANGED", [operand] =>
    if fragment = .collections then do
      return .eq false (← lowerPrime site operand) operand
    else fail site (.unsupportedBuiltin (.builtin name))
  | .ident "TRUE", [] => pure (.boolean true)
  | .ident "FALSE", [] => pure (.boolean false)
  | .ident "BOOLEAN", [] => pure .booleanSet
  | .symbol .prefix "\\lnot", [arg] => pure (.not arg)
  | .symbol .infix "=", [l, r] => pure (.eq false l r)
  | .symbol .infix "/=", [l, r] => pure (.eq true l r)
  | .symbol .infix "\\in", [l, r] => pure (.mem false l r)
  | .symbol .infix "\\notin", [l, r] => pure (.mem true l r)
  | .symbol .infix "\\land", [l, r] => pure (.logic .and l r)
  | .symbol .infix "\\lor", [l, r] => pure (.logic .or l r)
  | .symbol .infix "=>", [l, r] => pure (.logic .implies l r)
  | .symbol .infix "\\equiv", [l, r] => pure (.logic .equiv l r)
  | .symbol .prefix "DOMAIN", [operand] =>
    if enabled : fragment = .collections then pure (.graphDomain enabled operand)
    else fail site (.unsupportedBuiltin (.builtin name))
  | _, _ => fail site (.unsupportedBuiltin (.builtin name))

private def expressionArgs (site : Site) (id : BindingId) (args : List (Local signature fragment)) :
    LowerM (List (Term signature fragment)) :=
  args.mapM fun arg =>
    match arg with
    | .expression term => pure term
    | _ => fail site (.invalidApplication id)

private def lowerPrimitive (site : Site) (binding : Binding) (args : List (Local signature fragment)) :
    LowerM (Term signature fragment) := do
  unless binding.slots = List.replicate binding.slots.length .expression do
    fail site (.unsupportedPrimitiveSignature binding.id)
  let terms ← expressionArgs site binding.id args
  if admitted : signature binding.id = some terms.length then
    return .external binding.id terms.length admitted terms
  else
    match signature binding.id with
    | none => fail site (.missingPrimitive binding.id)
    | some arity => fail site (.primitiveArity binding.id terms.length arity)

private def applyClosure (visit : Visit signature fragment) (home : Site) (body : Surface.Expr)
    (captured : Context signature fragment) (args : List (Local signature fragment)) :
    LowerM (Term signature fragment) :=
  let formals := args.zipIdx.map fun (arg, i) => (declarationId home (.parameter i), arg)
  visit (formals ++ captured) (home.child .body) body

private def applyGlobal (registry : CheckedRegistry) (visit : Visit signature fragment)
    (site : Site) (binding : Binding) (args : List (Local signature fragment)) :
    LowerM (Term signature fragment) := do
  match binding.id with
  | .builtin name => lowerBuiltin site name (← expressionArgs site binding.id args)
  | .declared home =>
    match binding.kind with
    | .constant =>
      if args.isEmpty && (signature binding.id).isNone then
        pure (.rigid binding.id)
      else lowerPrimitive site binding args
    | .variable =>
      if args.isEmpty then pure (.flexible binding.id) else fail site (.invalidApplication binding.id)
    | .operator =>
      let some mod := registry.moduleAt home.moduleId
        | fail site (.unavailableDefinition binding.id)
      match mod.source with
      | none => lowerPrimitive site binding args
      | some source =>
        let some body := sourceBody source home.path | fail site (.unavailableDefinition binding.id)
        applyClosure visit home body [] args
    | _ => fail site (.missingLexicalBinding binding.id)

private def applyBinding (visit : Visit signature fragment) (global : GlobalApply signature fragment)
    (frame : Replay.Frame signature fragment) (locals : Context signature fragment) (site : Site)
    (binding : Binding) (args : List (Local signature fragment)) : LowerM (Term signature fragment) :=
  match locals.lookup binding.id with
  | some (.expression term) =>
    if args.isEmpty then pure term else fail site (.invalidApplication binding.id)
  | some (.closure home body captured) => applyClosure visit home body captured args
  | some (.named target) => global site target args
  | none =>
    match frame.lookup binding.id with
    | some term => if args.isEmpty then pure term else fail site (.invalidApplication binding.id)
    | none => global site binding args

private def lowerActual (registry : CheckedRegistry) (visit : Visit signature fragment)
    (locals : Context signature fragment) (site : Site) (slot : Slot) (arg : Surface.OpArg) :
    LowerM (Local signature fragment) := do
  match slot, arg with
  | .expression, .expr body => return .expression (← visit locals site body)
  | .expression, _ => fail site (.missingReference .application)
  | .operator _, .lambda _ body => return .closure site body locals
  | .operator _, _ =>
    let binding ← useBinding registry site .operatorArgument
    match locals.lookup binding.id with
    | some actual => return actual
    | none =>
      if binding.kind = .formal then fail site (.missingLexicalBinding binding.id)
      return .named binding

private def lowerApplication (registry : CheckedRegistry) (visit : Visit signature fragment)
    (global : GlobalApply signature fragment) (frame : Replay.Frame signature fragment)
    (locals : Context signature fragment) (site : Site) (args : List (Site × Surface.OpArg))
    (allowPrime : Bool) : LowerM (Term signature fragment) := do
  let binding ← useBinding registry site .application allowPrime
  unless args.length = binding.slots.length do fail site (.invalidApplication binding.id)
  let actuals ← (binding.slots.zip args).mapM fun (slot, argSite, arg) =>
    lowerActual registry visit locals argSite slot arg
  applyBinding visit global frame locals site binding actuals

private def bindWitness (site : Site) (index : Nat) (locals : Context signature fragment) :
    LowerM (Nat × Context signature fragment) := do
  let slot ← freshWitness
  return (slot, (declarationId site (.binder index), .expression (.witness slot)) :: locals)

private def bindGroup (registry : CheckedRegistry) (site : Site) (names : List Surface.Ident)
    (locals : Context signature fragment) : LowerM (List Nat × Context signature fragment) := do
  let (slots, inner) ← names.zipIdx.foldlM (init := ([], locals)) fun (slots, inner) (_, index) => do
    let binderSite := site.child (.binder index)
    let id := BindingId.declared binderSite
    let some binding := registry.findBinding id | fail binderSite (.missingBinding id)
    unless binding.kind = .rigid && binding.slots.isEmpty do fail binderSite (.invalidBinder id)
    let (slot, inner) ← bindWitness site index inner
    return (slot :: slots, inner)
  return (slots.reverse, inner)

private def lowerBounds (registry : CheckedRegistry) (visit : Visit signature fragment)
    (locals : Context signature fragment) (site : Site) (enabled : fragment = .collections)
    (kind : Bounded) (bounds : List Surface.Bound) (body : Surface.Expr) :
    LowerM (Term signature fragment) := do
  let (groups, inner) ← bounds.zipIdx.foldlM (init := ([], locals)) fun (groups, inner) (group, i) => do
    let groupSite := site.child (.bound i)
    let bound ← visit locals (groupSite.child .domain) group.domain
    let (patterns, inner) ← match group.names with
      | .names names => do
        let (slots, inner) ← bindGroup registry groupSite names inner
        pure (slots.map BinderPattern.name, inner)
      | .tuple names => do
        let (slots, inner) ← bindGroup registry groupSite names inner
        pure ([BinderPattern.tuple slots], inner)
    return ((patterns, bound) :: groups, inner)
  return .bounded enabled kind groups.reverse (← visit inner (site.child .body) body)

private def lowerFunction (registry : CheckedRegistry) (visit : Visit signature fragment)
    (locals : Context signature fragment) (site : Site) (enabled : fragment = .collections)
    (bounds : List Surface.Bound) (body : Surface.Expr) : LowerM (Term signature fragment) := do
  match bounds with
  | [⟨.names [name], domain⟩] =>
    let groupSite := site.child (.bound 0)
    let bound ← visit locals (groupSite.child .domain) domain
    let ([slot], inner) ← bindGroup registry groupSite [name] locals | fail groupSite .invalidExpansion
    return .function enabled site (declarationId groupSite (.binder 0)) slot bound
      (← visit inner (site.child .body) body)
  | _ => lowerBounds registry visit locals site enabled (.map .function) bounds body

private def lowerFields (visit : Visit signature fragment) (locals : Context signature fragment)
    (site : Site) (fields : List Surface.Field) : LowerM (List (String × Term signature fragment)) := do
  let mut seen := []
  for (field, i) in fields.zipIdx do
    if field.name ∈ seen then fail (site.child (.field i)) (.duplicateField field.name)
    seen := field.name :: seen
  fields.zipIdx.mapM fun (field, i) => do
    return (field.name, ← visit locals (site.child (.field i)) field.value)

private def lowerKey (visit : Visit signature fragment) (locals : Context signature fragment)
    (site : Site) (enabled : fragment = .collections) (keySite : Nat → Site)
    (args : List Surface.Expr) : LowerM (Term signature fragment) :=
  match args with
  | [] => fail site .invalidExpansion
  | [arg] => visit locals (keySite 0) arg
  | _ => return .tuple enabled (← args.zipIdx.mapM fun (arg, i) => visit locals (keySite i) arg)

private def lowerExcept (registry : CheckedRegistry) (visit : Visit signature fragment)
    (locals : Context signature fragment) (site : Site) (enabled : fragment = .collections)
    (base : Surface.Expr) (updates : List Surface.Update) : LowerM (Term signature fragment) := do
  let root ← visit locals (site.child (.operand 0)) base
  let clauses ← updates.zipIdx.mapM fun (update, i) => do
    let clause := site.child (.update i)
    let keys ← update.path.zipIdx.mapM fun (component, j) => do
      let position := clause.child (.updateComponent j)
      match component with
      | .field name => pure (.string enabled name)
      | .index args => lowerKey visit locals position enabled (fun k => position.child (.argument k)) args
    let id := BindingId.declared clause
    let some binding := registry.findBinding id | fail clause (.missingBinding id)
    unless binding.kind = .oldValue && binding.slots.isEmpty do fail clause (.invalidBinder id)
    let slot ← freshWitness
    let inner := (id, Local.expression (.oldValue enabled slot)) :: locals
    return (slot, keys, ← visit inner (clause.child .body) update.value)
  return .except enabled root clauses

-- All group domains are in the outer scope, as in resolution.
private def rigidBinderGroups (site : Site) (binders : Surface.RigidBinders) :
    Except Diagnostic (List (Site × List Surface.Ident × Option Surface.Expr)) :=
  match binders with
  | .unbounded names => pure [(site, names, none)]
  | .bounded groups =>
    groups.zipIdx.mapM fun (group, i) =>
      let groupSite := site.child (.bound i)
      match group.names with
      | .tuple _ => throw ⟨groupSite, .unsupported .tupleBinder⟩
      | .names names => pure (groupSite, names, some group.domain)

private def bindRigidGroups {α : Type} (registry : CheckedRegistry)
    (locals : Context signature fragment) (groups : List (Site × List Surface.Ident × α)) :
    LowerM (Context signature fragment × List (Nat × α)) :=
  groups.foldlM (init := (locals, [])) fun (inner, reversed) (groupSite, names, range) => do
    let (slots, inner) ← bindGroup registry groupSite names inner
    return (inner, slots.foldl (fun rev slot => (slot, range) :: rev) reversed)

private def lowerQuant (registry : CheckedRegistry) (visit : Visit signature fragment)
    (locals : Context signature fragment) (site : Site) (kind : Surface.Quantifier)
    (binders : Surface.RigidBinders) (body : Surface.Expr) : LowerM (Term signature fragment) := do
  let groups ← liftM (rigidBinderGroups site binders)
  let domains ← groups.mapM fun (groupSite, names, domain) => do
    return (groupSite, names, ← domain.mapM (visit locals (groupSite.child .domain)))
  let (inner, reversed) ← bindRigidGroups registry locals domains
  let result ← visit inner (site.child .body) body
  return reversed.foldl (fun term (slot, domain) => .quant kind slot domain term) result

private def lower (registry : CheckedRegistry) (fragment : Fragment)
    (allowPrime allowInstances : Bool) (fuel : Nat) (frame : Replay.Frame signature fragment)
    (locals : Context signature fragment) (site : Site) (request : Request signature fragment) :
    LowerM (Term signature fragment) := do
  match fuel with
  | 0 => fail site .expansionLimit
  | remaining + 1 =>
    let descend := lower registry fragment allowPrime allowInstances remaining
    let visit : Visit signature fragment := fun context origin expr =>
      descend frame context origin (.expression expr)
    let global : GlobalApply signature fragment := fun origin binding args => do
      if allowInstances then
        if let some (plan, member) := registry.instanceMemberAt binding.id then
          let actuals ← expressionArgs origin binding.id args
          let step ← Replay.prepare registry origin plan member actuals
            (fun problem => fail problem.site (.instanceReplay problem.kind))
            (fun formals rhs expr => visit (expressionBindings formals) rhs expr)
            (fun formals rhs target =>
              descend frame (expressionBindings formals) rhs (.invoke target []))
          return ← descend step.frame [] origin (.invoke step.home (step.arguments.map .expression))
      applyGlobal registry visit origin binding args
    if let .invoke binding args := request then
      return ← applyBinding visit global frame locals site binding args
    let .expression expr := request | fail site .invalidExpansion
    let operands := fun (items : List Surface.Expr) =>
      items.zipIdx.mapM fun (item, i) => visit locals (site.child (.operand i)) item
    let apply :=
      fun args => lowerApplication registry visit global frame locals site args allowPrime
    let arguments := fun (args : List Surface.OpArg) (child : Nat → Step) =>
      args.zipIdx.map fun (arg, i) => (site.child (child i), arg)
    let symbolic := fun args => apply (arguments (args.map Surface.OpArg.expr) .operand)
    let unsupported := fun form => fail site (.unsupported form)
    match expr with
    | .ref (.operator _) args [] => apply (arguments args .argument)
    | .ref (.operator head) args selectors =>
      unless allowInstances do fail site (.unsupported .proofOrQualifiedReference)
      let some (_, parts) := qualifiedCall site head args selectors
        | unsupported .proofOrQualifiedReference
      apply (qualifiedArguments parts)
    | .ref .. => unsupported .proofOrQualifiedReference
    | .prefix _ arg | .postfix _ arg => symbolic [arg]
    | .infix _ left right => symbolic [left, right]
    | .ifThenElse condition yes no =>
      return .ite (← visit locals (site.child (.operand 0)) condition)
        (← visit locals (site.child (.operand 1)) yes) (← visit locals (site.child (.operand 2)) no)
    | .junction kind items => return .junction kind (← operands items)
    | .letIn declarations body =>
      let inner ← declarations.zipIdx.foldlM (init := locals) fun context (decl, i) => do
        let home := site.child (.letDecl i)
        match decl with
        | .definition (.operator _ _ body) =>
          return (.declared home, .closure home body context) :: context
        | _ => fail home (.unsupported .letDeclaration)
      visit inner (site.child .body) body
    | .rigidQuant kind binders body =>
      if enabled : fragment = .collections then
        if let .bounded bounds := binders then
          lowerBounds registry visit locals site enabled (.quant kind) bounds body
        else lowerQuant registry visit locals site kind binders body
      else lowerQuant registry visit locals site kind binders body
    | .choose (.ident _) domain body =>
      let bound ← domain.mapM (visit locals (site.child .domain))
      let (slot, inner) ← bindWitness site 0 locals
      return .choose slot bound (← visit inner (site.child .body) body)
    | .setFilter (.ident _) domain body =>
      let bound ← visit locals (site.child .domain) domain
      let (slot, inner) ← bindWitness site 0 locals
      return .filter slot bound (← visit inner (site.child .body) body)
    | .choose (.tuple names) domain body =>
      if enabled : fragment = .collections then
        let bound ← domain.mapM (visit locals (site.child .domain))
        let (slots, inner) ← bindGroup registry site names locals
        return .chooseTuple enabled slots bound (← visit inner (site.child .body) body)
      else unsupported .tupleBinder
    | .setFilter (.tuple names) domain body =>
      if enabled : fragment = .collections then
        let bound ← visit locals (site.child .domain) domain
        let (slots, inner) ← bindGroup registry site names locals
        return .bounded enabled .filter [([.tuple slots], bound)] (← visit inner (site.child .body) body)
      else unsupported .tupleBinder
    | .setMap body [⟨.names [_], domain⟩] =>
      let groupSite := site.child (.bound 0)
      let bound ← visit locals (groupSite.child .domain) domain
      let (slot, inner) ← bindWitness groupSite 0 locals
      return .image slot bound (← visit inner (site.child .body) body)
    | .setMap body bounds =>
      if enabled : fragment = .collections then
        lowerBounds registry visit locals site enabled (.map .image) bounds body
      else
        match bounds with
        | [⟨.tuple _, _⟩] => unsupported .tupleBinder
        | _ => unsupported .setMapBounds
    | .setEnum items => return .enum (← operands items)
    | .literal (.natural value) => pure (.numeral value)
    | .literal (.string value) =>
      if enabled : fragment = .collections then pure (.string enabled value)
      else unsupported .literal
    | .literal _ => unsupported .literal
    | .cartesian _ => unsupported .cartesian
    | .cases .. => unsupported .caseExpression
    | .function bounds body =>
      if enabled : fragment = .collections then
        lowerFunction registry visit locals site enabled bounds body
      else unsupported .function
    | .functionSet domain range =>
      if enabled : fragment = .collections then
        return .functionSet enabled site (← visit locals (site.child (.operand 0)) domain)
          (← visit locals (site.child (.operand 1)) range)
      else unsupported .functionSet
    | .index fn args =>
      if enabled : fragment = .collections then
        let root ← visit locals (site.child (.operand 0)) fn
        return .index enabled root
          (← lowerKey visit locals site enabled (fun i => site.child (.operand (i + 1))) args)
      else unsupported .index
    | .tuple items =>
      if enabled : fragment = .collections then return .tuple enabled (← operands items)
      else unsupported .tuple
    | .record fields =>
      if enabled : fragment = .collections then
        return .record enabled site (← lowerFields visit locals site fields)
      else unsupported .record
    | .recordSet fields =>
      if enabled : fragment = .collections then
        return .recordSet enabled site (← lowerFields visit locals site fields)
      else unsupported .recordSet
    | .field root name =>
      if enabled : fragment = .collections then
        return .index enabled (← visit locals (site.child (.operand 0)) root) (.string enabled name)
      else unsupported .field
    | .except root updates =>
      if enabled : fragment = .collections then lowerExcept registry visit locals site enabled root updates
      else unsupported .except
    | .oldValue =>
      if fragment = .collections then apply [] else unsupported .except
    | .action .. | .fairness .. | .temporalQuant .. => unsupported .actionOrTemporal
    | .labeled .. => unsupported .labeled
termination_by structural fuel

private def definitionBody (registry : CheckedRegistry) (id : BindingId) :
    Except Diagnostic (Site × Surface.Expr) := do
  let .declared home := id
    | throw ⟨⟨registry.root, []⟩, .expectedNullaryDefinition id⟩
  let body : Option Surface.Expr := do
    let binding ← registry.findBinding id
    if binding.kind = .operator ∧ binding.slots = [] then
      let mod ← registry.moduleAt home.moduleId
      let source ← mod.source
      sourceBody source home.path
    else none
  let some body := body | throw ⟨home, .expectedNullaryDefinition id⟩
  return (home, body)

private def lowerBody (registry : CheckedRegistry) (signature : ExternalSignature)
    (fragment : Fragment) (allowPrime : Bool) (maxDepth : Nat) (home : Site) (body : Surface.Expr)
    (allowInstances : Bool := false) : Except Diagnostic (CheckedExpr signature fragment) := do
  let (term, _) ← (lower registry fragment allowPrime allowInstances maxDepth [] [] (home.child .body)
    (.expression body)).run 0
  if valid : term.isWellFormed [] = true then
    return ⟨term, valid⟩
  else
    throw ⟨home.child .body, .invalidExpansion⟩

/-- Expand a nullary source definition without a level check. Prime is
rejected. The depth bound counts visits through source expressions and expanded
bodies. Exhaustion reports the next unvisited site. -/
public def lowerDefinition (registry : CheckedRegistry) (signature : ExternalSignature)
    (maxDepth : Nat) (id : BindingId) : Except Diagnostic (CheckedExpr signature) := do
  let (home, body) ← definitionBody registry id
  lowerBody registry signature .core false maxDepth home body

end Silmaril.Logic.Temporal.TLA.DataElab
