module

public import Silmaril.Logic.Temporal.TLA.DataElab.Defs
public import Silmaril.Logic.Temporal.TLA.Resolution.Levels.Defs
public import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs

/-! Scoped, constant-level TLA+ proof obligations over the data denotation. -/

namespace Silmaril.Logic.Temporal.TLA.ProofFrontEnd

open Resolution DataElab

universe u

public section

abbrev noPrimitives : DataElab.ExternalSignature := fun _ => none

abbrev Proposition := CheckedExpr noPrimitives

structure Interpretation (V : Type u) where
  operations : DataOperations V
  booleans : Booleans V

/-- Truth in a single interpretation of the landed data semantics. -/
@[expose] noncomputable def Proposition.holds {V : Type u} (proposition : Proposition)
    (model : Interpretation V) (valuation : Valuation V) : Prop :=
  proposition.eval model.operations model.booleans (fun _ _ admitted => nomatch admitted)
    valuation = model.booleans.trueValue

structure Assumption where
  unit : Nat
  name : Option Surface.Ident
  proposition : Proposition

structure LocalHypothesis where
  label : Option Surface.Ident
  proposition : Proposition

/-- A hypothesis label is relative to the theorem whose proof cites it. -/
inductive FactRef where
  | assumption (unit : Nat)
  | hypothesis (label : Surface.Ident)
  | theoremDecl (unit : Nat)
  deriving DecidableEq, Repr

/-- The status of the source proof text after scope checking. -/
inductive Unresolved where
  | missing
  | omitted
  | obvious
  | byFacts (only : Bool) (facts : List FactRef)
  deriving DecidableEq, Repr

structure TheoremStatement where
  private mk ::
  unit : Nat
  name : Option Surface.Ident
  hypotheses : List LocalHypothesis
  goal : Proposition
  sourceProof : Unresolved

structure Obligation extends TheoremStatement where
  private mk ::
  private moduleAssumptions : List Assumption

structure Context where
  private mk ::
  assumptions : List Assumption
  private statements : List TheoremStatement

private def Context.obligation (context : Context) (statement : TheoremStatement) : Obligation :=
  ⟨statement, context.assumptions⟩

def Context.theorems (context : Context) : List Obligation :=
  context.statements.map context.obligation

/-- The module assumptions preceding this theorem in source order. -/
def Obligation.assumptions (obligation : Obligation) : List Assumption :=
  obligation.moduleAssumptions.filter (fun fact => fact.unit < obligation.unit)

/-- A premise-checking goal with the same module and local context. -/
def Obligation.withGoal (obligation : Obligation) (goal : Proposition) : Obligation :=
  ⟨{ obligation.toTheoremStatement with goal }, obligation.moduleAssumptions⟩

/-- A theorem judgment under its preceding module assumptions and local hypotheses,
for every valuation in the chosen data interpretation. -/
@[expose] def Obligation.Valid {V : Type u} (obligation : Obligation)
    (model : Interpretation V) : Prop :=
  ∀ valuation : Valuation V,
    (∀ fact ∈ obligation.assumptions, fact.proposition.holds model valuation) →
    (∀ hypothesis ∈ obligation.hypotheses, hypothesis.proposition.holds model valuation) →
    obligation.goal.holds model valuation

theorem Obligation.holds_of_valid_withGoal {V : Type u} {obligation : Obligation}
    {goal : Proposition} {model : Interpretation V} {valuation : Valuation V}
    (valid : (obligation.withGoal goal).Valid model)
    (assumptions : ∀ fact ∈ obligation.assumptions, fact.proposition.holds model valuation)
    (hypotheses : ∀ hyp ∈ obligation.hypotheses, hyp.proposition.holds model valuation) :
    goal.holds model valuation :=
  valid valuation assumptions hypotheses

/-- Evidence provided by a Lean caller for the denoted judgment. -/
structure SuppliedEvidence {V : Type u} (obligation : Obligation)
    (model : Interpretation V) : Prop where
  valid : obligation.Valid model

/-- Exact reuse of in-scope facts and independently certified theorems. -/
inductive ExactCertificate : Obligation → Type where
  | assumption {obligation : Obligation} (premise : Assumption)
      (inScope : premise ∈ obligation.assumptions)
      (termEq : premise.proposition.term = obligation.goal.term) : ExactCertificate obligation
  | hypothesis {obligation : Obligation} (premise : LocalHypothesis)
      (inScope : premise ∈ obligation.hypotheses)
      (termEq : premise.proposition.term = obligation.goal.term) : ExactCertificate obligation
  | theoremDecl {obligation : Obligation} (earlier : Obligation)
      (certificate : ExactCertificate earlier) (before : earlier.unit < obligation.unit)
      (inScope : earlier.assumptions ⊆ obligation.assumptions) (closed : earlier.hypotheses = [])
      (termEq : earlier.goal.term = obligation.goal.term) : ExactCertificate obligation
  | applyRule {obligation : Obligation} (earlier : Obligation)
      (certificate : ExactCertificate earlier) (before : earlier.unit < obligation.unit)
      (inScope : earlier.assumptions ⊆ obligation.assumptions)
      (premises : (hypothesis : LocalHypothesis) → hypothesis ∈ earlier.hypotheses →
        ExactCertificate (obligation.withGoal hypothesis.proposition))
      (termEq : earlier.goal.term = obligation.goal.term) : ExactCertificate obligation

inductive Diagnostic where
  | parse (error : Surface.Parser.Diagnostic)
  | imports
  | unsupportedUnit (unit : Nat)
  | unsupportedStatement (unit : Nat)
  | unsupportedProof (unit : Nat)
  | unsupportedCitation (unit : Nat)
  | nameConflict (unit : Nat) (name : Surface.Ident)
  | duplicateHypothesisLabel (unit : Nat) (label : Surface.Ident)
  | factNotInScope (unit : Nat) (name : Surface.Ident)
  | hypothesisNotInScope (unit : Nat) (owner label : Surface.Ident)
  | resolution (error : Resolution.Diagnostic)
  | levels (error : Levels.Diagnostic)
  | missingLevel (site : Site)
  | expectedConstant (site : Site) (actual : Levels.Level)
  | lowering (error : DataElab.Diagnostic)
  deriving Repr

end

open Surface

private inductive StatementKind where
  | assumption
  | theoremDecl (proof : Option Proof)

private structure StatementPlan where
  unit : Nat
  kind : StatementKind
  name : Option Ident
  goal : Nat
  hypotheses : List (Nat × Option Ident)

/-- A generated identifier containing a colon cannot be named by the parser. -/
private def expressionUnit (index : Nat) (name : Option Ident) (body : Expr) : ModuleUnit :=
  .definition (.operator .ordinary (.ident (name.getD s!"proof:{index}") []) body)

/-- Project source expressions to nullary definitions for the existing resolver and
lowerer. Local hypotheses get fresh private-to-the-projection names. -/
private def project (source : Surface.Module) :
    Except Diagnostic (Surface.Module × List StatementPlan) := do
  unless source.extendsModules.isEmpty do throw .imports
  let mut projected := #[]
  let mut plans := []
  let mut names : List Ident := []
  for (unit, index) in source.units.zipIdx do
    let (kind, name, hypotheses, goal) ← match unit with
      | .assumption name body => pure (.assumption, name, [], body)
      | .theoremDecl ⟨name, statement, proof⟩ =>
        match statement with
        | .expr goal => pure (.theoremDecl proof, name, [], goal)
        | .assumeProve .plain hypotheses .plain goal =>
          let hypotheses ← hypotheses.mapM fun
            | .statement (.expr (.labeled ⟨label, []⟩ expression)) =>
              if name.isSome then pure (some label, expression) else throw (.unsupportedStatement index)
            | .statement (.expr (.labeled ..)) => throw (.unsupportedStatement index)
            | .statement (.expr expression) => pure (none, expression)
            | _ => throw (.unsupportedStatement index)
          pure (.theoremDecl proof, name, hypotheses, goal)
        | _ => throw (.unsupportedStatement index)
      | .constants _ | .variables _ | .definition (.operator ..) =>
        projected := projected.push unit
        continue
      | _ => throw (.unsupportedUnit index)
    if let some name := name then
      if names.contains name then throw (.nameConflict index name)
      names := name :: names
    let mut locals := []
    let mut labels := []
    for (label, hypothesis) in hypotheses do
      if let some label := label then
        if labels.contains label then throw (.duplicateHypothesisLabel index label)
        labels := label :: labels
      locals := (projected.size, label) :: locals
      projected := projected.push (expressionUnit projected.size none hypothesis)
    let goalIndex := projected.size
    -- An ASSUME/PROVE name denotes a rule and cannot be used as an expression.
    projected := projected.push (expressionUnit goalIndex
      (if hypotheses.isEmpty then name else none) goal)
    plans := ⟨index, kind, name, goalIndex, locals.reverse⟩ :: plans
  return ({ source with units := projected.toList }, plans.reverse)

private def resolveProof (unit : Nat) (name : Option Ident) (hypotheses : List LocalHypothesis)
    (known : List (Ident × FactRef)) :
    Option Proof → Except Diagnostic Unresolved
  | none => pure .missing
  | some .omitted => pure .omitted
  | some .obvious => pure .obvious
  | some (.steps ..) => throw (.unsupportedProof unit)
  | some (.byFacts only citations) => do
    unless citations.defs.isEmpty && !citations.facts.isEmpty do
      throw (.unsupportedCitation unit)
    let facts ← citations.facts.mapM fun
      | .expr (.ref (.operator (.ident cited)) [] []) =>
        match known.lookup cited with
        | some fact => pure fact
        | none => throw (.factNotInScope unit cited)
      | .expr (.ref (.operator (.ident owner)) [] [.named (.ident label) []]) =>
        if name == some owner && hypotheses.any (·.label == some label) then
          pure (.hypothesis label)
        else throw (.hypothesisNotInScope unit owner label)
      | _ => throw (.unsupportedCitation unit)
    return .byFacts only facts

private def lower (registry : CheckedRegistry) (levels : Levels.CheckedLevels)
    (maxDepth index : Nat) : Except Diagnostic Proposition := do
  let site : Site := ⟨registry.root, [.unit index]⟩
  let id := BindingId.declared site
  let some level := levels.operatorAt id | throw (.missingLevel site)
  unless level.result.floor = .constant do throw (.expectedConstant site level.result.floor)
  (DataElab.lowerDefinition registry noPrimitives maxDepth id).mapError .lowering

/-- Prepare obligations for a single parsed source module. Source proof text
is scoped here and can be passed to the separate exact checker. -/
public def prepare (source : String) (maxDepth : Nat := 64) : Except Diagnostic Context := do
  let parsed ← (Surface.Parser.parseModule source).mapError .parse
  let (projected, plans) ← project parsed
  let registry ← (Resolution.resolveWith .levelSyntax
    [(parsed.name, .parsed projected [])] parsed.name).mapError .resolution
  let levels ← (Levels.check registry).mapError .levels
  let mut known := []
  let mut assumptions := []
  let mut theorems := []
  for plan in plans do
    if let some name := plan.name then
      if !plan.hypotheses.isEmpty &&
          ((registry.moduleAt parsed.name).bind (·.bindingAt (.ident name))).isSome then
        throw (.nameConflict plan.unit name)
    let goal ← lower registry levels maxDepth plan.goal
    let fact ← match plan.kind with
      | .assumption =>
        assumptions := ⟨plan.unit, plan.name, goal⟩ :: assumptions
        pure (.assumption plan.unit)
      | .theoremDecl proof =>
        let hypotheses ← plan.hypotheses.mapM fun (index, label) => do
          return ⟨label, ← lower registry levels maxDepth index⟩
        let proof ← resolveProof plan.unit plan.name hypotheses known proof
        theorems := ⟨plan.unit, plan.name, hypotheses, goal, proof⟩ :: theorems
        pure (.theoremDecl plan.unit)
    if let some name := plan.name then
      known := (name, fact) :: known
  return ⟨assumptions.reverse, theorems.reverse⟩

/-- Compare a small fragment of expanded expressions. Every successful match
contains an equality of the actual evaluated terms. -/
private def matchTerm (left right : Term noPrimitives) : Option (PLift (left = right)) :=
  match left, right with
  | .rigid x, .rigid y => if h : x = y then some ⟨congrArg Term.rigid h⟩ else none
  | .numeral x, .numeral y => if h : x = y then some ⟨congrArg Term.numeral h⟩ else none
  | .boolean x, .boolean y => if h : x = y then some ⟨congrArg Term.boolean h⟩ else none
  | .eq n l r, .eq m l' r' => do
    if hn : n = m then
      let ⟨hl⟩ ← matchTerm l l'
      let ⟨hr⟩ ← matchTerm r r'
      return ⟨by
        cases hn
        cases hl
        cases hr
        rfl⟩
    else none
  | _, _ => none

private def Obligation.checkFact (obligation : Obligation) :
    FactRef → Option (ExactCertificate obligation)
  | .assumption unit => do
    let ⟨premise, inScope⟩ ← obligation.assumptions.attach.find? (·.val.unit == unit)
    let ⟨termEq⟩ ← matchTerm premise.proposition.term obligation.goal.term
    return .assumption premise inScope termEq
  | .hypothesis label => do
    let ⟨premise, inScope⟩ ← obligation.hypotheses.attach.find? (·.val.label == some label)
    let ⟨termEq⟩ ← matchTerm premise.proposition.term obligation.goal.term
    return .hypothesis premise inScope termEq
  | .theoremDecl _ => none

/-- Check a leaf with exactly one module or local assumption citation. -/
public def Obligation.checkExact (obligation : Obligation) : Option (ExactCertificate obligation) :=
  match obligation.sourceProof with
  | .byFacts _ [fact] => obligation.checkFact fact
  | _ => none

private theorem Context.assumptions_mono (context : Context) {earlier current : TheoremStatement}
    (before : earlier.unit < current.unit) :
    (context.obligation earlier).assumptions ⊆ (context.obligation current).assumptions := by
  intro _ member
  rcases List.mem_filter.mp member with ⟨inModule, earlierScope⟩
  exact List.mem_filter.mpr ⟨inModule,
    decide_eq_true (Nat.lt_trans (of_decide_eq_true earlierScope) before)⟩

private abbrev CertifiedTheorem (context : Context) :=
  (statement : TheoremStatement) × ExactCertificate (context.obligation statement)

private abbrev CheckedTheorem (context : Context) :=
  (statement : TheoremStatement) × Option (ExactCertificate (context.obligation statement))

private def findCertified {context : Context} (checked : List (CheckedTheorem context)) (unit : Nat) :
    Option (CertifiedTheorem context) := do
  let ⟨earlier, some proof⟩ ← checked.find? (·.1.unit == unit) | none
  return ⟨earlier, proof⟩

private def Context.checkTheorem (context : Context) (statement : TheoremStatement)
    (citation : CertifiedTheorem context) :
    Option (ExactCertificate (context.obligation statement)) := do
  let ⟨earlier, certificate⟩ := citation
  if hBefore : earlier.unit < statement.unit then
    if closed : earlier.hypotheses.isEmpty then
      let ⟨termEq⟩ ← matchTerm earlier.goal.term statement.goal.term
      return .theoremDecl (context.obligation earlier) certificate hBefore
        (context.assumptions_mono hBefore) (List.isEmpty_iff.mp closed) termEq
    else none
  else none

private def Context.checkRule (context : Context) (statement : TheoremStatement)
    (checked : List (CheckedTheorem context)) (facts : List FactRef) :
    Option (ExactCertificate (context.obligation statement)) := do
  let units := facts.filterMap fun
    | .theoremDecl unit => some unit
    | _ => none
  let cited ← units.mapM (findCertified checked)
  let (formulas, rules) := cited.partition (·.1.hypotheses.isEmpty)
  let [⟨earlier, certificate⟩] := rules | none
  if before : earlier.unit < statement.unit then
    let ⟨termEq⟩ ← matchTerm earlier.goal.term statement.goal.term
    let checkPremise (hypothesis : LocalHypothesis) :
        Option (ExactCertificate ((context.obligation statement).withGoal hypothesis.proposition)) := by
      let target := { statement with goal := hypothesis.proposition }
      change Option (ExactCertificate (context.obligation target))
      exact (facts.findSome? (context.obligation target).checkFact).orElse fun _ =>
        formulas.findSome? (context.checkTheorem target)
    if covered : earlier.hypotheses.all (fun hypothesis => (checkPremise hypothesis).isSome) then
      return .applyRule (context.obligation earlier) certificate before
        (context.assumptions_mono before)
        (fun hypothesis member =>
          (checkPremise hypothesis).get (List.all_eq_true.mp covered hypothesis member))
        termEq
    else none
  else none

/-- Check each obligation in source order. A multi-fact leaf can apply one
certified rule using explicitly cited facts for all its local premises. -/
public def Context.checkExact (context : Context) :
    List ((obligation : Obligation) × Option (ExactCertificate obligation)) := Id.run do
  let mut checked : List (CheckedTheorem context) := []
  for statement in context.statements do
    let obligation := context.obligation statement
    let certificate := match statement.sourceProof with
      | .byFacts _ [.theoremDecl unit] => do
        context.checkTheorem statement (← findCertified checked unit)
      | .byFacts _ facts@(_ :: _ :: _) => context.checkRule statement checked facts
      | _ => obligation.checkExact
    checked := ⟨statement, certificate⟩ :: checked
  return checked.reverse.map fun ⟨statement, certificate⟩ =>
    ⟨context.obligation statement, certificate⟩

end Silmaril.Logic.Temporal.TLA.ProofFrontEnd
