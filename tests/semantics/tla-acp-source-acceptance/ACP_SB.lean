module

import Silmaril.Logic.Temporal.TLA.DataBridge.Thms
public import Silmaril.Logic.Temporal.TLA.DataElab.Collections.Tagged
import all Silmaril.Logic.Temporal.TLA.DataElab.Defs
import all Silmaril.Logic.Temporal.TLA.DataElab.Collections.Defs
import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.RecordSet.Thms
import Silmaril.Logic.Temporal.TLA.Data.Tagged.Except.Thms
meta import Silmaril.Logic.Temporal.TLA.DataElab.Collections.Defs
meta import Silmaril.Logic.Temporal.TLA.Resolution.Instances.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
public import Lean
public meta import Lean

/-! State and transition semantics of the intact pinned ACP_SB module. -/

namespace Silmaril.Logic.Temporal.TLA.SourceAcceptance.ACP_SB

open Resolution DataElab Data.Tagged

private meta abbrev root : ModuleId := "pinned/acp-sb"
private meta abbrev declaration (unit : Nat) : BindingId := .declared ⟨root, [.unit unit]⟩
private meta abbrev member (unit index : Nat) : BindingId :=
  .declared ⟨root, [.unit unit, .member index]⟩
private meta def noPrimitives : ExternalSignature := fun _ => none

meta section

open Lean Elab.Term

private def checkedSource : TermElabM Instances.CheckedInstances := do
  let some path ← IO.getEnv "SILMARIL_ACP_SB_SOURCE"
    | throwError "stage ACP_SB with tla-acp-source-acceptance/check.py"
  let source ← match Surface.Parser.parseModule (← IO.FS.readFile path) with
    | .ok source => pure source
    | .error error => throwError "ACP_SB parse: {reprStr error}"
  unless source.name = "ACP_SB" ∧ source.units.length = 40 ∧ source.extendsModules = [] do
    throwError "expected the complete ACP_SB module with no imports"
  let checked ← match Instances.check [(root, .parsed source [])] root with
    | .ok checked => pure checked
    | .error error => throwError "ACP_SB resolution or levels: {reprStr error}"
  let some retained := (checked.registry.moduleAt root).bind (·.source)
    | throwError "missing original ACP_SB source"
  unless reprStr retained = reprStr source do throwError "ACP_SB source changed during checking"
  return checked

private def select (checked : Instances.CheckedInstances) (name : String) (unit : Nat) :
    TermElabM (CheckedExpr noPrimitives .collections) := do
  let id := declaration unit
  let binding := (checked.registry.moduleAt root).bind (·.bindingAt (.ident name))
  let some summary := checked.levels.operatorAt id | throwError "missing level for {name}"
  unless binding.map (·.id) = some id ∧ summary.result = Levels.LevelTerm.fixed .state ∧
      summary.parameters.isEmpty do
    throwError "unexpected declaration identity or level for {name}"
  match Collections.lowerState checked.registry [] noPrimitives 32 id with
  | .ok selected => return selected
  | .error error => throwError "ACP_SB {name} lowering: {reprStr error}"

deriving instance ToExpr for Resolution.Fixity
deriving instance ToExpr for Resolution.Name
deriving instance ToExpr for Step
deriving instance ToExpr for Site
deriving instance ToExpr for BindingId
deriving instance ToExpr for Logic
deriving instance ToExpr for Surface.Junction
deriving instance ToExpr for Surface.Quantifier
deriving instance ToExpr for BinderPattern
deriving instance ToExpr for BinderMap
deriving instance ToExpr for Bounded

private partial def quoteTerm (term : Term noPrimitives .collections) : TermElabM Lean.Expr := do
  let ctor := fun name => mkApp2 (mkConst name) (mkConst ``noPrimitives)
    (mkConst ``Fragment.collections)
  let type := ctor ``DataElab.Term
  let node := fun name args => mkAppN (ctor name) args
  let enabled ← Meta.mkEqRefl (mkConst ``Fragment.collections)
  let terms := fun values => do Meta.mkListLit type (← values.mapM quoteTerm)
  match term with
  | .rigid id => return node ``Term.rigid #[toExpr id]
  | .flexible id => return node ``Term.flexible #[toExpr id]
  | .witness slot => return node ``Term.witness #[toExpr slot]
  | .oldValue _ slot => return node ``Term.oldValue #[enabled, toExpr slot]
  | .prime site arg => return node ``Term.prime #[toExpr site, ← quoteTerm arg]
  | .boolean b => return node ``Term.boolean #[toExpr b]
  | .booleanSet => return node ``Term.booleanSet #[]
  | .not arg => return node ``Term.not #[← quoteTerm arg]
  | .eq negated left right =>
    return node ``Term.eq #[toExpr negated, ← quoteTerm left, ← quoteTerm right]
  | .logic op left right =>
    return node ``Term.logic #[toExpr op, ← quoteTerm left, ← quoteTerm right]
  | .junction kind items => return node ``Term.junction #[toExpr kind, ← terms items]
  | .mem negated element set =>
    return node ``Term.mem #[toExpr negated, ← quoteTerm element, ← quoteTerm set]
  | .enum values => return node ``Term.enum #[← terms values]
  | .bounded _ kind groups body =>
    let patternsType := mkApp (mkConst ``List [0]) (mkConst ``BinderPattern)
    let groupType := mkApp2 (mkConst ``Prod [0, 0]) patternsType type
    let domains ← groups.mapM fun (patterns, domain) => do
      Meta.mkAppM ``Prod.mk #[toExpr patterns, ← quoteTerm domain]
    return node ``Term.bounded #[enabled, toExpr kind, ← Meta.mkListLit groupType domains, ← quoteTerm body]
  | .functionSet _ site domain range =>
    return node ``Term.functionSet #[enabled, toExpr site, ← quoteTerm domain, ← quoteTerm range]
  | .recordSet _ site fields =>
    let pair := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) type
    let entries ← fields.mapM fun (name, value) =>
      return mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) type (toExpr name) (← quoteTerm value)
    return node ``Term.recordSet #[enabled, toExpr site, ← Meta.mkListLit pair entries]
  | .index _ root key => return node ``Term.index #[enabled, ← quoteTerm root, ← quoteTerm key]
  | .tuple _ items => return node ``Term.tuple #[enabled, ← terms items]
  | .string _ value => return node ``Term.string #[enabled, toExpr value]
  | .except _ root clauses =>
    let rhsType := mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``List [0]) type) type
    let clauseType := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) rhsType
    let entries ← clauses.mapM fun (slot, keys, body) => do
      let rhs ← Meta.mkAppM ``Prod.mk #[← terms keys, ← quoteTerm body]
      Meta.mkAppM ``Prod.mk #[toExpr slot, rhs]
    return node ``Term.except #[enabled, ← quoteTerm root, ← Meta.mkListLit clauseType entries]
  | other => throwError "unexpected expanded ACP_SB term: {reprStr other}"

private def quoteChecked (expression : CheckedExpr noPrimitives .collections) :
    TermElabM Lean.Expr := do
  return mkApp4 (mkConst ``CheckedExpr.mk) (mkConst ``noPrimitives) (mkConst ``Fragment.collections)
    (← quoteTerm expression.term) (← Meta.mkEqRefl (toExpr true))

/-- Follow the resolved disjunctions and participant quantifiers in the original
transition definition. Each remaining operator call is a leaf action. -/
private partial def actionLeaves (mod : CheckedModule) (source : Surface.Module)
    (site : Site) (parameter : Option BindingId) (expr : Surface.Expr) :
    TermElabM (List (String × Nat × Bool)) := do
  let targetAt := fun (atSite : Site) => (mod.referenceAt atSite.path).map (·.target)
  match expr with
  | .infix _ left right =>
    unless targetAt site = some (.builtin (.symbol .infix "\\lor")) do
      throwError "expected disjunction at {reprStr site}"
    return (← actionLeaves mod source (site.child (.operand 0)) parameter left) ++
      (← actionLeaves mod source (site.child (.operand 1)) parameter right)
  | .rigidQuant .exists (.bounded [⟨.names [_], .ref (.operator _) [] []⟩]) body =>
    let bound := site.child (.bound 0)
    unless parameter.isNone && targetAt (bound.child .domain) = some (member 0 0) do
      throwError "expected one existential over participants at {reprStr bound}"
    actionLeaves mod source (site.child .body) (some (.declared (bound.child (.binder 0)))) body
  | .ref (.operator (.ident name)) args [] =>
    let some (.declared home) := targetAt site
      | throwError "expected resolved action reference at {reprStr site}"
    let [.unit unit] := home.path | throwError "expected a module action declaration"
    match parameter, args with
    | none, [] => pure ()
    | some id, [.expr (.ref (.operator _) [] [])] =>
      unless targetAt (site.child (.argument 0)) = some id do
        throwError "unexpected participant binding for {name}"
    | _, _ => throwError "unexpected participant arguments for {name}"
    if name ∈ ["parProg", "parProgN", "coordProgA", "coordProgB", "coordProgN"] then
      let some body := sourceBody source home.path | throwError "missing action body for {name}"
      actionLeaves mod source (home.child .body) (parameter.map fun _ =>
        .declared (home.child (.parameter 0))) body
    else
      return [(name, unit, parameter.isSome)]
  | _ => throwError "unexpected ACP_SB transition expression at {reprStr site}"

private def emitNext (checked : Instances.CheckedInstances) : TermElabM Lean.Expr := do
  let some mod := checked.registry.moduleAt root | throwError "missing ACP_SB module"
  let some source := mod.source | throwError "missing original ACP_SB source"
  let id := declaration 24
  let some binding := mod.bindingAt (.ident "progN") | throwError "missing progN"
  let some (home, body) := (definitionBody checked.registry id).toOption
    | throwError "missing progN body"
  unless binding.id = id do throwError "unexpected progN declaration identity"
  let leaves ← actionLeaves mod source (home.child .body) none body
  let expected := [("parDie", 18, true), ("sendVote", 14, true), ("abortOnVote", 15, true),
    ("abortOnTimeoutRequest", 16, true), ("decide", 17, true), ("coordDie", 13, false),
    ("makeDecision", 11, false), ("request", 8, true), ("getVote", 9, true),
    ("detectFault", 10, true), ("coordBroadcast", 12, true)]
  unless leaves = expected do throwError "unexpected progN disjuncts: {reprStr leaves}"
  let action ← match Collections.lowerAction checked.registry [] noPrimitives 32 id with
    | .ok action => pure action
    | .error error => throwError "ACP_SB progN lowering: {reprStr error}"
  Meta.mkAppM ``Collections.CheckedAction.mk #[← quoteChecked action.expression]

private def emitSelections : TermElabM Lean.Expr := do
  let checked ← checkedSource
  let initial ← quoteChecked (← select checked "Init" 7)
  let invariant ← quoteChecked (← select checked "TypeInv" 4)
  let states ← Meta.mkAppM ``Prod.mk #[initial, invariant]
  let action ← emitNext checked
  logInfo "Intact ACP_SB: all 40 units checked, Init, TypeInv and all 11 progN actions lowered"
  Meta.mkAppM ``Prod.mk #[states, action]

end

private noncomputable def sourceSelections :
    (CheckedExpr noPrimitives .collections × CheckedExpr noPrimitives .collections) ×
      Collections.CheckedAction noPrimitives := by_elab emitSelections

private noncomputable def selections :
    CheckedExpr noPrimitives .collections × CheckedExpr noPrimitives .collections :=
  sourceSelections.1

private noncomputable def progN : Collections.CheckedAction noPrimitives := sourceSelections.2

private abbrev V := Value.{0}
private abbrev Name := ULift.{1} BindingId
private abbrev Scope := DataBridge.scope Name Name
private abbrev Rigid := DataBridge.RigidEnv V Scope
private abbrev State := DataBridge.State V Scope
private abbrev Schema := List (String × SetData.{0})

private def noExternal : ExternalInterpretation V noPrimitives := fun _ _ impossible => nomatch impossible

private meta abbrev participantsId := member 0 0
private meta abbrev yesId := member 0 1
private meta abbrev noId := member 0 2
private meta abbrev undecidedId := member 0 3
private meta abbrev commitId := member 0 4
private meta abbrev abortId := member 0 5
private meta abbrev waitingId := member 0 6
private meta abbrev notsentId := member 0 7
private meta abbrev participantId := member 1 0
private meta abbrev coordinatorId := member 1 1

private def rigidValue (ρ : Rigid) (id : BindingId) : V := ρ PUnit.unit (ULift.up id)
private def stateValue (s : State) (id : BindingId) : V := s PUnit.unit (ULift.up id)

private noncomputable def initialParticipantSchema (ρ : Rigid) : Schema :=
  [("vote", SetData.enum [rigidValue ρ yesId, rigidValue ρ noId]),
   ("alive", SetData.enum [Value.boolean true]),
   ("decision", SetData.enum [rigidValue ρ undecidedId]),
   ("faulty", SetData.enum [Value.boolean false]),
   ("voteSent", SetData.enum [Value.boolean false])]

private def booleanValues : SetData.{0} := SetData.enum [Value.boolean true, Value.boolean false]

private noncomputable def invariantParticipantSchema (ρ : Rigid) : Schema :=
  [("vote", SetData.enum [rigidValue ρ yesId, rigidValue ρ noId]),
   ("alive", booleanValues),
   ("decision", SetData.enum [rigidValue ρ undecidedId, rigidValue ρ commitId, rigidValue ρ abortId]),
   ("faulty", booleanValues),
   ("voteSent", booleanValues)]

private noncomputable def initialCoordinatorSchema (ρ : Rigid) (P : SetData.{0}) : Schema :=
  [("request", P.functionSet (SetData.enum [Value.boolean false])),
   ("vote", P.functionSet (SetData.enum [rigidValue ρ waitingId])),
   ("alive", SetData.enum [Value.boolean true]),
   ("broadcast", P.functionSet (SetData.enum [rigidValue ρ notsentId])),
   ("decision", SetData.enum [rigidValue ρ undecidedId]),
   ("faulty", SetData.enum [Value.boolean false])]

private noncomputable def invariantCoordinatorSchema (ρ : Rigid) (P : SetData.{0}) : Schema :=
  [("request", P.functionSet booleanValues),
   ("vote", P.functionSet (SetData.enum [rigidValue ρ waitingId, rigidValue ρ yesId, rigidValue ρ noId])),
   ("broadcast", P.functionSet (SetData.enum [rigidValue ρ commitId, rigidValue ρ abortId, rigidValue ρ notsentId])),
   ("decision", SetData.enum [rigidValue ρ commitId, rigidValue ρ abortId, rigidValue ρ undecidedId]),
   ("alive", booleanValues),
   ("faulty", booleanValues)]

private noncomputable def predicate (policy : Tagged.Policy.{0})
    (invalid : Tagged.CollectionPolicy.{0}) (selected : CheckedExpr noPrimitives .collections) :
    DataBridge.StatePredicate V Scope :=
  fun ρ s => policy.booleans.holds
    (selected.eval (policy.collectionOperations invalid) policy.booleans noExternal
      ⟨fun id => ρ PUnit.unit (ULift.up id), fun id => s PUnit.unit (ULift.up id)⟩)

private noncomputable def formula (policy : Tagged.Policy.{0})
    (invalid : Tagged.CollectionPolicy.{0}) (selected : CheckedExpr noPrimitives .collections) :
    General.Formula (DataBridge.Carrier V) Scope :=
  .state (.atom (predicate policy invalid selected))

private noncomputable def actionHolds (policy : Tagged.Policy.{0})
    (invalid : Tagged.CollectionPolicy.{0}) (ρ : Rigid) (s t : State) : Prop :=
  policy.booleans.holds (progN.eval (policy.collectionOperations invalid) policy.booleans noExternal
    ⟨rigidValue ρ, stateValue s, stateValue t⟩)

private theorem ofProp_isBoolean (B : Booleans V) (p : Prop) : B.IsBoolean (B.ofProp p) := by
  by_cases p <;> simp [Booleans.ofProp, Booleans.IsBoolean, *]

private theorem ofProp_or (B : Booleans V) (p q : Prop) :
    Logic.or.eval B (B.ofProp p) (B.ofProp q) = B.ofProp (p ∨ q) := by
  have distinct : B.falseValue ≠ B.trueValue := fun eq => B.not_holds_false (eq ▸ B.holds_true)
  by_cases hp : p <;> by_cases hq : q <;>
    simp [Logic.eval, Logic.holds, Booleans.IsBoolean, B.not_holds_false, distinct, hp, hq]

open Classical in
private noncomputable def negValue (B : Booleans V) (v : V) : V :=
  if B.IsBoolean v then B.ofProp (¬ B.holds v) else B.invalid .negation [v]

private theorem eval_neg (ops : CollectionOperations V) (B : Booleans V)
    (env : Valuation V) (arg : Term noPrimitives .collections)
    (witnesses : Nat → V) (target : BindingId → V) :
    (Term.not arg).eval ops B noExternal env witnesses target =
      negValue B (arg.eval ops B noExternal env witnesses target) := by
  rw [Term.eval.eq_def]
  rfl

private theorem neg_ofProp (B : Booleans V) (p : Prop) :
    negValue B (B.ofProp p) = B.ofProp (¬ p) := by
  simp [negValue, ofProp_isBoolean, Booleans.holds_ofProp]

open Classical in
private noncomputable def junctionValue {α : Type*}
    (kind : Surface.Junction) (B : Booleans α) (vs : List α) : α :=
  let (absorbing, identity) := match kind with
    | .conjunction => (B.falseValue, B.trueValue)
    | .disjunction => (B.trueValue, B.falseValue)
  if absorbing ∈ vs then absorbing
  else if ∀ v ∈ vs, B.IsBoolean v then identity
  else B.invalid (.junction kind) vs

private theorem eval_junction (ops : CollectionOperations V) (B : Booleans V)
    (env : Valuation V) (kind : Surface.Junction) (items : List (Term noPrimitives .collections))
    (witnesses : Nat → V) (target : BindingId → V) :
    (Term.junction kind items).eval ops B noExternal env witnesses target =
      junctionValue kind B (Term.evalList ops B noExternal env items witnesses target) := by
  rw [Term.eval.eq_def]
  rfl

private theorem conjunction_ofProp (B : Booleans V) (vs : List V)
    (typed : ∀ v ∈ vs, B.IsBoolean v) :
    junctionValue .conjunction B vs = B.ofProp (∀ v ∈ vs, B.holds v) := by
  classical
  simp only [junctionValue]
  by_cases falseOccurs : B.falseValue ∈ vs
  · have rejected : ¬ ∀ v ∈ vs, B.holds v := fun all => B.not_holds_false (all _ falseOccurs)
    rw [ite_eq_left falseOccurs, Booleans.ofProp, ite_eq_right rejected]
  · have accepted : ∀ v ∈ vs, B.holds v := by
      intro v hv
      rcases typed v hv with rfl | rfl
      · exact B.holds_true
      · exact False.elim (falseOccurs hv)
    rw [ite_eq_right falseOccurs, ite_eq_left typed, Booleans.ofProp, ite_eq_left accepted]

private theorem disjunction_ofProp (B : Booleans V) (vs : List V)
    (typed : ∀ v ∈ vs, B.IsBoolean v) :
    junctionValue .disjunction B vs = B.ofProp (∃ v ∈ vs, B.holds v) := by
  classical
  simp only [junctionValue]
  by_cases trueOccurs : B.trueValue ∈ vs
  · have accepted : ∃ v ∈ vs, B.holds v := ⟨_, trueOccurs, B.holds_true⟩
    rw [ite_eq_left trueOccurs, Booleans.ofProp, ite_eq_left accepted]
  · have rejected : ¬ ∃ v ∈ vs, B.holds v := by
      rintro ⟨v, hv, holds⟩
      rcases typed v hv with rfl | rfl
      · exact trueOccurs hv
      · exact B.not_holds_false holds
    rw [ite_eq_right trueOccurs, ite_eq_left typed, Booleans.ofProp, ite_eq_right rejected]

private theorem holds_and_ofProp (B : Booleans V) (p q : Prop) :
    B.holds (Logic.and.eval B (B.ofProp p) (B.ofProp q)) ↔ p ∧ q := by
  have distinct : B.trueValue ≠ B.falseValue := fun eq => B.not_holds_false (eq ▸ B.holds_true)
  by_cases hp : p <;> by_cases hq : q <;>
    simp [Logic.eval, Logic.holds, Booleans.IsBoolean, B.holds_true, B.not_holds_false, distinct, hp, hq]

private theorem init_membership (policy : Tagged.Policy.{0}) (invalid : Tagged.CollectionPolicy.{0})
    (ρ : Rigid) (s : State) (P : SetData.{0}) (domain : (rigidValue ρ participantsId).asSet = some P) :
    predicate policy invalid selections.1 ρ s ↔
      (P.functionSet (SetData.recordSet (initialParticipantSchema ρ))).mem (stateValue s participantId) ∧
      (SetData.recordSet (initialCoordinatorSchema ρ P)).mem (stateValue s coordinatorId) := by
  simp [rigidValue] at domain
  simp [predicate, selections, sourceSelections, CheckedExpr.eval, Term.eval, Term.evalFields, Term.evalList,
    Operations.collection, Tagged.Policy.collectionOperations, Tagged.Policy.operations,
    Tagged.Policy.booleans, Value.recordSet, Value.checkRecordSetFields,
    Value.decodeRecordSetBounds, Except.map, initialParticipantSchema, initialCoordinatorSchema, rigidValue,
    stateValue, domain, holds_and_ofProp]

private theorem typeInv_membership (policy : Tagged.Policy.{0}) (invalid : Tagged.CollectionPolicy.{0})
    (ρ : Rigid) (s : State) (P : SetData.{0}) (domain : (rigidValue ρ participantsId).asSet = some P) :
    predicate policy invalid selections.2 ρ s ↔
      (P.functionSet (SetData.recordSet (invariantParticipantSchema ρ))).mem (stateValue s participantId) ∧
      (SetData.recordSet (invariantCoordinatorSchema ρ P)).mem (stateValue s coordinatorId) := by
  simp [rigidValue] at domain
  simp [predicate, selections, sourceSelections, CheckedExpr.eval, Term.eval, Term.evalFields, Term.evalList,
    Operations.collection, Tagged.Policy.collectionOperations, Tagged.Policy.operations,
    Tagged.Policy.booleans, Value.recordSet, Value.checkRecordSetFields,
    Value.decodeRecordSetBounds, Except.map, invariantParticipantSchema, invariantCoordinatorSchema, booleanValues,
    rigidValue, stateValue, domain, holds_and_ofProp]

private def matchesRecord (fields : Schema) (v : V) : Prop :=
  ∃ g, Value.function g = v ∧ g.domain = SetData.recordSetKeys fields ∧ g.fitsRecordSet fields

private def matchesState (P : SetData.{0}) (participantSchema coordinatorSchema : Schema) (s : State) : Prop :=
  (∃ g, Value.function g = stateValue s participantId ∧ g.domain = P ∧
    ∀ k v, g.relates k v → matchesRecord participantSchema v) ∧
  matchesRecord coordinatorSchema (stateValue s coordinatorId)

private theorem matchesRecord.field {fields : Schema} {v : V} {name : String}
    {bound : SetData.{0}} (h : matchesRecord fields v) (entry : (name, bound) ∈ fields)
    (policy : Unspecified.{0}) : bound.mem (Value.apply policy v (Value.string name)) := by
  obtain ⟨g, rfl, _, fits⟩ := h
  obtain ⟨field, lookup, typed⟩ := fits name bound entry
  rwa [Value.apply_function policy (Graph.lookup_eq_some.mp lookup)]

private theorem functionSet_at {P range : SetData.{0}} {v i : V}
    (h : (P.functionSet range).mem v) (hi : P.mem i) (policy : Unspecified.{0}) :
    range.mem (Value.apply policy v i) := by
  obtain ⟨g, rfl, rfl, typed⟩ := SetData.mem_functionSet.mp h
  obtain ⟨y, edge⟩ := Graph.mem_domain.mp hi
  rw [Value.apply_function policy edge]
  exact typed i y edge

private theorem matchesState.participant {P : SetData.{0}} {p c : Schema} {s : State}
    (h : matchesState P p c s) {i : V} (hi : P.mem i) (policy : Unspecified.{0}) :
    matchesRecord p (Value.apply policy (stateValue s participantId) i) := by
  obtain ⟨g, value, domain, typed⟩ := h.1
  obtain ⟨y, edge⟩ := Graph.mem_domain.mp (domain ▸ hi)
  rw [← value, Value.apply_function policy edge]
  exact typed i y edge

private theorem matchesRecord.update {fields : Schema} {root v : V} {name : String}
    (h : matchesRecord fields root) (policy : Unspecified.{0})
    (typed : ∀ bound, (name, bound) ∈ fields → bound.mem v) :
    matchesRecord fields (Value.update policy root (Value.string name) v) := by
  obtain ⟨g, rfl, keys, fits⟩ := h
  refine ⟨g.update (Value.string name) v, (Value.update_function _ _ _ _).symm,
    (Graph.domain_update ..).trans keys, ?_⟩
  intro field bound entry
  obtain ⟨old, lookup, oldTyped⟩ := fits field bound entry
  by_cases same : field = name
  · subst field
    have present := Graph.mem_domain.mpr ⟨old, Graph.lookup_eq_some.mp lookup⟩
    exact ⟨v, Graph.lookup_update present, typed bound entry⟩
  · exact ⟨old, (Graph.lookup_update_other (fun eq => same (Value.string_injective eq))).trans lookup,
      oldTyped⟩

private theorem functionSet_update {P range : SetData.{0}} {root i v : V}
    (h : (P.functionSet range).mem root) (hi : P.mem i) (good : range.mem v)
    (policy : Unspecified.{0}) : (P.functionSet range).mem (Value.update policy root i v) := by
  obtain ⟨g, rfl, rfl, typed⟩ := SetData.mem_functionSet.mp h
  refine SetData.mem_functionSet.mpr ⟨g.update i v, (Value.update_function _ _ _ _).symm,
    Graph.domain_update .., ?_⟩
  intro k y edge
  have lookup := Graph.lookup_eq_some.mpr edge
  by_cases same : k = i
  · subst k
    rw [Graph.lookup_update hi] at lookup
    cases lookup
    exact good
  · rw [Graph.lookup_update_other same] at lookup
    exact typed k y (Graph.lookup_eq_some.mp lookup)

private def test (policy : Unspecified.{0}) (root key : V) : Prop :=
  (Value.apply policy root key).isTrue

private theorem reify_test (policy : Tagged.Policy.{0}) {root key : V}
    (h : booleanValues.mem (Value.apply policy.numeric root key)) :
    Value.apply policy.numeric root key = policy.booleans.ofProp (test policy.numeric root key) := by
  rcases (SetData.mem_enum _ _).mp h with h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  unfold test
  rcases h with h | h <;>
    simp [h, Tagged.Policy.booleans, Value.isTrue_boolean]

private theorem tuple_singleton_eq (a b : V) : Value.tuple [a] = Value.tuple [b] ↔ a = b :=
  ⟨fun eq => List.cons.inj (Graph.tuple_injective (Value.function_injective eq)) |>.1,
    fun eq => congrArg (fun v => Value.tuple [v]) eq⟩

private theorem forall_values_cons (p : V → Prop) (v : V) (vs : List V) :
    (∀ x ∈ v :: vs, p x) ↔ p v ∧ ∀ x ∈ vs, p x := by
  simp only [List.mem_cons, forall_eq_or_imp]

private theorem exists_values_cons (B : Booleans V) (v : V) (vs : List V) :
    (∃ x ∈ v :: vs, B.holds x) ↔ B.holds v ∨ ∃ x ∈ vs, B.holds x := by
  simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left]

private theorem collection_self (ops : CollectionOperations V) (h : Fragment.collections = .collections) :
    Operations.collection ops h = ops := rfl

private theorem eval_one_binder (ops : CollectionOperations V) (B : Booleans V)
    (env : Valuation V) (kind : Surface.Quantifier) (slot : Nat)
    (domain body : Term noPrimitives .collections) (w : Nat → V) (target : BindingId → V)
    (h : Fragment.collections = .collections) :
    (Term.bounded h (.quant kind) [([.name slot], domain)] body).eval
        ops B noExternal env w target =
      B.ofProp (match kind with
        | .exists => ∃ x, ops.mem x (domain.eval ops B noExternal env w target) ∧
            B.holds (body.eval ops B noExternal env (withWitness w slot x) target)
        | .forall => ∀ x, ops.mem x (domain.eval ops B noExternal env w target) →
            B.holds (body.eval ops B noExternal env (withWitness w slot x) target)) := by
  cases h
  cases kind <;>
    simp [Term.eval, Term.evalBounds, Bounded.axes, Bounded.quantify, BinderPattern.bind,
      collection_self, ← and_assoc, and_comm]

private def stepCases (policy : Tagged.Policy.{0}) (ρ : Rigid) (P : SetData.{0}) (s t : State) : Prop :=
  let numeric := policy.numeric
  let p := stateValue s participantId
  let c := stateValue s coordinatorId
  let p' := stateValue t participantId
  let c' := stateValue t coordinatorId
  let get := Value.apply numeric
  let field := fun v name => get v (Value.string name)
  let bit := fun v name => test numeric v (Value.string name)
  let write := Value.update numeric
  let put := fun v name x => write v (Value.string name) x
  let yes := rigidValue ρ yesId
  let no := rigidValue ρ noId
  let waiting := rigidValue ρ waitingId
  let undecided := rigidValue ρ undecidedId
  let commit := rigidValue ρ commitId
  let abort := rigidValue ρ abortId
  let notsent := rigidValue ρ notsentId
  let kill := fun v => put (put v "alive" (Value.boolean false)) "faulty" (Value.boolean true)
  (∃ i, P.mem i ∧
    let r := get p i
    let request := test numeric (field c "request") i
    (bit r "alive" ∧ p' = write p i (kill r) ∧ c' = c) ∨
    (bit r "alive" ∧ request ∧ p' = write p i (put r "voteSent" (Value.boolean true)) ∧ c' = c) ∨
    (bit r "alive" ∧ field r "decision" = undecided ∧ bit r "voteSent" ∧ field r "vote" = no ∧
      p' = write p i (put r "decision" abort) ∧ c' = c) ∨
    (bit r "alive" ∧ field r "decision" = undecided ∧ ¬bit c "alive" ∧ ¬request ∧
      p' = write p i (put r "decision" abort) ∧ c' = c) ∨
    (bit r "alive" ∧ field r "decision" = undecided ∧ get (field c "broadcast") i ≠ notsent ∧
      p' = write p i (put r "decision" (get (field c "broadcast") i)) ∧ c' = c)) ∨
  (bit c "alive" ∧ c' = kill c ∧ p' = p) ∨
  (bit c "alive" ∧ field c "decision" = undecided ∧
    (∀ j, P.mem j → (get (field c "vote") j).mem (Value.set (SetData.enum [yes, no]))) ∧
    (((∀ j, P.mem j → get (field c "vote") j = yes) ∧ c' = put c "decision" commit) ∨
      ((∃ j, P.mem j ∧ get (field c "vote") j = no) ∧ c' = put c "decision" abort)) ∧ p' = p) ∨
  (∃ i, P.mem i ∧
    let r := get p i
    let allRequested := ∀ j, P.mem j → test numeric (field c "request") j
    (bit c "alive" ∧ ¬test numeric (field c "request") i ∧
      c' = put c "request" (write (field c "request") i (Value.boolean true)) ∧ p' = p) ∨
    (bit c "alive" ∧ field c "decision" = undecided ∧ allRequested ∧ get (field c "vote") i = waiting ∧
      bit r "voteSent" ∧ c' = put c "vote" (write (field c "vote") i (field r "vote")) ∧ p' = p) ∨
    (bit c "alive" ∧ field c "decision" = undecided ∧ allRequested ∧ get (field c "vote") i = waiting ∧
      ¬bit r "alive" ∧ ¬bit r "voteSent" ∧ c' = put c "decision" abort ∧ p' = p) ∨
    (bit c "alive" ∧ field c "decision" ≠ undecided ∧ get (field c "broadcast") i = notsent ∧
      c' = put c "broadcast" (write (field c "broadcast") i (field c "decision")) ∧ p' = p))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem progN_holds_iff (policy : Tagged.Policy.{0}) (invalid : Tagged.CollectionPolicy.{0})
    (ρ : Rigid) (P : SetData.{0}) (s t : State)
    (domain : (rigidValue ρ participantsId).asSet = some P)
    (typed : matchesState P (invariantParticipantSchema ρ) (invariantCoordinatorSchema ρ P) s) :
    actionHolds policy invalid ρ s t ↔ stepCases policy ρ P s t := by
  have inParticipants (i : V) : i.mem (rigidValue ρ participantsId) ↔ P.mem i :=
    show i.mem _ ↔ _ by rw [← Value.asSet_eq_some.mp domain, Value.mem_set]
  have coordAlive := reify_test policy (typed.2.field (name := "alive") (bound := booleanValues)
    (by simp [invariantCoordinatorSchema]) policy.numeric)
  have requests := typed.2.field (name := "request") (bound := P.functionSet booleanValues)
    (by simp [invariantCoordinatorSchema]) policy.numeric
  have coordRequest (i : V) (hi : P.mem i) := reify_test policy (functionSet_at requests hi policy.numeric)
  have parAlive (i : V) (hi : P.mem i) := reify_test policy
    ((typed.participant hi policy.numeric).field (name := "alive") (bound := booleanValues)
      (by simp [invariantParticipantSchema]) policy.numeric)
  have parSent (i : V) (hi : P.mem i) := reify_test policy
    ((typed.participant hi policy.numeric).field (name := "voteSent") (bound := booleanValues)
      (by simp [invariantParticipantSchema]) policy.numeric)
  classical
  simp only [actionHolds, progN, sourceSelections, Collections.CheckedAction.eval,
    ↓eval_junction, ↓eval_one_binder, ↓eval_neg,
    Term.eval, Term.evalList, Term.evalClauses, collection_self, Tagged.Policy.collectionOperations,
    Tagged.Policy.operations, withWitness, Nat.reduceEqDiff, eq_self, ite_true, ite_false,
    List.map_cons, List.map_nil, inParticipants, Value.updateClauses_cons, Value.updateClauses_nil,
    Value.updatePath_single, tuple_singleton_eq, Bool.false_eq_true]
  simp (config := { contextual := true }) only [
    coordAlive, coordRequest, ofProp_or, ofProp_isBoolean, neg_ofProp,
    conjunction_ofProp, disjunction_ofProp, Booleans.holds_ofProp, forall_values_cons,
    exists_values_cons, List.not_mem_nil, false_implies, implies_true,
    and_true, or_false, false_and, exists_false, stepCases]
  refine or_congr (exists_congr fun i => and_congr_right fun hi => ?_)
    (or_congr Iff.rfl (or_congr Iff.rfl (exists_congr fun i => and_congr_right fun hi => ?_)))
  all_goals
    simp only [parAlive _ hi, parSent _ hi, coordRequest _ hi, ofProp_or, ofProp_isBoolean,
      neg_ofProp, conjunction_ofProp, Booleans.holds_ofProp, forall_values_cons,
      List.not_mem_nil, false_implies, implies_true, and_true, or_assoc]; rfl

private theorem matchesState_iff (P : SetData.{0}) (participantSchema coordinatorSchema : Schema) (s : State) :
    matchesState P participantSchema coordinatorSchema s ↔
      (P.functionSet (SetData.recordSet participantSchema)).mem (stateValue s participantId) ∧
      (SetData.recordSet coordinatorSchema).mem (stateValue s coordinatorId) := by
  simp only [matchesState, matchesRecord, SetData.mem_functionSet, SetData.mem_recordSet]

private theorem init_holds_iff (policy : Tagged.Policy.{0}) (invalid : Tagged.CollectionPolicy.{0})
    (ρ : Rigid) (σ : Behavior State) (i : Nat) (P : SetData.{0})
    (domain : (rigidValue ρ participantsId).asSet = some P) :
    (formula policy invalid selections.1).Holds ρ σ i ↔
      matchesState P (initialParticipantSchema ρ) (initialCoordinatorSchema ρ P) (σ i) := by
  rw [formula, DataBridge.state_holds, init_membership policy invalid ρ (σ i) P domain,
    matchesState_iff]

private theorem typeInv_holds_iff (policy : Tagged.Policy.{0}) (invalid : Tagged.CollectionPolicy.{0})
    (ρ : Rigid) (σ : Behavior State) (i : Nat) (P : SetData.{0})
    (domain : (rigidValue ρ participantsId).asSet = some P) :
    (formula policy invalid selections.2).Holds ρ σ i ↔
      matchesState P (invariantParticipantSchema ρ) (invariantCoordinatorSchema ρ P) (σ i) := by
  rw [formula, DataBridge.state_holds, typeInv_membership policy invalid ρ (σ i) P domain,
    matchesState_iff]

private theorem enum_mono {xs ys : List V} (sub : ∀ v, v ∈ xs → v ∈ ys) (v : V)
    (h : (SetData.enum xs).mem v) : (SetData.enum ys).mem v :=
  (SetData.mem_enum _ _).mpr (sub v ((SetData.mem_enum _ _).mp h))

private theorem functionSet_mono {D S T : SetData.{0}} (sub : ∀ v, S.mem v → T.mem v) (v : V)
    (h : (D.functionSet S).mem v) : (D.functionSet T).mem v := by
  obtain ⟨g, value, domain, range⟩ := SetData.mem_functionSet.mp h
  exact SetData.mem_functionSet.mpr ⟨g, value, domain, fun x y edge => sub y (range x y edge)⟩

private structure SchemaInclusion (lower upper : Schema) : Prop where
  sameKeys : SetData.recordSetKeys lower = SetData.recordSetKeys upper
  bounds : ∀ name bound, (name, bound) ∈ upper →
    ∃ initial, (name, initial) ∈ lower ∧ ∀ v, initial.mem v → bound.mem v

private theorem SchemaInclusion.matches {lower upper : Schema} (inclusion : SchemaInclusion lower upper)
    {v : V} (h : matchesRecord lower v) : matchesRecord upper v := by
  obtain ⟨g, value, keys, fits⟩ := h
  refine ⟨g, value, keys.trans inclusion.sameKeys, ?_⟩
  intro name bound found
  obtain ⟨initial, member, sub⟩ := inclusion.bounds name bound found
  obtain ⟨field, lookup, proof⟩ := fits name initial member
  exact ⟨field, lookup, sub field proof⟩

private theorem participant_inclusion (ρ : Rigid) :
    SchemaInclusion (initialParticipantSchema ρ) (invariantParticipantSchema ρ) where
  sameKeys := rfl
  bounds := by
    intro name bound h
    simp only [invariantParticipantSchema, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h <;> cases h
    · exact ⟨_, by simp [initialParticipantSchema], fun _ h => h⟩
    · exact ⟨SetData.enum [Value.boolean true], by simp [initialParticipantSchema],
        enum_mono (by simp)⟩
    · exact ⟨SetData.enum [rigidValue ρ undecidedId], by simp [initialParticipantSchema], enum_mono (by simp)⟩
    · exact ⟨SetData.enum [Value.boolean false], by simp [initialParticipantSchema],
        enum_mono (by simp)⟩
    · exact ⟨SetData.enum [Value.boolean false], by simp [initialParticipantSchema],
        enum_mono (by simp)⟩

private theorem coordinator_inclusion (ρ : Rigid) (P : SetData.{0}) :
    SchemaInclusion (initialCoordinatorSchema ρ P) (invariantCoordinatorSchema ρ P) where
  sameKeys := by
    apply SetData.ext
    intro key
    simp [SetData.mem_recordSetKeys, initialCoordinatorSchema, invariantCoordinatorSchema,
      or_comm, or_left_comm]
  bounds := by
    intro name bound h
    simp only [invariantCoordinatorSchema, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h <;> cases h
    · exact ⟨P.functionSet (SetData.enum [Value.boolean false]), by simp [initialCoordinatorSchema],
        functionSet_mono (enum_mono (by simp))⟩
    · exact ⟨P.functionSet (SetData.enum [rigidValue ρ waitingId]), by simp [initialCoordinatorSchema],
        functionSet_mono (enum_mono (by simp))⟩
    · exact ⟨P.functionSet (SetData.enum [rigidValue ρ notsentId]), by simp [initialCoordinatorSchema],
        functionSet_mono (enum_mono (by simp))⟩
    · exact ⟨SetData.enum [rigidValue ρ undecidedId], by simp [initialCoordinatorSchema], enum_mono (by simp)⟩
    · exact ⟨SetData.enum [Value.boolean true], by simp [initialCoordinatorSchema],
        enum_mono (by simp)⟩
    · exact ⟨SetData.enum [Value.boolean false], by simp [initialCoordinatorSchema],
        enum_mono (by simp)⟩

/-- Initialization narrows each field range while keeping the exact domains. -/
private theorem init_implies_typeInv (policy : Tagged.Policy.{0})
    (invalid : Tagged.CollectionPolicy.{0}) (ρ : Rigid) (σ : Behavior State) (i : Nat)
    (P : SetData.{0}) (domain : (rigidValue ρ participantsId).asSet = some P)
    (init : (formula policy invalid selections.1).Holds ρ σ i) :
    (formula policy invalid selections.2).Holds ρ σ i := by
  obtain ⟨⟨g, value, keys, fits⟩, coordinator⟩ :=
    (init_holds_iff policy invalid ρ σ i P domain).mp init
  exact (typeInv_holds_iff policy invalid ρ σ i P domain).mpr
    ⟨⟨g, value, keys, fun k v edge => (participant_inclusion ρ).matches (fits k v edge)⟩,
      (coordinator_inclusion ρ P).matches coordinator⟩

private theorem stepCases_preserve (policy : Tagged.Policy.{0}) (ρ : Rigid) (P : SetData.{0})
    (s t : State)
    (current : matchesState P (invariantParticipantSchema ρ) (invariantCoordinatorSchema ρ P) s)
    (step : stepCases policy ρ P s t) :
    matchesState P (invariantParticipantSchema ρ) (invariantCoordinatorSchema ρ P) t := by
  let get := Value.apply policy.numeric
  let p := stateValue s participantId
  let c := stateValue s coordinatorId
  let p' := stateValue t participantId
  let c' := stateValue t coordinatorId
  let par := invariantParticipantSchema ρ
  let coord := invariantCoordinatorSchema ρ P
  have graphs := (matchesState_iff P par coord s).mp current
  have parStep {i v : V} (hi : P.mem i) (changePar : p' = Value.update policy.numeric p i v)
      (keepCoord : c' = c) (updated : matchesRecord par v) :
      matchesState P par coord t := by
    apply (matchesState_iff P par coord t).mpr
    change (P.functionSet (SetData.recordSet par)).mem p' ∧ (SetData.recordSet coord).mem c'
    rw [changePar, keepCoord]
    exact ⟨functionSet_update graphs.1 hi (SetData.mem_recordSet.mpr updated) policy.numeric, graphs.2⟩
  have coordStep {v : V} (changeCoord : c' = v) (keepPar : p' = p)
      (updated : matchesRecord coord v) : matchesState P par coord t := by
    apply (matchesState_iff P par coord t).mpr
    change (P.functionSet (SetData.recordSet par)).mem p' ∧ (SetData.recordSet coord).mem c'
    rw [keepPar, changeCoord]
    exact ⟨graphs.1, SetData.mem_recordSet.mpr updated⟩
  have parRecord {i : V} (hi : P.mem i) : matchesRecord par (get p i) :=
    current.participant hi policy.numeric
  have coordRecord : matchesRecord coord c := current.2
  rcases step with participants | died | decided | messages
  · obtain ⟨i, hi, cases⟩ := participants
    rcases cases with ⟨_, changePar, keepCoord⟩ | ⟨_, _, changePar, keepCoord⟩ |
      ⟨_, _, _, _, changePar, keepCoord⟩ | ⟨_, _, _, _, changePar, keepCoord⟩ |
      ⟨_, _, received, changePar, keepCoord⟩
    · apply parStep hi changePar keepCoord
      apply matchesRecord.update (matchesRecord.update (parRecord hi) _ ?_) _
      all_goals simp [par, invariantParticipantSchema, booleanValues, SetData.mem_enum]
    · apply parStep hi changePar keepCoord
      apply matchesRecord.update (parRecord hi) _
      simp [par, invariantParticipantSchema, booleanValues, SetData.mem_enum]
    · apply parStep hi changePar keepCoord
      apply matchesRecord.update (parRecord hi) _
      simp [par, invariantParticipantSchema, SetData.mem_enum]
    · apply parStep hi changePar keepCoord
      apply matchesRecord.update (parRecord hi) _
      simp [par, invariantParticipantSchema, SetData.mem_enum]
    · apply parStep hi changePar keepCoord
      apply matchesRecord.update (parRecord hi) _
      simp [par, invariantParticipantSchema]
      let broadcast := SetData.enum [rigidValue ρ commitId, rigidValue ρ abortId, rigidValue ρ notsentId]
      have broadcasts := coordRecord.field (name := "broadcast") (bound := P.functionSet broadcast)
        (by simp [coord, invariantCoordinatorSchema, broadcast]) policy.numeric
      have value := functionSet_at broadcasts hi policy.numeric
      simp only [broadcast, SetData.mem_enum, List.mem_cons, List.not_mem_nil, or_false] at value
      rcases value with eq | eq | eq
      · exact Or.inr (Or.inl eq)
      · exact Or.inr (Or.inr eq)
      · exact False.elim (received eq)
  · obtain ⟨_, changeCoord, keepPar⟩ := died
    apply coordStep changeCoord keepPar
    apply matchesRecord.update (matchesRecord.update coordRecord _ ?_) _
    all_goals simp [coord, invariantCoordinatorSchema, booleanValues, SetData.mem_enum]
  · obtain ⟨_, _, _, result, keepPar⟩ := decided
    rcases result with ⟨_, changeCoord⟩ | ⟨_, changeCoord⟩ <;>
      apply coordStep changeCoord keepPar <;>
      apply matchesRecord.update coordRecord _ <;>
      simp [coord, invariantCoordinatorSchema, SetData.mem_enum]
  · obtain ⟨i, hi, cases⟩ := messages
    rcases cases with ⟨_, _, changeCoord, keepPar⟩ |
      ⟨_, _, _, _, _, changeCoord, keepPar⟩ |
      ⟨_, _, _, _, _, _, changeCoord, keepPar⟩ |
      ⟨_, chosen, _, changeCoord, keepPar⟩
    · apply coordStep changeCoord keepPar
      apply matchesRecord.update coordRecord _
      simp [coord, invariantCoordinatorSchema]
      exact functionSet_update (coordRecord.field (by simp [coord, invariantCoordinatorSchema]) _)
        hi (by simp [booleanValues, SetData.mem_enum]) _
    · apply coordStep changeCoord keepPar
      apply matchesRecord.update coordRecord _
      simp [coord, invariantCoordinatorSchema]
      refine functionSet_update (coordRecord.field (by simp [coord, invariantCoordinatorSchema]) _) hi ?_ _
      apply enum_mono (xs := [rigidValue ρ yesId, rigidValue ρ noId]) (by simp)
      exact (parRecord hi).field (by simp [par, invariantParticipantSchema]) _
    · apply coordStep changeCoord keepPar
      apply matchesRecord.update coordRecord _
      simp [coord, invariantCoordinatorSchema, SetData.mem_enum]
    · apply coordStep changeCoord keepPar
      apply matchesRecord.update coordRecord _
      simp [coord, invariantCoordinatorSchema]
      refine functionSet_update (coordRecord.field (by simp [coord, invariantCoordinatorSchema]) _) hi ?_ _
      let decisions := SetData.enum [rigidValue ρ commitId, rigidValue ρ abortId, rigidValue ρ undecidedId]
      have value := coordRecord.field (name := "decision") (bound := decisions)
        (by simp [coord, invariantCoordinatorSchema, decisions]) policy.numeric
      simp only [decisions, SetData.mem_enum, List.mem_cons, List.not_mem_nil, or_false] at value
      rcases value with eq | eq | eq
      · exact (SetData.mem_enum _ _).mpr (eq.symm ▸ List.mem_cons_self ..)
      · exact (SetData.mem_enum _ _).mpr (eq.symm ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
      · exact False.elim (chosen eq)

/-- The original `progN` transition preserves the original `TypeInv` at its target. -/
private theorem progN_preserves_typeInv (policy : Tagged.Policy.{0}) (invalid : Tagged.CollectionPolicy.{0})
    (ρ : Rigid) (σ : Behavior State) (i : Nat) (P : SetData.{0})
    (domain : (rigidValue ρ participantsId).asSet = some P)
    (current : (formula policy invalid selections.2).Holds ρ σ i)
    (step : actionHolds policy invalid ρ (σ i) (σ (i + 1))) :
    (formula policy invalid selections.2).Holds ρ σ (i + 1) := by
  have typed := (typeInv_holds_iff policy invalid ρ σ i P domain).mp current
  have cases := (progN_holds_iff policy invalid ρ P (σ i) (σ (i + 1)) domain typed).mp step
  exact (typeInv_holds_iff policy invalid ρ σ (i + 1) P domain).mpr
    (stepCases_preserve policy ρ P (σ i) (σ (i + 1)) typed cases)

open Lean in
run_cmd do
  let declarations := [``init_holds_iff, ``typeInv_holds_iff, ``init_implies_typeInv,
    ``progN_holds_iff, ``progN_preserves_typeInv]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for name in declarations do
    let axioms ← collectAxioms name
    unless axioms.all (· ∈ allowed) do
      throwError "unexpected axioms for {name}: {axioms}"
  logInfo m!"Axiom audit passed for {declarations.length} ACP_SB theorems"

end Silmaril.Logic.Temporal.TLA.SourceAcceptance.ACP_SB
