module

public import Silmaril.Logic.Temporal.TLA.DataElab.Temporal.Thms
import Silmaril.Logic.Temporal.TLA.StutterReduction.Thms
public import Lean
public meta import Lean
meta import Silmaril.Logic.Temporal.TLA.DataElab.Temporal.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs

namespace Silmaril.Logic.Temporal.TLA.SourceAcceptance.Flexible

open DataElab DataElab.Temporal Resolution

private meta def source := r"
---- MODULE Flexible ----
VARIABLE x
Delayed == \EE h : /\ h = FALSE
                   /\ [][(h = TRUE) /\ (h' = FALSE)]_x
                   /\ <>(x = FALSE)
Changes == \EE h : <> <<h' /= h>>_h
Rigid == \E h : <> <<h' /= h>>_h
Dual == \AA h : h = TRUE
Nested == \AA h : \EE k, j : [] ((k /= h) /\ (j = k))
Mixed == \E a : \EE h : [] (h = a)
CanChange == \EE h : (h = FALSE) /\ ENABLED (h' = TRUE)
====
"

private meta abbrev signature : ExternalSignature := fun _ => none

private meta def select (name : String) : Except String (Form signature) := do
  let parsed ← (Surface.Parser.parseModule source).mapError reprStr
  let registry ← (resolveWith .levelSyntax [("root", .parsed parsed [])] "root").mapError reprStr
  let some binding := (registry.moduleAt "root").bind (·.bindingAt (.ident name))
    | throw s!"missing definition {name}"
  let result ← (lowerFormula registry [] (fun _ => none) 32 binding.id).mapError reprStr
  return result.form

meta section

open Lean

deriving instance ToExpr for Resolution.Fixity
deriving instance ToExpr for Resolution.Name
deriving instance ToExpr for Step
deriving instance ToExpr for Site
deriving instance ToExpr for BindingId
deriving instance ToExpr for Logic
deriving instance ToExpr for Surface.Junction
deriving instance ToExpr for Surface.Quantifier

private partial def quoteData (term : DataElab.Term signature) : Elab.Term.TermElabM Lean.Expr := do
  let node := fun ctor fields =>
    mkAppN (mkConst ctor) (#[mkConst ``signature, mkConst ``Fragment.core] ++ fields)
  match term with
  | .flexible id => return node ``DataElab.Term.flexible #[toExpr id]
  | .witness slot => return node ``DataElab.Term.witness #[toExpr slot]
  | .boolean value => return node ``DataElab.Term.boolean #[toExpr value]
  | .prime site operand => return node ``DataElab.Term.prime #[toExpr site, ← quoteData operand]
  | .eq neg l r => return node ``DataElab.Term.eq #[toExpr neg, ← quoteData l, ← quoteData r]
  | _ => throwError "unexpected fixture data term: {reprStr term}"

private def quoteChecked (e : ScopedExpr signature) : Elab.Term.TermElabM Lean.Expr := do
  Meta.mkAppM ``ScopedExpr.mk #[← quoteData e.term, toExpr e.slots, ← Meta.mkEqRefl (toExpr true)]

private partial def quotePred : Predicate signature → Elab.Term.TermElabM Lean.Expr
  | .data e => do Meta.mkAppM ``Predicate.data #[← quoteChecked e]
  | .binary op p q => do Meta.mkAppM ``Predicate.binary #[toExpr op, ← quotePred p, ← quotePred q]
  | .enabled p => do Meta.mkAppM ``Predicate.enabled #[← quotePred p]
  | _ => throwError "unexpected fixture predicate"

private def quoteObs (obs : Observation signature) : Elab.Term.TermElabM Lean.Expr := do
  Meta.mkListLit (mkApp2 (mkConst ``ScopedExpr) (mkConst ``signature) (mkConst ``Fragment.core)) (← obs.mapM quoteChecked)

private partial def quoteForm : Form signature → Elab.Term.TermElabM Lean.Expr
  | .state p => do Meta.mkAppM ``Form.state #[← quotePred p]
  | .binary op p q => do Meta.mkAppM ``Form.binary #[toExpr op, ← quoteForm p, ← quoteForm q]
  | .junction kind items => do
    let forms ← Meta.mkListLit (mkApp2 (mkConst ``Form) (mkConst ``signature) (mkConst ``Fragment.core)) (← items.mapM quoteForm)
    Meta.mkAppM ``Form.junction #[toExpr kind, forms]
  | .flexQuant kind id p => do
    Meta.mkAppM ``Form.flexQuant #[toExpr kind, toExpr id, ← quoteForm p]
  | .rigidQuant kind slot none p => do
    let bound := mkApp (mkConst ``Option.none [0]) (mkApp2 (mkConst ``ScopedExpr) (mkConst ``signature) (mkConst ``Fragment.core))
    Meta.mkAppM ``Form.rigidQuant #[toExpr kind, toExpr slot, bound, ← quoteForm p]
  | .always p => do Meta.mkAppM ``Form.always #[← quoteForm p]
  | .eventually p => do Meta.mkAppM ``Form.eventually #[← quoteForm p]
  | .alwaysBracket p obs => do Meta.mkAppM ``Form.alwaysBracket #[← quotePred p, ← quoteObs obs]
  | .eventuallyAngle p obs => do Meta.mkAppM ``Form.eventuallyAngle #[← quotePred p, ← quoteObs obs]
  | _ => throwError "unexpected fixture temporal form"

private def emit (name : String) : Elab.Term.TermElabM Lean.Expr := do
  match select name with
  | .ok form => quoteForm form
  | .error problem => throwError "{name}: {problem}"

end

private noncomputable def delayed : Form signature := by_elab emit "Delayed"

private def x : BindingId := .declared ⟨"root", [.unit 0, .member 0]⟩

private def booleans : Booleans Bool := ⟨true, false, (· = true), rfl, by decide, fun _ _ => false⟩

private noncomputable def interp (ops : DataOperations Bool) : Interpretation Bool signature :=
  ⟨ops, booleans, fun _ _ h => nomatch h⟩

private abbrev S := State Bool

private noncomputable def denotation (ops : DataOperations Bool) (form : Form signature) : Formula S :=
  form.toFormula (interp ops) (fun _ => false)

private theorem bool_and (p q : Prop) :
    booleans.holds (Logic.and.eval booleans (booleans.ofProp p) (booleans.ofProp q)) ↔ p ∧ q := by
  classical
  by_cases p <;> by_cases q <;> simp_all [Logic.eval, Logic.holds, Booleans.ofProp,
    Booleans.IsBoolean, booleans]

private def delayedBody (τ : Behavior (S × Bool)) : Prop :=
  (τ 0).2 = false ∧
    (∀ n, ((τ n).2 = true ∧ (τ (n + 1)).2 = false) ∨ (τ (n + 1)).1 x = (τ n).1 x) ∧
    ∃ n, (τ n).1 x = false

set_option maxRecDepth 4096 in
private theorem delayed_denotation (ops : DataOperations Bool) (σ : Behavior S) :
    (denotation ops delayed).Sat σ ↔ hide delayedBody σ := by
  change (Formula.existsFlex _).Sat σ ↔ _
  rw [Formula.sat_existsFlex]
  apply exists_congr
  intro τ
  apply and_congr_right
  intro _
  simp [Form.toFormulaIn, Form.junctionFormulaIn, Form.binaryFormula,
    Formula.Sat, Formula.Holds, Formula.holds_eventually, delayedBody,
    Predicate.actionIn, Predicate.evalIn, ScopedExpr.eval, Observation.evalIn, Term.eval,
    Action.bracket, Action.unchanged, Action.current, Action.prime,
    extendState, bool_and, Booleans.holds_ofProp, interp, x]
  rfl

private def visible : Behavior S := fun n _ => decide (n = 0)

private def delay : Retiming where
  index n := n - 1
  zero := rfl
  step n := by
    change (n + 1) - 1 = n - 1 ∨ (n + 1) - 1 = (n - 1) + 1
    omega
  cofinal n := ⟨n + 1, by omega⟩

private theorem admits_delayed_visible_step (ops : DataOperations Bool) :
    (denotation ops delayed).Sat visible := by
  apply (delayed_denotation ops visible).mpr
  let τ : Behavior (S × Bool) := fun n => (visible.retime delay n, decide (n = 1))
  refine ⟨τ, StutterEquiv.retime visible delay, rfl, ?_, ⟨2, rfl⟩⟩
  intro n
  by_cases h : n = 1
  · subst n
    exact Or.inl ⟨rfl, rfl⟩
  · right
    change decide ((n + 1) - 1 = 0) = decide (n - 1 = 0)
    simp only [show ((n + 1) - 1 = 0) ↔ n - 1 = 0 by omega]

-- The same unexpanded projection cannot supply the initial hidden-only step.
private theorem excludes_exact_projection (τ : Behavior (S × Bool))
    (h : τ.map Prod.fst = visible) : ¬ delayedBody τ := by
  intro ⟨initial, step, _⟩
  have x₀ : (τ 0).1 x = true := congrArg (fun s : Behavior S => s 0 x) h
  have x₁ : (τ 1).1 x = false := congrArg (fun s : Behavior S => s 1 x) h
  rcases step 0 with witness | unchanged
  · exact Bool.false_ne_true (initial.symm.trans witness.1)
  · exact Bool.false_ne_true (x₁.symm.trans (unchanged.trans x₀))

private theorem excludes_constant_projection (ops : DataOperations Bool) :
    ¬ (denotation ops delayed).Sat (fun _ _ => true) := by
  rw [delayed_denotation]
  rintro ⟨τ, ⟨r, t, he⟩, _, _, n, hn⟩
  obtain ⟨k, _, reached, _⟩ := t.crosses (i := 0) (j := n) (by rw [t.zero]; exact Nat.zero_le n)
  have same : true = (τ (t.index k)).1 x :=
    congrArg (fun s : Behavior S => s k x) he
  rw [reached, hn] at same
  exact Bool.false_ne_true same.symm

private noncomputable def changes : Form signature := by_elab emit "Changes"
private noncomputable def rigid : Form signature := by_elab emit "Rigid"
private noncomputable def dual : Form signature := by_elab emit "Dual"
private noncomputable def nested : Form signature := by_elab emit "Nested"
private noncomputable def mixed : Form signature := by_elab emit "Mixed"
private noncomputable def canChange : Form signature := by_elab emit "CanChange"

private theorem changing_witness (ops : DataOperations Bool) (σ : Behavior S) :
    (denotation ops changes).Sat σ := by
  change (Formula.existsFlex _).Sat σ
  rw [Formula.sat_existsFlex]
  let τ : Behavior (S × Bool) := fun n => (σ n, decide (n = 0))
  refine ⟨τ, StutterEquiv.refl σ, ?_⟩
  change (Formula.eventuallyAngle _ _).Holds τ 0
  rw [Formula.holds_eventuallyAngle]
  refine ⟨0, Nat.le_refl 0, ?_⟩
  simp [Predicate.actionIn, Predicate.evalIn, ScopedExpr.eval, Observation.evalIn, Term.eval,
    Action.angle, Action.unchanged, Action.current, Action.prime, extendState, interp, τ, booleans]

private theorem rigid_witness_cannot_change (ops : DataOperations Bool) (σ : Behavior S) :
    ¬ (denotation ops rigid).Sat σ := by
  change ¬ (Formula.existsRigid _).Holds σ 0
  rw [Formula.holds_existsRigid]
  rintro ⟨value, h⟩
  change (Formula.eventuallyAngle _ _).Holds σ 0 at h
  rw [Formula.holds_eventuallyAngle] at h
  obtain ⟨n, _, step⟩ := h
  simp [Predicate.actionIn, Predicate.evalIn, ScopedExpr.eval, Term.eval, Action.angle, interp, booleans] at step

private theorem universal_checks_every_extension (ops : DataOperations Bool) (σ : Behavior S) :
    ¬ (denotation ops dual).Sat σ := by
  change ¬ (Formula.forallFlex _).Sat σ
  rw [Formula.sat_forallFlex]
  intro all
  have h := all (fun n => (σ n, false)) (StutterEquiv.refl σ)
  simp [Form.toFormulaIn, Formula.Sat, Formula.Holds, Predicate.actionIn, Predicate.evalIn,
    ScopedExpr.eval, Term.eval, extendState, interp, booleans] at h

private theorem nested_binders (ops : DataOperations Bool) (σ : Behavior S) :
    (denotation ops nested).Sat σ := by
  change (Formula.forallFlex _).Sat σ
  rw [Formula.sat_forallFlex]
  intro τ _
  change (Formula.existsFlex _).Sat τ
  rw [Formula.sat_existsFlex]
  refine ⟨fun n => (τ n, !(τ n).2), StutterEquiv.refl τ, ?_⟩
  change (Formula.existsFlex _).Sat _
  rw [Formula.sat_existsFlex]
  refine ⟨fun n => ((τ n, !(τ n).2), !(τ n).2), StutterEquiv.refl _, ?_⟩
  simp [Form.toFormulaIn, Formula.Sat, Formula.Holds, Predicate.actionIn, Predicate.evalIn, ScopedExpr.eval,
    Term.eval, extendState, interp, booleans, Logic.eval, Logic.holds, Booleans.IsBoolean]

private theorem mixed_binders (ops : DataOperations Bool) (σ : Behavior S) :
    (denotation ops mixed).Sat σ := by
  change (Formula.existsRigid _).Holds σ 0
  rw [Formula.holds_existsRigid]
  refine ⟨false, ?_⟩
  change (Formula.existsFlex _).Sat σ
  rw [Formula.sat_existsFlex]
  refine ⟨fun n => (σ n, false), StutterEquiv.refl σ, ?_⟩
  simp [Form.toFormulaIn, Formula.Sat, Formula.Holds, Predicate.actionIn, Predicate.evalIn, ScopedExpr.eval,
    Term.eval, extendState, interp, withWitness, booleans]

private theorem enabled_hidden_successor (ops : DataOperations Bool) (σ : Behavior S) :
    (denotation ops canChange).Sat σ := by
  change (Formula.existsFlex _).Sat σ
  rw [Formula.sat_existsFlex]
  refine ⟨fun n => (σ n, false), StutterEquiv.refl σ, ?_⟩
  simp [Form.toFormulaIn, Formula.Sat, Formula.Holds, Predicate.actionIn, Predicate.evalIn, ScopedExpr.eval, Term.eval,
    Action.enabled, extendState, interp, booleans, Logic.eval, Logic.holds, Booleans.IsBoolean]

#print axioms admits_delayed_visible_step
#print axioms excludes_exact_projection
#print axioms excludes_constant_projection
#print axioms changing_witness
#print axioms rigid_witness_cannot_change
#print axioms universal_checks_every_extension
#print axioms nested_binders
#print axioms mixed_binders
#print axioms enabled_hidden_successor
#print axioms CheckedFormula.sat_stutterInvariant
#print axioms Formula.sat_existsFlex_iff_lamport_reduction

end Silmaril.Logic.Temporal.TLA.SourceAcceptance.Flexible
