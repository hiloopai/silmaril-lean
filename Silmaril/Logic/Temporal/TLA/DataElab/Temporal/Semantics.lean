module

public import Silmaril.Logic.Temporal.TLA.DataElab.Defs
public import Silmaril.Logic.Temporal.TLA.Defs

/-! Denotations for the temporal fragment of named data expressions. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.Temporal

open Resolution

@[expose] public section

universe u

/-- Every flexible declaration can take any value in the interpretation. -/
abbrev State (V : Type u) := BindingId → V
abbrev RigidEnv (V : Type u) := BindingId → V

/-- Fix these operations and primitive interpretations throughout a behavior. -/
structure Interpretation (V : Type u) (signature : ExternalSignature) (fragment : Fragment := .core) where
  data : Operations V fragment
  booleans : Booleans V
  external : ExternalInterpretation V signature

variable {V S : Type u} {signature : ExternalSignature} {fragment : Fragment}

abbrev Witnesses (V : Type u) := Nat → V

/-- A data leaf checked against the enclosing temporal witness slots. -/
structure ScopedExpr (signature : ExternalSignature) (fragment : Fragment := .core) where
  term : Term signature fragment
  slots : List Nat
  wellFormed : term.isWellFormed slots = true

noncomputable def ScopedExpr.eval (e : ScopedExpr signature fragment) (I : Interpretation V signature fragment)
    (ρ : RigidEnv V) (witnesses : Witnesses V) (s t : State V) : V :=
  e.term.eval I.data I.booleans I.external ⟨ρ, s⟩ witnesses t

/-- A scalar or tuple of state expressions used only for observation equality. -/
abbrev Observation (signature : ExternalSignature) (fragment : Fragment := .core) := List (ScopedExpr signature fragment)

noncomputable def Observation.evalIn (observation : Observation signature fragment)
    (I : Interpretation V signature fragment) (ρ : RigidEnv V) (witnesses : Witnesses V)
    (read : S → State V) : StateExpr S (List V) :=
  fun s => observation.map fun e => e.eval I ρ witnesses (read s) (read s)

noncomputable def Observation.evalWith (observation : Observation signature fragment)
    (I : Interpretation V signature fragment) (ρ : RigidEnv V) (witnesses : Witnesses V) :
    StateExpr (State V) (List V) :=
  observation.evalIn I ρ witnesses id

noncomputable def Observation.eval (observation : Observation signature fragment)
    (I : Interpretation V signature fragment) (ρ : RigidEnv V) : StateExpr (State V) (List V) :=
  observation.evalWith I ρ (fun _ => (Operations.base (fragment := fragment) I.data).enum [])

/-- Values of predicates in state and step positions. Source atoms use the
existing data interpretation, and action operators reify propositions. -/
inductive Predicate (signature : ExternalSignature) (fragment : Fragment := .core) where
  | data (expression : ScopedExpr signature fragment)
  | neg (p : Predicate signature fragment)
  | binary (op : Logic) (p q : Predicate signature fragment)
  | junction (kind : Surface.Junction) (items : List (Predicate signature fragment))
  | unchanged (obs : Observation signature fragment)
  | bracket (kind : Surface.ActionBracket) (p : Predicate signature fragment) (obs : Observation signature fragment)
  | enabled (p : Predicate signature fragment)

open Classical in
mutual

noncomputable def Predicate.evalIn (I : Interpretation V signature fragment) (ρ : RigidEnv V)
    (witnesses : Witnesses V) (read : S → State V)
    (p : Predicate signature fragment) (s t : S) : V :=
  let B := I.booleans
  match p with
  | .data e => e.eval I ρ witnesses (read s) (read t)
  | .neg p =>
    let value := p.evalIn I ρ witnesses read s t
    if B.IsBoolean value then B.ofProp (¬B.holds value) else B.invalid .negation [value]
  | .binary op p q => op.eval B (p.evalIn I ρ witnesses read s t) (q.evalIn I ρ witnesses read s t)
  | .junction kind items =>
    let values := Predicate.evalListIn I ρ witnesses read items s t
    let (absorbing, identity) := match kind with
      | .conjunction => (B.falseValue, B.trueValue)
      | .disjunction => (B.trueValue, B.falseValue)
    if absorbing ∈ values then absorbing
    else if ∀ value ∈ values, B.IsBoolean value then identity
    else B.invalid (.junction kind) values
  | .unchanged obs => B.ofProp (Action.unchanged (obs.evalIn I ρ witnesses read) s t)
  | .bracket kind p obs =>
    let A : Action S := fun source target => B.holds (p.evalIn I ρ witnesses read source target)
    let f := obs.evalIn I ρ witnesses read
    B.ofProp (match kind with
      | .square => A.bracket f s t
      | .angle => A.angle f s t)
  | .enabled p => B.ofProp (Action.enabled (fun source target => B.holds (p.evalIn I ρ witnesses read source target)) s)
termination_by structural p

noncomputable def Predicate.evalListIn (I : Interpretation V signature fragment) (ρ : RigidEnv V)
    (witnesses : Witnesses V) (read : S → State V)
    (items : List (Predicate signature fragment)) (s t : S) : List V :=
  match items with
  | [] => []
  | p :: rest => p.evalIn I ρ witnesses read s t :: Predicate.evalListIn I ρ witnesses read rest s t
termination_by structural items

end

noncomputable def Predicate.evalList (I : Interpretation V signature fragment) (ρ : RigidEnv V)
    (witnesses : Witnesses V) (items : List (Predicate signature fragment)) (s t : State V) : List V :=
  Predicate.evalListIn I ρ witnesses id items s t

noncomputable def Predicate.evalWith (I : Interpretation V signature fragment) (ρ : RigidEnv V)
    (witnesses : Witnesses V) (p : Predicate signature fragment) (s t : State V) : V :=
  p.evalIn I ρ witnesses id s t

noncomputable def Predicate.eval (I : Interpretation V signature fragment) (ρ : RigidEnv V)
    (p : Predicate signature fragment) (s t : State V) : V :=
  p.evalWith I ρ (fun _ => (Operations.base (fragment := fragment) I.data).enum []) s t

noncomputable def Predicate.actionIn (p : Predicate signature fragment) (I : Interpretation V signature fragment)
    (ρ : RigidEnv V) (witnesses : Witnesses V) (read : S → State V) : Action S :=
  fun s t => I.booleans.holds (p.evalIn I ρ witnesses read s t)

noncomputable def Predicate.actionWith (p : Predicate signature fragment) (I : Interpretation V signature fragment)
    (ρ : RigidEnv V) (witnesses : Witnesses V) : Action (State V) :=
  p.actionIn I ρ witnesses id

noncomputable def Predicate.toAction (p : Predicate signature fragment) (I : Interpretation V signature fragment)
    (ρ : RigidEnv V) : Action (State V) :=
  p.actionWith I ρ (fun _ => (Operations.base (fragment := fragment) I.data).enum [])

noncomputable def Predicate.toStatePred (p : Predicate signature fragment) (I : Interpretation V signature fragment)
    (ρ : RigidEnv V) : StatePred (State V) :=
  fun s => p.toAction I ρ s s

/-- Only a square or angle modality can turn a step predicate into a formula.
Fairness applies to the changing steps of the given action and observation. -/
inductive Form (signature : ExternalSignature) (fragment : Fragment := .core) where
  | state (p : Predicate signature fragment)
  | neg (p : Form signature fragment)
  | binary (op : Logic) (p q : Form signature fragment)
  | junction (kind : Surface.Junction) (items : List (Form signature fragment))
  | rigidQuant (kind : Surface.Quantifier) (slot : Nat) (bound : Option (ScopedExpr signature fragment))
      (body : Form signature fragment)
  | flexQuant (kind : Surface.Quantifier) (binder : BindingId) (body : Form signature fragment)
  | always (p : Form signature fragment)
  | eventually (p : Form signature fragment)
  | leadsTo (p q : Form signature fragment)
  | alwaysBracket (p : Predicate signature fragment) (obs : Observation signature fragment)
  | eventuallyAngle (p : Predicate signature fragment) (obs : Observation signature fragment)
  | fairness (kind : Surface.Fairness) (p : Predicate signature fragment) (obs : Observation signature fragment)

def Form.binaryFormula {S : Type u} (op : Logic) (p q : Formula S) : Formula S :=
  match op with
  | .and => .conj p q
  | .or => p.disj q
  | .implies => p.imp q
  | .equiv => .conj (p.imp q) (q.imp p)

/-- The new coordinate supplies the bound name at the current endpoint. -/
def extendState (read : S → State V) (binder : BindingId) (s : S × V) : State V :=
  fun id => if id = binder then s.2 else read s.1 id

mutual

/-- Interpret a formula in a state space with all its enclosing flexible coordinates. -/
noncomputable def Form.toFormulaIn {S : Type u} (form : Form signature fragment) (I : Interpretation V signature fragment)
    (ρ : RigidEnv V) (witnesses : Witnesses V) (read : S → State V) : Formula S :=
  match form with
  | .state p => .state (fun s => p.actionIn I ρ witnesses read s s)
  | .neg p => .neg (p.toFormulaIn I ρ witnesses read)
  | .binary op p q => Form.binaryFormula op (p.toFormulaIn I ρ witnesses read) (q.toFormulaIn I ρ witnesses read)
  | .junction kind items => Form.junctionFormulaIn kind items I ρ witnesses read
  | .rigidQuant kind slot bound body =>
    let instantiate := fun value => body.toFormulaIn I ρ (withWitness witnesses slot value) read
    let guard := fun (e : ScopedExpr signature fragment) value =>
      Formula.state fun s => (Operations.base (fragment := fragment) I.data).mem value (e.eval I ρ witnesses (read s) (read s))
    match kind, bound with
    | .exists, none => .existsRigid instantiate
    | .forall, none => .forallRigid instantiate
    | .exists, some e => .existsRigid fun value => .conj (guard e value) (instantiate value)
    | .forall, some e => .forallRigid fun value => (guard e value).imp (instantiate value)
  | .flexQuant kind binder body =>
    let inner := body.toFormulaIn (S := S × V) I ρ witnesses (extendState read binder)
    match kind with
    | .exists => .existsFlex inner
    | .forall => .forallFlex inner
  | .always p => .always (p.toFormulaIn I ρ witnesses read)
  | .eventually p => (p.toFormulaIn I ρ witnesses read).eventually
  | .leadsTo p q => (p.toFormulaIn I ρ witnesses read).leadsTo (q.toFormulaIn I ρ witnesses read)
  | .alwaysBracket p obs => .alwaysBracket (p.actionIn I ρ witnesses read) (obs.evalIn I ρ witnesses read)
  | .eventuallyAngle p obs => .eventuallyAngle (p.actionIn I ρ witnesses read) (obs.evalIn I ρ witnesses read)
  | .fairness .weak p obs => .weakFair (p.actionIn I ρ witnesses read) (obs.evalIn I ρ witnesses read)
  | .fairness .strong p obs => .strongFair (p.actionIn I ρ witnesses read) (obs.evalIn I ρ witnesses read)
termination_by structural form

noncomputable def Form.junctionFormulaIn {S : Type u} (kind : Surface.Junction) (items : List (Form signature fragment))
    (I : Interpretation V signature fragment) (ρ : RigidEnv V) (witnesses : Witnesses V) (read : S → State V) : Formula S :=
  match items with
  | [] => .state fun _ => match kind with | .conjunction => True | .disjunction => False
  | p :: rest =>
    let op := match kind with | .conjunction => Logic.and | .disjunction => .or
    Form.binaryFormula op (p.toFormulaIn I ρ witnesses read) (Form.junctionFormulaIn kind rest I ρ witnesses read)
termination_by structural items

end

noncomputable def Form.junctionFormula (kind : Surface.Junction) (items : List (Form signature fragment))
    (I : Interpretation V signature fragment) (ρ : RigidEnv V) (witnesses : Witnesses V) : Formula (State V) :=
  Form.junctionFormulaIn kind items I ρ witnesses id

noncomputable def Form.toFormulaWith (form : Form signature fragment) (I : Interpretation V signature fragment)
    (ρ : RigidEnv V) (witnesses : Witnesses V) : Formula (State V) :=
  form.toFormulaIn I ρ witnesses id

noncomputable def Form.toFormula (form : Form signature fragment) (I : Interpretation V signature fragment)
    (ρ : RigidEnv V) : Formula (State V) :=
  form.toFormulaWith I ρ (fun _ => (Operations.base (fragment := fragment) I.data).enum [])

end
end Silmaril.Logic.Temporal.TLA.DataElab.Temporal
