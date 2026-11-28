module

public import Silmaril.Logic.Temporal.TLA.DataElab.Temporal.Thms
import Silmaril.Logic.Temporal.TLA.DataElab.Tagged.Thms
import Mathlib.Data.Nat.Find
import all Silmaril.Logic.Temporal.TLA.DataElab.Defs
meta import Silmaril.Logic.Temporal.TLA.DataElab.Temporal.Defs
meta import Silmaril.Logic.Temporal.TLA.DataElab.Tagged.Thms
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
public import Lean
public meta import Lean

namespace Silmaril.Logic.Temporal.TLA.SourceAcceptance.LiveHourClock

open DataElab DataElab.Temporal Resolution Data.Tagged
open DataElab.Tagged (Policy NumericPrimitive numericSignature)

private meta abbrev hr : BindingId := .declared ⟨"HourClock", [.unit 0, .member 0]⟩
private meta abbrev interval : BindingId := .declared ⟨"Naturals", [.member 0]⟩
private meta abbrev plus : BindingId := .declared ⟨"Naturals", [.member 1]⟩

private meta def numeric (id : BindingId) : Option NumericPrimitive :=
  if id = interval then some .interval else if id = plus then some .add else none

private meta abbrev signature := numericSignature numeric

private structure ClockForms where
  spec : Form signature
  tick : Form signature
  allTimes : Form signature
  inv : Form signature
  settles : Form signature

meta section

open Lean

private def load (dir : System.FilePath) (name : String) : IO Surface.Module := do
  let text ← IO.FS.readFile (dir / (name ++ ".tla"))
  match Surface.Parser.parseModule text with
  | .ok mod =>
    unless mod.name = name do throw (IO.userError s!"unexpected module name {mod.name}")
    return mod
  | .error e => throw (IO.userError s!"{name} parse: {reprStr e}")

private def attestInfix (source : Surface.Module) (index : Nat) (symbol : String) :
    Except String SignatureDecl := do
  let some (.definition (.operator .ordinary (.infix _ (.symbol actual) _) _)) :=
    source.units[index]? | throw s!"expected Naturals infix declaration at unit {index}"
  unless actual = symbol do throw s!"expected Naturals {symbol} at unit {index}"
  return .operator (.symbol .infix actual) [.expression, .expression]

private def checkedForms (live clock naturals tlce : Surface.Module) :
    Except String ClockForms := do
  -- Check the actual anonymous statement before proving the same entailment
  -- from its independently selected definitions.
  let [.theoremDecl ⟨none, .expr
    (.infix (.symbol "=>") (.ref (.operator (.ident "LSpec")) [] [])
      (.infix (.symbol "/\\")
        (.infix (.symbol "/\\") (.ref (.operator (.ident "AlwaysTick")) [] [])
          (.ref (.operator (.ident "AllTimes")) [] []))
        (.ref (.operator (.ident "TypeInvariance")) [] []))), none⟩] :=
    live.units.filter (fun | .theoremDecl _ => true | _ => false)
    | throw "unexpected LiveHourClock anonymous theorem"
  let rangeDecl ← attestInfix naturals 11 ".."
  let plusDecl ← attestInfix naturals 1 "+"
  unless tlce.units.any fun unit =>
      match unit with
      | .definition (.operator .ordinary (.ident "CounterExample" []) _) => true
      | _ => false
    do throw "missing nullary TLCExt.CounterExample"
  let registry ← (resolveWith .levelSyntax
    [("LiveHourClock", .parsed live [("HourClock", "HourClock"), ("TLC", "TLC"), ("TLCExt", "TLCExt")]),
     ("HourClock", .parsed clock [("Naturals", "Naturals")]),
     ("Naturals", .signature "Naturals" [] [rangeDecl, plusDecl]),
     ("TLC", .signature "TLC" [] []),
     ("TLCExt", .signature "TLCExt" [] [.operator (.ident "CounterExample") []])]
    "LiveHourClock").mapError (fun e => s!"resolution: {reprStr e}")
  let binary : Levels.ExternalSignature := ⟨.constant, [⟨.action, true⟩, ⟨.action, true⟩]⟩
  let levels : Levels.ExternalLevels :=
    [(interval, binary), (plus, binary),
      (.declared ⟨"TLCExt", [.member 0]⟩, ⟨.constant, []⟩)]
  let some root := registry.moduleAt "LiveHourClock" | throw "missing resolved root"
  let select := fun name => do
    let some binding := root.bindingAt (.ident name) | throw s!"missing {name}"
    pure (Temporal.lowerFormula registry levels signature 32 binding.id)
  let accept := fun name => do
    let form ← (← select name).mapError (fun e => s!"{name} lowering: {reprStr e}")
    return form.form
  let .error (.data diagnostic) ← select "PostCondition"
    | throw "expected the TLC postcondition to be unsupported"
  unless diagnostic.kind = .missingPrimitive (.declared ⟨"TLCExt", [.member 0]⟩) do
    throw s!"unexpected PostCondition rejection: {reprStr diagnostic}"
  return ⟨← accept "LSpec", ← accept "AlwaysTick", ← accept "AllTimes",
    ← accept "TypeInvariance", ← accept "ClockSettles"⟩

deriving instance ToExpr for Resolution.Fixity
deriving instance ToExpr for Resolution.Name
deriving instance ToExpr for Step
deriving instance ToExpr for Site
deriving instance ToExpr for BindingId

/-- Quote the emitted syntax for the fixture so the kernel checks its denotation. -/
private partial def quoteData (term : DataElab.Term signature) : Elab.Term.TermElabM Lean.Expr := do
  let core := fun ctor => mkApp2 (mkConst ctor) (mkConst ``signature) (mkConst ``Fragment.core)
  let node := fun ctor fields => mkAppN (core ctor) fields
  match term with
  | .flexible id => return node ``DataElab.Term.flexible #[toExpr id]
  | .witness slot => return node ``DataElab.Term.witness #[toExpr slot]
  | .numeral n => return node ``DataElab.Term.numeral #[toExpr n]
  | .prime site operand => return node ``DataElab.Term.prime #[toExpr site, ← quoteData operand]
  | .eq neg l r => return node ``DataElab.Term.eq #[toExpr neg, ← quoteData l, ← quoteData r]
  | .mem neg x s => return node ``DataElab.Term.mem #[toExpr neg, ← quoteData x, ← quoteData s]
  | .ite c y n => return node ``DataElab.Term.ite #[← quoteData c, ← quoteData y, ← quoteData n]
  | .external id arity _ args =>
    let key := toExpr id
    let expected ← Meta.mkEq (mkApp (mkConst ``signature) key) (toExpr (some arity))
    let admitted ← Elab.Term.elabTerm (← `(by
      simp [signature, numericSignature, numeric, interval, plus, NumericPrimitive.arity])) (some expected)
    let values ← Meta.mkListLit (core ``DataElab.Term) (← args.mapM quoteData)
    return node ``DataElab.Term.external #[key, toExpr arity, admitted, values]
  | _ => throwError "unexpected clock data term: {reprStr term}"

private def quoteChecked (e : ScopedExpr signature) : Elab.Term.TermElabM Lean.Expr := do
  Meta.mkAppM ``ScopedExpr.mk #[← quoteData e.term, toExpr e.slots, ← Meta.mkEqRefl (toExpr true)]

private def quotePred : Predicate signature → Elab.Term.TermElabM Lean.Expr
  | .data e => do Meta.mkAppM ``Predicate.data #[← quoteChecked e]
  | _ => throwError "expected a data predicate leaf"

private def quoteObs (obs : Observation signature) : Elab.Term.TermElabM Lean.Expr := do
  let type := mkApp2 (mkConst ``ScopedExpr) (mkConst ``signature) (mkConst ``Fragment.core)
  Meta.mkListLit type (← obs.mapM quoteChecked)

private def quoteForm : Form signature → Elab.Term.TermElabM Lean.Expr
  | .state p => do Meta.mkAppM ``Form.state #[← quotePred p]
  | .binary .and p q => do
    Meta.mkAppM ``Form.binary #[mkConst ``Logic.and, ← quoteForm p, ← quoteForm q]
  | .rigidQuant kind slot (some bound) p => do
    let quantifier := match kind with
      | .forall => mkConst ``Surface.Quantifier.forall
      | .exists => mkConst ``Surface.Quantifier.exists
    let range ← Meta.mkAppM ``Option.some #[← quoteChecked bound]
    Meta.mkAppM ``Form.rigidQuant #[quantifier, toExpr slot, range, ← quoteForm p]
  | .always p => do Meta.mkAppM ``Form.always #[← quoteForm p]
  | .eventually p => do Meta.mkAppM ``Form.eventually #[← quoteForm p]
  | .alwaysBracket p obs => do Meta.mkAppM ``Form.alwaysBracket #[← quotePred p, ← quoteObs obs]
  | .eventuallyAngle p obs => do Meta.mkAppM ``Form.eventuallyAngle #[← quotePred p, ← quoteObs obs]
  | .fairness .weak p obs => do
    Meta.mkAppM ``Form.fairness #[mkConst ``Surface.Fairness.weak, ← quotePred p, ← quoteObs obs]
  | _ => throwError "unexpected temporal clock form"

private def emitForms : Elab.Term.TermElabM Lean.Expr := do
  let some path ← IO.getEnv "SILMARIL_TLA_LIVE_CLOCK_FIXTURES"
    | throwError "stage the clock fixtures with tla-temporal-source/check.py"
  let dir := System.FilePath.mk path
  let forms := checkedForms (← load dir "LiveHourClock") (← load dir "HourClock")
    (← load dir "Naturals") (← load dir "TLCExt")
  let forms ← match forms with
    | .ok result => pure result
    | .error message => throwError "{message}"
  Meta.mkAppM ``ClockForms.mk #[← quoteForm forms.spec, ← quoteForm forms.tick,
    ← quoteForm forms.allTimes, ← quoteForm forms.inv, ← quoteForm forms.settles]

end

private noncomputable def selected : ClockForms := by_elab emitForms

private abbrev ClockValue := Value.{0}
private abbrev ClockState := State ClockValue

private noncomputable def interp (policy : Policy.{0}) : Interpretation ClockValue signature :=
  ⟨policy.operations, policy.booleans, policy.external numeric⟩

private noncomputable def initial (I : Interpretation ClockValue signature) (ρ : RigidEnv ClockValue) :
    StatePred ClockState :=
  match selected.inv with
  | .always (.state p) => p.toStatePred I ρ
  | _ => fun _ => False

private noncomputable def next (I : Interpretation ClockValue signature) (ρ : RigidEnv ClockValue) :
    Action ClockState :=
  match selected.tick with
  | .always (.eventuallyAngle p _) => p.toAction I ρ
  | _ => fun _ _ => False

private noncomputable def hour (s : ClockState) : ClockValue := s hr
private noncomputable def observedHour (s : ClockState) : List ClockValue := [hour s]

private noncomputable def clockRange (I : Interpretation ClockValue signature) (ρ : RigidEnv ClockValue)
    (value : ClockValue) : StatePred ClockState :=
  fun s => match selected.allTimes with
    | .rigidQuant _ _ (some bound) _ => I.data.mem value (bound.eval I ρ (fun _ => I.data.enum []) s s)
    | _ => False

private noncomputable def isHour (I : Interpretation ClockValue signature) (value : ClockValue) :
    StatePred ClockState :=
  fun s => I.booleans.holds (I.booleans.ofProp (hour s = value))

private theorem initial_iff (policy : Policy.{0}) (ρ : RigidEnv ClockValue) (s : ClockState) :
    initial (interp policy) ρ s ↔ ∃ n : Int, hour s = Value.integer n ∧ 1 ≤ n ∧ n ≤ 12 := by
  simp only [initial, selected, interp, Predicate.toStatePred, Predicate.toAction, Predicate.actionWith,
    Predicate.actionIn, Predicate.evalIn, id, ScopedExpr.eval,
    DataElab.Term.eval, DataElab.Term.evalList, Bool.false_eq_true, ite_false,
    Booleans.holds_ofProp, policy.numeral_eq, policy.mem_value, hour]
  rw [policy.external_apply numeric (show numeric interval = some .interval by simp [numeric])]
  simp only [policy.interval_apply, Value.interval_integer, Value.mem_set, SetData.mem_intRange, eq_comm]
  rfl

private theorem clockRange_iff (policy : Policy.{0}) (ρ : RigidEnv ClockValue)
    (value : ClockValue) (s : ClockState) :
    clockRange (interp policy) ρ value s ↔ ∃ n : Int, value = Value.integer n ∧ 1 ≤ n ∧ n ≤ 12 := by
  simp only [clockRange, selected, interp, ScopedExpr.eval, DataElab.Term.eval,
    DataElab.Term.evalList, policy.numeral_eq, policy.mem_value]
  rw [policy.external_apply numeric (show numeric interval = some .interval by simp [numeric])]
  simp only [policy.interval_apply, Value.interval_integer, Value.mem_set, SetData.mem_intRange, eq_comm]
  rfl

open Classical in
private theorem next_integer_iff (policy : Policy.{0}) (ρ : RigidEnv ClockValue) (s t : ClockState)
    (n : Int) (h : hour s = Value.integer n) :
    next (interp policy) ρ s t ↔ hour t = Value.integer (if n = 12 then 1 else n + 1) := by
  have guard (p : Prop) : policy.booleans.IsBoolean (policy.booleans.ofProp p) := by
    by_cases hp : p <;> simp [Booleans.IsBoolean, hp]
  simp only [next, selected, interp, Predicate.toAction, Predicate.actionWith, Predicate.actionIn,
    Predicate.evalIn, id,
    ScopedExpr.eval, DataElab.Term.eval,
    DataElab.Term.evalList, Bool.false_eq_true, ite_false, ite_true,
    policy.numeral_eq, guard, Booleans.holds_ofProp, hour] at *
  rw [policy.external_apply numeric (show numeric plus = some .add by simp [numeric, interval, plus]), h]
  by_cases hn : n = 12 <;> simp [hn, policy.add_apply, Value.integer_injective.eq_iff]

private theorem spec_shape (I : Interpretation ClockValue signature) (ρ : RigidEnv ClockValue) :
    selected.spec.toFormula I ρ =
      .conj (.conj (.state (initial I ρ)) (.alwaysBracket (next I ρ) observedHour))
        (.weakFair (next I ρ) observedHour) := rfl

private theorem tick_shape (I : Interpretation ClockValue signature) (ρ : RigidEnv ClockValue) :
    selected.tick.toFormula I ρ = .always (.eventuallyAngle (next I ρ) observedHour) := rfl

private theorem invariant_shape (I : Interpretation ClockValue signature) (ρ : RigidEnv ClockValue) :
    selected.inv.toFormula I ρ = .always (.state (initial I ρ)) := rfl

private theorem allTimes_shape (I : Interpretation ClockValue signature) (ρ : RigidEnv ClockValue) :
    selected.allTimes.toFormula I ρ = .forallRigid (fun value =>
      (Formula.state (clockRange I ρ value)).imp (.always (Formula.state (isHour I value)).eventually)) :=
  rfl

private theorem settles_shape (I : Interpretation ClockValue signature) (ρ : RigidEnv ClockValue) :
    selected.settles.toFormula I ρ = .existsRigid (fun value =>
      .conj (.state (clockRange I ρ value)) (Formula.always (.state (isHour I value))).eventually) :=
  rfl

private theorem preserves (policy : Policy.{0}) (ρ : RigidEnv ClockValue) (s t : ClockState)
    (hs : initial (interp policy) ρ s) (hst : Action.bracket (next (interp policy) ρ) observedHour s t) :
    initial (interp policy) ρ t := by
  obtain ⟨n, hn, hlo, hhi⟩ := (initial_iff policy ρ s).mp hs
  apply (initial_iff policy ρ t).mpr
  rcases hst with step | idle
  · have ht := (next_integer_iff policy ρ s t n hn).mp step
    refine ⟨_, ht, ?_, ?_⟩ <;> split <;> omega
  · have ht : hour t = hour s := (List.singleton_inj.mp idle)
    exact ⟨n, ht.trans hn, hlo, hhi⟩

private theorem tick_enabled (policy : Policy.{0}) (ρ : RigidEnv ClockValue) (s : ClockState)
    (hs : initial (interp policy) ρ s) : ((next (interp policy) ρ).angle observedHour).enabled s := by
  obtain ⟨n, hn, _, _⟩ := (initial_iff policy ρ s).mp hs
  let m := if n = 12 then 1 else n + 1
  let t : ClockState := fun id => if id = hr then Value.integer m else s id
  have ht : hour t = Value.integer m := by simp [hour, t]
  refine ⟨t, (next_integer_iff policy ρ s t n hn).mpr ht, ?_⟩
  intro h
  have eq := Value.integer_injective (ht.symm.trans ((List.singleton_inj.mp h).trans hn))
  dsimp [m] at eq
  split at eq <;> omega

private def distance (goal current : Int) : Nat :=
  (if current ≤ goal then goal - current else 12 + goal - current).toNat

private theorem distance_decreases (goal current : Int)
    (lo : 1 ≤ current) (hi : current ≤ 12) (goalLo : 1 ≤ goal) (goalHi : goal ≤ 12)
    (different : current ≠ goal) :
    distance goal (if current = 12 then 1 else current + 1) < distance goal current := by
  by_cases wrap : current = 12 <;> simp only [wrap, ite_true, ite_false, distance] <;>
    split <;> split <;> omega

/-- Stutters preserve the distance to a chosen hour. Each changing step before
that hour strictly decreases it, so even a suffix with arbitrarily long idle
periods must reach the hour if changing steps recur. -/
private theorem visits (current : Nat → Int) (inRange : ∀ j, 1 ≤ current j ∧ current j ≤ 12)
    (step : ∀ j, current (j + 1) = current j ∨
      current (j + 1) = (if current j = 12 then 1 else current j + 1))
    (ticks : ∀ i, ∃ j, i ≤ j ∧ current (j + 1) ≠ current j)
    (goal : Int) (lo : 1 ≤ goal) (hi : goal ≤ 12) (i : Nat) :
    ∃ j, i ≤ j ∧ current j = goal := by
  classical
  by_contra absent
  let dist := distance goal ∘ current
  have decreases (j : Nat) (hij : i ≤ j) (tick : current (j + 1) ≠ current j) :
      dist (j + 1) < dist j := by
    change distance goal (current (j + 1)) < distance goal (current j)
    rw [(step j).resolve_left tick]
    exact distance_decreases _ _ (inRange j).1 (inRange j).2 lo hi (fun eq => absent ⟨j, hij, eq⟩)
  have monotoneTail (j : Nat) (hij : i ≤ j) (gap : Nat) : dist (j + gap) ≤ dist j := by
    induction gap with
    | zero => exact Nat.le_refl _
    | succ gap ih =>
      apply Nat.le_trans ?_ ih
      by_cases idle : current (j + gap + 1) = current (j + gap)
      · exact Nat.le_of_eq (congrArg (distance goal) idle)
      · exact Nat.le_of_lt (decreases _ (hij.trans (Nat.le_add_right j gap)) idle)
  let seen := fun d => ∃ j, i ≤ j ∧ dist j = d
  have someDistance : ∃ d, seen d := ⟨dist i, i, Nat.le_refl i, rfl⟩
  obtain ⟨j, hij, hj⟩ := Nat.find_spec someDistance
  obtain ⟨k, hjk, tick⟩ := ticks j
  have diff : j + (k - j) = k := by omega
  have le : dist k ≤ dist j := diff ▸ monotoneTail j hij (k - j)
  have minimum := Nat.find_min' someDistance (show seen (dist (k + 1)) from ⟨k + 1, by omega, rfl⟩)
  have lt := decreases k (by omega) tick
  omega

/-- The denotation of the intact anonymous LiveHourClock theorem under every
tagged adapter policy. -/
private theorem live_hour_clock (policy : Policy.{0}) (ρ : RigidEnv ClockValue) :
    (selected.spec.toFormula (interp policy) ρ).Entails
      (.conj (.conj (selected.tick.toFormula (interp policy) ρ) (selected.allTimes.toFormula (interp policy) ρ))
        (selected.inv.toFormula (interp policy) ρ)) := by
  intro σ h
  rw [spec_shape] at h
  have hInit : initial (interp policy) ρ (σ 0) := h.1.1
  have step : ∀ i, (next (interp policy) ρ).bracket observedHour (σ i) (σ (i + 1)) :=
    fun i => h.1.2 i (Nat.zero_le i)
  have invariant (i : Nat) : initial (interp policy) ρ (σ i) := by
    induction i with
    | zero => exact hInit
    | succ i ih => exact preserves policy ρ _ _ ih (step i)
  have recurring := (Formula.holds_weakFair _ _ σ 0).mp h.2
    ⟨0, Nat.le_refl _, fun j _ => tick_enabled policy ρ _ (invariant j)⟩
  rw [tick_shape, allTimes_shape, invariant_shape]
  refine ⟨⟨?_, ?_⟩, fun i _ => invariant i⟩
  · intro i hi
    exact (Formula.holds_eventuallyAngle _ _ σ i).mpr (recurring i hi)
  apply (Formula.holds_forallRigid _ σ 0).mpr
  intro value
  apply (Formula.holds_imp _ _ σ 0).mpr
  intro inDomain
  obtain ⟨goal, rfl, lo, hi⟩ := (clockRange_iff policy ρ value (σ 0)).mp inDomain
  classical
  let valid := fun j => (initial_iff policy ρ (σ j)).mp (invariant j)
  let current := fun j => (valid j).choose
  have tagged (j : Nat) : hour (σ j) = .integer (current j) := (valid j).choose_spec.1
  have range (j : Nat) : 1 ≤ current j ∧ current j ≤ 12 := (valid j).choose_spec.2
  have stepHour (j : Nat) : current (j + 1) = current j ∨
      current (j + 1) = (if current j = 12 then 1 else current j + 1) := by
    rcases step j with advance | idle
    · exact Or.inr (Value.integer_injective ((tagged _).symm.trans
        ((next_integer_iff policy ρ _ _ _ (tagged j)).mp advance)))
    · exact Or.inl (Value.integer_injective
        ((tagged _).symm.trans ((List.singleton_inj.mp idle).trans (tagged _))))
  have tickHour (i : Nat) : ∃ j, i ≤ j ∧ current (j + 1) ≠ current j := by
    obtain ⟨j, hij, _, changed⟩ := recurring i (Nat.zero_le i)
    refine ⟨j, hij, fun eq => changed ?_⟩
    change [hour (σ (j + 1))] = [hour (σ j)]
    rw [tagged, tagged, eq]
  intro i _
  apply (Formula.holds_eventually _ σ i).mpr
  obtain ⟨j, hij, hj⟩ := visits current range stepHour tickHour goal lo hi i
  exact ⟨j, hij, (policy.booleans.holds_ofProp _).mpr ((tagged j).trans (congrArg Value.integer hj))⟩

private theorem lspec_excludes_clock_settles (policy : Policy.{0}) (ρ : RigidEnv ClockValue)
    (σ : Behavior ClockState) (h : (selected.spec.toFormula (interp policy) ρ).Sat σ) :
    ¬ (selected.settles.toFormula (interp policy) ρ).Sat σ := by
  rw [settles_shape]
  rintro ⟨value, _, steady⟩
  obtain ⟨i, hi, stable⟩ := (Formula.holds_eventually _ σ 0).mp steady
  have tick := (live_hour_clock policy ρ σ h).1.1
  rw [tick_shape] at tick
  obtain ⟨j, hj, _, changed⟩ := (Formula.holds_eventuallyAngle _ _ σ i).mp (tick i hi)
  have atJ : hour (σ j) = value := (policy.booleans.holds_ofProp _).mp (stable j hj)
  have afterJ : hour (σ (j + 1)) = value :=
    (policy.booleans.holds_ofProp _).mp (stable (j + 1) (by omega))
  exact changed (congrArg List.singleton (afterJ.trans atJ.symm))

#print axioms live_hour_clock
#print axioms lspec_excludes_clock_settles

end Silmaril.Logic.Temporal.TLA.SourceAcceptance.LiveHourClock
