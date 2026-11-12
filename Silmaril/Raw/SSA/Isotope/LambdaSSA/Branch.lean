module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.InstructionMap
public import Silmaril.SSA.Isotope.LambdaSSA.Thms

/-! # Adding a scalar branch to an arbitrary SSA signature

The extension retains the original value types, state and primitive transitions.
The extra test has no state effect and returns one of the two unit injections.
Its input representation and truth test are parameters; determinism requires
that the representation is injective. No primitive effect is weakened.
-/

@[expose] public section
universe u v a b s e
namespace Silmaril.Isotope.LambdaSSA.Branch

inductive Instruction (Φ : Type u) {τ : Type v} (testType : τ) where
  | primitive (instruction : Φ)
  | test

variable {Φ : Type u} {τ : Type v} {testType : τ}

instance [TypeFormers τ] [HasTy Φ τ] : HasTy (Instruction Φ testType) τ where
  src
    | .primitive i => instrSrc i
    | .test => testType
  trg
    | .primitive i => instrTrg i
    | .test => TypeFormers.coprod TypeFormers.unit TypeFormers.unit

instance {ε : Type e} [HasEff Φ ε] : HasEff (Instruction Φ testType) (Option ε) where
  eff
    | .primitive i => some (instrEff i)
    | .test => none

instance {ε : Type e} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] :
    Signature (Instruction Φ testType) τ (Option ε) where

def embed (term : Tm Φ) : Tm (Instruction Φ testType) := term.mapInstr .primitive
def embedRegion (region : Region Φ) : Region (Instruction Φ testType) := region.mapInstr .primitive
def test (predicate : Tm (Instruction Φ testType)) : Tm (Instruction Φ testType) := .op .test predicate

theorem embed_typed [TypeFormers τ] [HasTy Φ τ] {Γ : VCtx τ} {term : Tm Φ} {type : τ}
    (typed : Tm.HasType Γ term type) : Tm.HasType Γ (embed (testType := testType) term) type :=
  typed.mapInstr Instruction.primitive ⟨fun _ => rfl, fun _ => rfl⟩

theorem embedRegion_typed [TypeFormers τ] [HasTy Φ τ] {Γ : VCtx τ} {region : Region Φ} {labels : LCtx τ}
    (typed : Region.HasType Γ region labels) : Region.HasType Γ (embedRegion (testType := testType) region) labels :=
  typed.mapInstr Instruction.primitive ⟨fun _ => rfl, fun _ => rfl⟩

theorem test_typed [TypeFormers τ] [HasTy Φ τ] {Γ : VCtx τ} {predicate : Tm (Instruction Φ testType)}
    (typed : Tm.HasType Γ predicate testType) :
    Tm.HasType Γ (test predicate) (TypeFormers.coprod TypeFormers.unit TypeFormers.unit) := .op typed

def result {α : Type a} (truth : Bool) : Value α := if truth then .inl .unit else .inr .unit

variable {α : Type a} {β : Type b} {σ : Type s}

inductive Step (instr : Φ → Value α → σ → Value α → σ → Prop)
    (input : β → Value α) (truth : β → Bool) :
    Instruction Φ testType → Value α → σ → Value α → σ → Prop where
  | primitive {i x before y after} (step : instr i x before y after) :
      Step instr input truth (.primitive i) x before y after
  | test (value : β) (state : σ) :
      Step instr input truth .test (input value) state (result (truth value)) state

theorem Step.test_iff {instr : Φ → Value α → σ → Value α → σ → Prop}
    {input : β → Value α} {truth : β → Bool} {x y : Value α} {before after : σ} :
    Step (testType := testType) instr input truth .test x before y after ↔
      ∃ value, x = input value ∧ y = result (truth value) ∧ after = before := by
  constructor
  · intro step
    cases step with | test value state => exact ⟨value, rfl, rfl, rfl⟩
  · rintro ⟨value, rfl, rfl, rfl⟩
    exact .test value _

theorem Step.deterministic {instr : Φ → Value α → σ → Value α → σ → Prop}
    {input : β → Value α} {truth : β → Bool} (det : Semantics.InstrDeterministic instr)
    (injective : Function.Injective input) :
    Semantics.InstrDeterministic (Step (testType := testType) instr input truth) := by
  intro i x before y middle z after one two
  cases one with
  | primitive one => cases two with
    | primitive two => exact det _ _ _ _ _ _ _ one two
  | test value state =>
    obtain ⟨other, same, output, final⟩ := Step.test_iff.mp two
    have eq := injective same
    subst other
    exact ⟨output.symm, final.symm⟩

theorem embed_eval {instr : Φ → Value α → σ → Value α → σ → Prop}
    {input : β → Value α} {truth : β → Bool} {env : Semantics.Env α} {term : Tm Φ}
    {before after : σ} {value : Value α} (execution : Semantics.Tm.Eval instr env term before value after) :
    Semantics.Tm.Eval (Step (testType := testType) instr input truth) env (embed term) before value after :=
  execution.mapInstr Instruction.primitive (fun _ _ _ _ _ step => .primitive step)

theorem embedRegion_eval {instr : Φ → Value α → σ → Value α → σ → Prop}
    {input : β → Value α} {truth : β → Bool} {env : Semantics.Env α} {region : Region Φ}
    {before after : σ} {label : Nat} {value : Value α}
    (execution : Semantics.Region.Eval instr env region before label value after) :
    Semantics.Region.Eval (Step (testType := testType) instr input truth) env (embedRegion region)
      before label value after :=
  execution.mapInstr Instruction.primitive (fun _ _ _ _ _ step => .primitive step)

end Silmaril.Isotope.LambdaSSA.Branch
