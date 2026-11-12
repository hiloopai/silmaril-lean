module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.InstructionPredicate
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.ResumptionInvariant

/-! # Instruction provenance through suspended source continuations

An allowed-instruction predicate checks active code, pending requests, every
saved expression/region and all captured CFG blocks. Actual administrative and
primitive transitions preserve it, including jumps into saved block scopes.
Thus an arbitrary scheduled run cannot invent an opcode absent from the
checked source predicate. Runtime values contain no executable code.

This is opcode/attribute provenance, not a source phase invariant: it does not
by itself establish operation order, arguments, memory safety or termination.
-/

@[expose] public section
universe u v w x
namespace Silmaril.Isotope.LambdaSSA.Resumption
open Semantics
variable {CTA : Type x} {α : Type u} {Φ : Type v} {σ : Type w}

def RegionCont.ForallInstr (allowed : Φ → Prop) : RegionCont α Φ → Prop
  | .halt => True
  | .cfg _ _ blocks next => (∀ index, (blocks index).ForallInstr allowed) ∧ next.ForallInstr allowed

def TermCont.ForallInstr (allowed : Φ → Prop) : TermCont α Φ → Prop
  | .halt | .abort => True
  | .op instruction next => allowed instruction ∧ next.ForallInstr allowed
  | .let₁ _ body next | .let₂ _ body next | .pairLeft _ body next =>
      body.ForallInstr allowed ∧ next.ForallInstr allowed
  | .pairRight _ next | .inl next | .inr next => next.ForallInstr allowed
  | .case _ left right next => left.ForallInstr allowed ∧ right.ForallInstr allowed ∧ next.ForallInstr allowed
  | .br _ next => next.ForallInstr allowed
  | .regionLet₁ _ body next | .regionLet₂ _ body next => body.ForallInstr allowed ∧ next.ForallInstr allowed
  | .regionCase _ left right next => left.ForallInstr allowed ∧ right.ForallInstr allowed ∧ next.ForallInstr allowed

def Control.ForallInstr (allowed : Φ → Prop) : Control α Φ → Prop
  | .term _ expression next => expression.ForallInstr allowed ∧ next.ForallInstr allowed
  | .value _ next => next.ForallInstr allowed
  | .region _ body next => body.ForallInstr allowed ∧ next.ForallInstr allowed
  | .branch _ _ next => next.ForallInstr allowed
  | .request instruction _ next => allowed instruction ∧ next.ForallInstr allowed

theorem Admin.forallInstr {allowed : Φ → Prop} {before after : Control α Φ}
    (transition : Admin before after) (checked : before.ForallInstr allowed) : after.ForallInstr allowed := by
  cases transition <;>
    simp_all [Control.ForallInstr, TermCont.ForallInstr, RegionCont.ForallInstr,
      Tm.ForallInstr, Region.ForallInstr]

variable {instr : Φ → Value α → σ → Value α → σ → Prop}

theorem Step.forallInstr {allowed : Φ → Prop} {first last : Control α Φ} {before after : σ}
    (step : Step instr first before last after) (checked : first.ForallInstr allowed) : last.ForallInstr allowed := by
  cases step with
  | admin transition => exact transition.forallInstr checked
  | instruction => exact checked.2

theorem Run.forallInstr {allowed : Φ → Prop} {first last : Control α Φ} {before after : σ}
    (run : Run instr first before last after) (checked : first.ForallInstr allowed) : last.ForallInstr allowed := by
  induction run with
  | refl => exact checked
  | head step _ ih => exact ih (step.forallInstr checked)

theorem startTerm_forallInstr (allowed : Φ → Prop) (env : Env α) (term : Tm Φ)
    (checked : term.ForallInstr allowed) : (startTerm env term).ForallInstr allowed := ⟨checked, trivial⟩

theorem startRegion_forallInstr (allowed : Φ → Prop) (env : Env α) (region : Region Φ)
    (checked : region.ForallInstr allowed) : (startRegion env region).ForallInstr allowed := ⟨checked, trivial⟩

namespace World
variable {instructions : CTA → Φ → Value α → σ → Value α → σ → Prop}

def ForallInstr (world : World CTA α Φ σ) (allowed : CTA → Φ → Prop) : Prop :=
  ∀ cta, (world.control cta).ForallInstr (allowed cta)

theorem Step.forallInstr {allowed : CTA → Φ → Prop} {cta : CTA} {before after : World CTA α Φ σ}
    (step : Step instructions cta before after) (checked : before.ForallInstr allowed) :
    after.ForallInstr allowed := by
  intro other
  by_cases same : other = cta
  · subst other
    exact step.execution.forallInstr (checked cta)
  · rw [step.other other same]
    exact checked other

theorem forallInstr_invariant (allowed : CTA → Φ → Prop) :
    Invariant instructions (fun world => world.ForallInstr allowed) :=
  fun _ _ _ step checked => step.forallInstr checked

theorem Run.forallInstr {allowed : CTA → Φ → Prop} {schedule : List CTA} {before after : World CTA α Φ σ}
    (run : Run instructions schedule before after) (checked : before.ForallInstr allowed) :
    after.ForallInstr allowed := (forallInstr_invariant allowed).run run checked

/-- Any instruction that an arbitrary reachable CTA is about to execute is
allowed by its original code and all captured source continuations. -/
theorem Run.request_allowed {allowed : CTA → Φ → Prop} {schedule : List CTA}
    {before after : World CTA α Φ σ} (run : Run instructions schedule before after)
    (checked : before.ForallInstr allowed) {cta : CTA} {instruction : Φ} {argument : Value α}
    {continuation : TermCont α Φ}
    (selected : after.control cta = .request instruction argument continuation) : allowed cta instruction := by
  have current := run.forallInstr checked cta
  rw [selected] at current
  exact current.1

/-- The request witness and actual primitive transition concern the same
reachable state; no whole-expression evaluation is used as an atomic step. -/
theorem Run.executed_allowed {allowed : CTA → Φ → Prop} {schedule : List CTA}
    {before current after : World CTA α Φ σ} (run : Run instructions schedule before current)
    (checked : before.ForallInstr allowed) {cta : CTA} {instruction : Φ} {argument : Value α}
    {continuation : TermCont α Φ} (selected : current.control cta = .request instruction argument continuation)
    (step : Step instructions cta current after) :
    allowed cta instruction ∧ ∃ result, after.control cta = .value result continuation ∧
      instructions cta instruction argument current.shared result after.shared := by
  refine ⟨run.request_allowed checked selected, ?_⟩
  have actual := step.execution
  rw [selected] at actual
  exact actual.from_request

end World
end Silmaril.Isotope.LambdaSSA.Resumption
