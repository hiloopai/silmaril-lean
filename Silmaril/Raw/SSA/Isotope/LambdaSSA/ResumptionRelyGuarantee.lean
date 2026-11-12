module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.ResumptionInvariant

/-! # Interference-stable assertions for instruction resumptions

Assertions describe exact controls, including suspended argument evaluation
and captured continuations, in the current shared state. Administrative closure
and actual instruction request/return closure are separate proof obligations.
Other CTAs may change shared state: an explicit interference rule preserves
their assertions under the selected CTA's proved guarantee.

There is no future-evaluation, termination or progress premise. The framework
proves partial correctness for arbitrary supplied instruction schedules.
-/

@[expose] public section
universe u v w x
namespace Silmaril.Isotope.LambdaSSA.Resumption.World
open Semantics
variable {CTA : Type x} {α : Type u} {Φ : Type v} {σ : Type w}
variable {instr : CTA → Φ → Value α → σ → Value α → σ → Prop}

/-- A proof rule covers actual microstates. Its guarantee constrains effects
that occur; administrative steps keep shared state and need no guarantee. -/
structure RelyGuarantee (instr : CTA → Φ → Value α → σ → Value α → σ → Prop)
    (shared : σ → Prop) (assertion : CTA → Control α Φ → σ → Prop)
    (guarantee : CTA → σ → σ → Prop) : Prop where
  admin : ∀ cta before after state, Admin before after → shared state →
    assertion cta before state → assertion cta after state
  instruction : ∀ cta f argument continuation before result after,
    instr cta f argument before result after → shared before →
    assertion cta (.request f argument continuation) before →
    shared after ∧ assertion cta (.value result continuation) after ∧ guarantee cta before after
  interference : ∀ actor other before after control, other ≠ actor →
    guarantee actor before after → shared before → shared after →
    assertion other control before → assertion other control after

namespace RelyGuarantee
variable {shared : σ → Prop} {assertion : CTA → Control α Φ → σ → Prop}
variable {guarantee : CTA → σ → σ → Prop}

/-- A real local step establishes its selected assertion and either leaves
shared state unchanged or supplies its actual interference guarantee. -/
theorem advance (rules : RelyGuarantee instr shared assertion guarantee)
    {cta : CTA} {first last : Control α Φ} {before after : σ}
    (step : Resumption.Step (instr cta) first before last after)
    (global : shared before) (selected : assertion cta first before) :
    shared after ∧ assertion cta last after ∧ (after = before ∨ guarantee cta before after) := by
  cases step with
  | admin transition => exact ⟨global, rules.admin cta _ _ _ transition global selected, Or.inl rfl⟩
  | instruction primitive =>
      obtain ⟨globalAfter, selectedAfter, effect⟩ := rules.instruction cta _ _ _ _ _ _ primitive global selected
      exact ⟨globalAfter, selectedAfter, Or.inr effect⟩

theorem step (rules : RelyGuarantee instr shared assertion guarantee)
    {cta : CTA} {before after : World CTA α Φ σ} (executed : Step instr cta before after)
    (initial : before.Relational shared assertion) : after.Relational shared assertion := by
  obtain ⟨globalAfter, selectedAfter, change⟩ := rules.advance executed.execution initial.1 (initial.2 cta)
  refine ⟨globalAfter, fun other => ?_⟩
  by_cases same : other = cta
  · subst other
    exact selectedAfter
  · rw [executed.other other same]
    rcases change with identity | effect
    · rw [identity]
      exact initial.2 other
    · exact rules.interference cta other _ _ _ same effect initial.1 globalAfter (initial.2 other)

theorem invariant (rules : RelyGuarantee instr shared assertion guarantee) :
    Invariant instr (fun world => world.Relational shared assertion) :=
  fun _ _ _ executed initial => rules.step executed initial

theorem run (rules : RelyGuarantee instr shared assertion guarantee)
    {schedule : List CTA} {before after : World CTA α Φ σ} (executed : Run instr schedule before after)
    (initial : before.Relational shared assertion) : after.Relational shared assertion :=
  rules.invariant.run executed initial

/-- Terminal extraction requires an actual completed run and the caller's
proved interpretation of terminal controls. It does not construct that run. -/
theorem terminal (rules : RelyGuarantee instr shared assertion guarantee)
    {schedule : List CTA} {before after : World CTA α Φ σ} (executed : Run instr schedule before after)
    (initial : before.Relational shared assertion)
    (terminal : CTA → Control α Φ → Prop) (post : CTA → σ → Prop)
    (stopped : ∀ cta, terminal cta (after.control cta))
    (extract : ∀ cta control state, shared state → assertion cta control state → terminal cta control → post cta state) :
    shared after.shared ∧ ∀ cta, post cta after.shared :=
  (rules.run executed initial).terminal terminal post stopped extract

/-- Two independently established control/state facts may be combined. Both
guarantees are retained; each interference proof uses its own component. -/
theorem and {shared' : σ → Prop} {assertion' : CTA → Control α Φ → σ → Prop}
    {guarantee' : CTA → σ → σ → Prop}
    (one : RelyGuarantee instr shared assertion guarantee)
    (two : RelyGuarantee instr shared' assertion' guarantee') :
    RelyGuarantee instr (fun state => shared state ∧ shared' state)
      (fun cta control state => assertion cta control state ∧ assertion' cta control state)
      (fun cta before after => guarantee cta before after ∧ guarantee' cta before after) where
  admin cta before after state transition global selected :=
    ⟨one.admin cta before after state transition global.1 selected.1,
      two.admin cta before after state transition global.2 selected.2⟩
  instruction cta f argument continuation before result after primitive global selected := by
    obtain ⟨globalOne, selectedOne, effectOne⟩ := one.instruction cta f argument continuation before result after
      primitive global.1 selected.1
    obtain ⟨globalTwo, selectedTwo, effectTwo⟩ := two.instruction cta f argument continuation before result after
      primitive global.2 selected.2
    exact ⟨⟨globalOne, globalTwo⟩, ⟨selectedOne, selectedTwo⟩, ⟨effectOne, effectTwo⟩⟩
  interference actor other before after control different effect globalBefore globalAfter selected :=
    ⟨one.interference actor other before after control different effect.1 globalBefore.1 globalAfter.1 selected.1,
      two.interference actor other before after control different effect.2 globalBefore.2 globalAfter.2 selected.2⟩

end RelyGuarantee
end Silmaril.Isotope.LambdaSSA.Resumption.World
