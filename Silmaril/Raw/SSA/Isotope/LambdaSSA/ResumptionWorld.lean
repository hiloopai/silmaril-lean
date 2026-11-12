module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Resumption
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.ResumptionTyping
public import Silmaril.Raw.SSA.Isotope.SequentialTrace

/-! # Shared-state scheduling of instruction-resumable SSA controls

The shared machine state occurs once. Each scheduling step advances exactly
one CTA by one administrative or primitive resumption step, using the current
shared state and preserving every other continuation. No step runs an entire
term or region. The supplied per-CTA primitive relation can include its own
local machine state, events and synchronization rules in the shared state.

A finite schedule records every selected CTA, including administrative steps.
Determinism is conditional on that schedule and primitive determinism. Nothing
here imposes fairness, total primitive execution or eventual termination.
-/

@[expose] public section
universe u v w x y
namespace Silmaril.Isotope.LambdaSSA.Resumption
open Semantics

structure World (CTA : Type x) (α : Type u) (Φ : Type v) (σ : Type w) where
  shared : σ
  control : CTA → Control α Φ

namespace World
variable {CTA : Type x} {α : Type u} {Φ : Type v} {σ : Type w}

@[ext] theorem ext {one two : World CTA α Φ σ}
    (shared : one.shared = two.shared) (control : one.control = two.control) : one = two := by
  cases one
  cases two
  cases shared
  cases control
  rfl

/-- A local instruction relation receives the current shared state, rather
than an independently cached copy belonging to its selected CTA. -/
structure Step (instr : CTA → Φ → Value α → σ → Value α → σ → Prop)
    (cta : CTA) (before after : World CTA α Φ σ) : Prop where
  execution : Resumption.Step (instr cta) (before.control cta) before.shared (after.control cta) after.shared
  other : ∀ different, different ≠ cta → after.control different = before.control different

abbrev Run (instr : CTA → Φ → Value α → σ → Value α → σ → Prop) :=
  SequentialTrace (Step instr)

variable {instr : CTA → Φ → Value α → σ → Value α → σ → Prop}

theorem Step.deterministic (det : ∀ cta, InstrDeterministic (instr cta))
    {cta : CTA} {before one two : World CTA α Φ σ}
    (first : Step instr cta before one) (second : Step instr cta before two) : one = two := by
  obtain ⟨control, shared⟩ := first.execution.deterministic (det cta) second.execution
  apply ext shared
  funext other
  by_cases same : other = cta
  · subst other
    exact control
  · exact (first.other other same).trans (second.other other same).symm

theorem Run.deterministic (det : ∀ cta, InstrDeterministic (instr cta))
    {schedule : List CTA} {before one two : World CTA α Φ σ}
    (first : Run instr schedule before one) (second : Run instr schedule before two) : one = two :=
  SequentialTrace.deterministic (execute := Step instr)
    (fun _ {_} {_} {_} a b => Step.deterministic det a b) first second

/-- A CTA omitted by the actual schedule retains its entire continuation. -/
theorem Run.other {schedule : List CTA} {before after : World CTA α Φ σ}
    (run : Run instr schedule before after) {cta : CTA} (absent : cta ∉ schedule) :
    after.control cta = before.control cta := by
  induction run with
  | nil => rfl
  | @cons selected rest before middle after head tail ih =>
    have different : cta ≠ selected := fun same => absent (same ▸ List.mem_cons_self ..)
    exact (ih (fun member => absent (List.mem_cons_of_mem _ member))).trans (head.other cta different)

/-- Shared-state and static per-CTA control invariants compose separately.
Control properties here do not depend on another CTA's mutable shared state. -/
def Satisfies (world : World CTA α Φ σ) (shared : σ → Prop) (control : CTA → Control α Φ → Prop) : Prop :=
  shared world.shared ∧ ∀ cta, control cta (world.control cta)

theorem Step.preserves {cta : CTA} {before after : World CTA α Φ σ}
    (step : Step instr cta before after) (shared : σ → Prop) (control : CTA → Control α Φ → Prop)
    (advance : ∀ first state last final, Resumption.Step (instr cta) first state last final →
      shared state → control cta first → shared final ∧ control cta last)
    (initial : before.Satisfies shared control) : after.Satisfies shared control := by
  obtain ⟨state, selected⟩ := advance _ _ _ _ step.execution initial.1 (initial.2 cta)
  refine ⟨state, fun other => ?_⟩
  by_cases same : other = cta
  · subst other
    exact selected
  · rw [step.other other same]
    exact initial.2 other

theorem Run.preserves {schedule : List CTA} {before after : World CTA α Φ σ}
    (run : Run instr schedule before after) (shared : σ → Prop) (control : CTA → Control α Φ → Prop)
    (advance : ∀ cta ∈ schedule, ∀ first state last final,
      Resumption.Step (instr cta) first state last final →
        shared state → control cta first → shared final ∧ control cta last)
    (initial : before.Satisfies shared control) : after.Satisfies shared control :=
  SequentialTrace.preserves run (fun world => world.Satisfies shared control)
    (fun cta member _ _ step => step.preserves shared control (advance cta member)) initial

section Install
variable [DecidableEq CTA]

def install (world : World CTA α Φ σ) (cta : CTA) (control : Control α Φ) (shared : σ) : World CTA α Φ σ :=
  ⟨shared, Function.update world.control cta control⟩

@[simp] theorem install_shared (world : World CTA α Φ σ) (cta : CTA) (control : Control α Φ) (shared : σ) :
    (world.install cta control shared).shared = shared := rfl

@[simp] theorem install_selected (world : World CTA α Φ σ) (cta : CTA) (control : Control α Φ) (shared : σ) :
    (world.install cta control shared).control cta = control := by simp [install]

theorem install_other (world : World CTA α Φ σ) {cta other : CTA} (different : other ≠ cta)
    (control : Control α Φ) (shared : σ) : (world.install cta control shared).control other = world.control other := by
  simp [install, different]

@[simp] theorem install_self (world : World CTA α Φ σ) (cta : CTA) :
    world.install cta (world.control cta) world.shared = world := by
  apply ext (one := world.install cta (world.control cta) world.shared) (two := world) rfl
  funext other
  by_cases same : other = cta
  · subst other
    exact install_selected ..
  · exact install_other _ same _ _

@[simp] theorem install_install (world : World CTA α Φ σ) (cta : CTA)
    (first last : Control α Φ) (middle final : σ) :
    (world.install cta first middle).install cta last final = world.install cta last final := by
  apply ext (one := (world.install cta first middle).install cta last final)
    (two := world.install cta last final) rfl
  funext other
  by_cases same : other = cta
  · subst other
    simp only [install_selected]
  · simp only [install_other _ same]

theorem Step.of_local {cta : CTA} {world : World CTA α Φ σ} {next : Control α Φ} {state : σ}
    (step : Resumption.Step (instr cta) (world.control cta) world.shared next state) :
    Step instr cta world (world.install cta next state) := by
  refine ⟨?_, fun other different => install_other world different next state⟩
  simpa only [install_selected, install_shared] using step

theorem Step.endpoint {cta : CTA} {before after : World CTA α Φ σ} (step : Step instr cta before after) :
    after = before.install cta (after.control cta) after.shared := by
  apply ext (one := after) (two := before.install cta (after.control cta) after.shared) rfl
  funext other
  by_cases same : other = cta
  · subst other
    simp only [install_selected]
  · rw [install_other _ same]
    exact step.other other same

theorem Step.instruction {cta : CTA} {world : World CTA α Φ σ} {f : Φ} {argument result : Value α}
    {continuation : TermCont α Φ} {state : σ}
    (selected : world.control cta = .request f argument continuation)
    (primitive : instr cta f argument world.shared result state) :
    Step instr cta world (world.install cta (.value result continuation) state) := by
  apply Step.of_local
  rw [selected]
  exact .instruction primitive

/-- Lift an actual single-CTA execution to a serial schedule containing one
entry per resumption step. The length is derived from the run, not postulated
as a polling bound or progress assumption. -/
theorem serial_run {cta : CTA} {first last : Control α Φ} {initial final : σ}
    (run : Resumption.Run (instr cta) first initial last final)
    (world : World CTA α Φ σ) (selected : world.control cta = first) (shared : world.shared = initial) :
    ∃ count, Run instr (List.replicate count cta) world (world.install cta last final) := by
  induction run generalizing world with
  | refl =>
    refine ⟨0, ?_⟩
    rw [← selected, ← shared, install_self]
    exact .nil _
  | @head first middle last initial state final head tail ih =>
    have localStep : Resumption.Step (instr cta) (world.control cta) world.shared middle state := by
      simpa only [selected, shared] using head
    obtain ⟨count, rest⟩ := ih (world.install cta middle state) (install_selected ..) rfl
    refine ⟨count + 1, ?_⟩
    simpa only [List.replicate_succ, install_install] using
      (SequentialTrace.cons (Step.of_local localStep) rest)

end Install

/-- A serial world schedule projects back to the same actual local run. This
does not project interleaved schedules to a run over stale shared state. -/
theorem Run.project_serial {cta : CTA} {count : Nat} {before after : World CTA α Φ σ}
    (run : Run instr (List.replicate count cta) before after) :
    Resumption.Run (instr cta) (before.control cta) before.shared (after.control cta) after.shared := by
  induction count generalizing before with
  | zero => cases run; exact .refl
  | succ count ih =>
    rw [List.replicate_succ] at run
    cases run with
    | cons head tail => exact .head head.execution (ih tail)

section Typing
variable {κ : Type y} [HasTy Φ (Ty κ)] {atomType : α → κ → Prop}

/-- Each CTA retains its own final answer type and all typed captured
environments. This static property places no liveness condition on the world. -/
def Typed (world : World CTA α Φ σ) (atomType : α → κ → Prop) (answer : CTA → Typing.Answer κ) : Prop :=
  ∀ cta, Typing.ControlTyped atomType (world.control cta) (answer cta)

theorem Step.typed {cta : CTA} {before after : World CTA α Φ σ} {answer : CTA → Typing.Answer κ}
    (primitiveTyped : Typing.InstrTyped atomType (instr cta))
    (step : Step instr cta before after) (initial : before.Typed atomType answer) :
    after.Typed atomType answer := by
  have preserved := step.preserves (fun _ => True)
    (fun c control => Typing.ControlTyped atomType control (answer c))
    (fun _ _ _ _ localStep _ typed => ⟨True.intro, Typing.Step.typed primitiveTyped localStep typed⟩)
    ⟨True.intro, initial⟩
  exact preserved.2

theorem Run.typed {schedule : List CTA} {before after : World CTA α Φ σ} {answer : CTA → Typing.Answer κ}
    (primitiveTyped : ∀ cta ∈ schedule, Typing.InstrTyped atomType (instr cta))
    (run : Run instr schedule before after) (initial : before.Typed atomType answer) :
    after.Typed atomType answer :=
  SequentialTrace.preserves run (fun world => world.Typed atomType answer)
    (fun cta member _ _ step => step.typed (primitiveTyped cta member)) initial

end Typing

end World
end Silmaril.Isotope.LambdaSSA.Resumption
