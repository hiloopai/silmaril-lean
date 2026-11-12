module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.ResumptionWorld

/-! # Finite pure control spines ending at a yield boundary

A spine lists actual controls, including all captured continuation frames.
Each link is either one administrative rule or one primitive whose particular
input/output transition preserves every current machine state. No link uses
whole-term evaluation, and the boundary instruction is not executed by the
certificate. Determinism then classifies arbitrary actual steps through this
spine, even when other threads change shared state between its links.

This is a finite expression-fragment rule, not a termination assumption for
an enclosing loop. The run decomposition either retains a suspended control
or exhibits the actual first scheduled transition from the yield boundary.
-/

@[expose] public section
universe u v w x
namespace Silmaril.Isotope.LambdaSSA.Resumption
open Semantics
variable {α : Type u} {Φ : Type v} {σ : Type w} {CTA : Type x}

inductive PureLink (instr : Φ → Value α → σ → Value α → σ → Prop) :
    Control α Φ → Control α Φ → Prop where
  | admin {first last} : Admin first last → PureLink instr first last
  | instruction {f input output continuation}
      (step : ∀ state, instr f input state output state) :
      PureLink instr (.request f input continuation) (.value output continuation)

theorem PureLink.step {instr : Φ → Value α → σ → Value α → σ → Prop}
    {first last : Control α Φ} (link : PureLink instr first last) (state : σ) :
    Step instr first state last state := by
  cases link with
  | admin transition => exact .admin transition
  | instruction transition => exact .instruction (transition state)

/-- A finite control spine, ending immediately before an unhandled effect or
another explicitly chosen source boundary. All intermediate links are pure. -/
structure Spine (instr : Φ → Value α → σ → Value α → σ → Prop) (length : Nat) where
  node : Fin (length + 1) → Control α Φ
  link : ∀ index : Fin length, PureLink instr (node index.castSucc) (node index.succ)

namespace Spine
variable {instr : Φ → Value α → σ → Value α → σ → Prop} {length : Nat}

def entry (spine : Spine instr length) : Control α Φ := spine.node 0
def boundary (spine : Spine instr length) : Control α Φ := spine.node (Fin.last length)
def At (spine : Spine instr length) (control : Control α Φ) : Prop := ∃ index, control = spine.node index

theorem at_entry (spine : Spine instr length) : spine.At spine.entry := ⟨0, rfl⟩
theorem at_boundary (spine : Spine instr length) : spine.At spine.boundary := ⟨Fin.last length, rfl⟩

/-- A selected actual step away from the boundary is the certified next pure
link. In particular it preserves the *current* state, not a stored snapshot. -/
theorem advance (spine : Spine instr length) (det : InstrDeterministic instr)
    {first last : Control α Φ} {before after : σ} (present : spine.At first)
    (inside : first ≠ spine.boundary) (executed : Step instr first before last after) :
    spine.At last ∧ after = before := by
  obtain ⟨index, rfl⟩ := present
  have less : index.val < length := by
    by_contra notLess
    have same : index = Fin.last length := Fin.ext (by simp only [Fin.val_last]; omega)
    exact inside (congrArg spine.node same)
  let next : Fin length := ⟨index.val, less⟩
  have same : next.castSucc = index := Fin.ext rfl
  have certified := (spine.link next).step before
  rw [same] at certified
  obtain ⟨control, state⟩ := executed.deterministic det certified
  exact ⟨⟨next.succ, control⟩, state⟩

variable {instructions : CTA → Φ → Value α → σ → Value α → σ → Prop} {cta : CTA}

/-- Interference leaves the saved control intact, with no assumption on how
the other CTA changes shared memory, events or local-machine components. -/
theorem other_step (spine : Spine (instructions cta) length)
    {actor : CTA} {before after : World CTA α Φ σ} (different : cta ≠ actor)
    (executed : World.Step instructions actor before after) (present : spine.At (before.control cta)) :
    spine.At (after.control cta) := by
  rw [executed.other cta different]
  exact present

theorem world_step (spine : Spine (instructions cta) length) (det : InstrDeterministic (instructions cta))
    {actor : CTA} {before after : World CTA α Φ σ} (executed : World.Step instructions actor before after)
    (present : spine.At (before.control cta))
    (inside : actor = cta → before.control cta ≠ spine.boundary) :
    spine.At (after.control cta) := by
  by_cases same : actor = cta
  · subst actor
    exact (spine.advance det present (inside rfl) executed.execution).1
  · exact spine.other_step (Ne.symm same) executed present

/-- A genuine chronological prefix, boundary transition and suffix of an
existing run. No future execution is added by this witness. -/
def Crossed (spine : Spine (instructions cta) length) (schedule : List CTA)
    (before after : World CTA α Φ σ) : Prop :=
  ∃ front tail waiting resumed,
    schedule = front ++ cta :: tail ∧
    World.Run instructions front before waiting ∧
    waiting.control cta = spine.boundary ∧
    World.Step instructions cta waiting resumed ∧
    World.Run instructions tail resumed after

/-- Every actual schedule either leaves the tracked CTA suspended in the
spine or contains a real transition from its exact yield boundary. -/
theorem run_or_crossed (spine : Spine (instructions cta) length)
    (det : InstrDeterministic (instructions cta)) {schedule : List CTA}
    {before after : World CTA α Φ σ} (run : World.Run instructions schedule before after)
    (present : spine.At (before.control cta)) : spine.At (after.control cta) ∨ spine.Crossed schedule before after := by
  induction run with
  | nil => exact Or.inl present
  | @cons actor rest before middle after head tail ih =>
    by_cases same : actor = cta
    · subst actor
      by_cases boundary : before.control cta = spine.boundary
      · exact Or.inr ⟨[], rest, before, middle, rfl, .nil _, boundary, head, tail⟩
      · rcases ih (spine.world_step det head present (fun _ => boundary)) with stayed | crossed
        · exact Or.inl stayed
        · obtain ⟨front, suffix, waiting, resumed, order, first, boundary, transition, last⟩ := crossed
          exact Or.inr ⟨cta :: front, suffix, waiting, resumed, congrArg (cta :: ·) order,
            .cons head first, boundary, transition, last⟩
    · rcases ih (spine.world_step det head present (fun impossible => (same impossible).elim)) with stayed | crossed
      · exact Or.inl stayed
      · obtain ⟨front, suffix, waiting, resumed, order, first, boundary, transition, last⟩ := crossed
        exact Or.inr ⟨actor :: front, suffix, waiting, resumed, congrArg (actor :: ·) order,
          .cons head first, boundary, transition, last⟩

end Spine
end Silmaril.Isotope.LambdaSSA.Resumption
