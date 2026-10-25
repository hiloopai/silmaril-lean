module

public import Silmaril.Wasm.Binaryen.InlReverseCall

@[expose] public section

/-! # Chosen reverse flat heads in the generic inlining mode

Generic configurations have equal frames, so a selected local access transfers
with its exact lookup, bounds and frame update. Restoring the original function
table transports every variable-family step. Together with the simple-head
reverse law, this covers all heads other than structured administrative labels,
handlers and frames, under any numerical profile and without outcome uniqueness.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Validation Numerics SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Profile}

/-- Replay the selected variable step after restoring the original function
list. The same actual frame update and result code occur on both sides. -/
theorem reverse_generic_variable {s t : Store H} {frame : Frame}
    {args : List Val} {head : Admin} {next : Config H} (related : SR p s t)
    (selected : VariableStep ⟨t, frame, vals args ++ [head]⟩ next) :
    ∃ originalNext : Config H,
      Det.Head P s frame args head originalNext ∧
      MR p .gen originalNext next ∧ SR p originalNext.store next.store := by
  obtain ⟨nextStore, nextFrame, nextCode⟩ := next
  obtain ⟨functions, replay⟩ := variableStep_withFuncs selected s.funcs
  refine ⟨⟨withFuncs nextStore s.funcs, nextFrame, nextCode⟩,
    ?_, ⟨rfl, LN.refl p _⟩, related.restore_reduct functions⟩
  apply Det.Head.variable
  simpa only [related.restore_original] using replay

/-- Every actual selected flat head step has an original head step with the
actual generic runtime and store relations. The hypotheses exclude only nested
administrative contexts, not structured Wasm instructions or local accesses. -/
theorem reverse_generic_flat_head (parameters : PrmOk p)
    {s t : Store H} {frame : Frame} {args : List Val} {head : Admin} {next : Config H}
    (related : SR p s t)
    (nonlabel : ∀ n cont body, head ≠ .label n cont body)
    (nonhandler : ∀ n catches body, head ≠ .handler n catches body)
    (nonframe : ∀ n frame body, head ≠ .frame n frame body)
    (selected : Det.Head P t frame args head next) :
    ∃ originalNext : Config H,
      Det.Head P s frame args head originalNext ∧
      MR p .gen originalNext next ∧ SR p originalNext.store next.store := by
  by_cases simple : SimpleE head
  · exact reverse_generic_simple_head_matched parameters related simple selected
  · have localAccess : ∃ x, head = .plain (.localGet x) ∨ head = .plain (.localSet x) ∨
        head = .plain (.localTee x) := by
      refine Classical.byContradiction fun absent =>
        simple ⟨nonlabel, nonhandler, nonframe, ?_, ?_, ?_⟩
      · intro x eq; exact absent ⟨x, .inl eq⟩
      · intro x eq; exact absent ⟨x, .inr (.inl eq)⟩
      · intro x eq; exact absent ⟨x, .inr (.inr eq)⟩
    obtain ⟨x, shape⟩ := localAccess
    have family : Det.famOf head = .variable := by
      rcases shape with rfl | rfl | rfl <;> rfl
    cases selected with
    | «variable» step => exact reverse_generic_variable related step
    | parametric step =>
      exact absurd ((Det.famOf_of_shape (Det.ParametricStep.shape step)).2.symm.trans family)
        (by decide)
    | numeric step =>
      exact absurd ((Det.famOf_of_shape (Det.NumericStep.shape step)).2.symm.trans family)
        (by decide)
    | vector step =>
      exact absurd ((Det.famOf_of_shape (Det.VectorStep.shape step)).2.symm.trans family)
        (by decide)
    | table step =>
      exact absurd ((Det.famOf_of_shape (Det.TableStep.shape step)).2.symm.trans family)
        (by decide)
    | memory step =>
      exact absurd ((Det.famOf_of_shape (Det.MemoryStep.shape step)).2.symm.trans family)
        (by decide)
    | reference step =>
      exact absurd ((Det.famOf_of_shape (Det.RefStep.shape step)).2.symm.trans family)
        (by decide)
    | aggregate step =>
      exact absurd ((Det.famOf_of_shape (Det.AggregateStep.shape step)).2.symm.trans family)
        (by decide)
    | _ => rcases shape with eq | eq | eq <;> (try cases eq) <;> simp_all [Admin.IsCallRef]

end Silmaril.Wasm.Binaryen.InlR
