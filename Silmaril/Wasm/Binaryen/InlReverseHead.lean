module

public import Silmaril.Wasm.Binaryen.InlSim

@[expose] public section

/-! # Chosen reverse head steps for the actual inlining store relation

The transformed computation supplies the head step and its actual result. We
restore the original function table and replay that same numerical, memory,
table, reference or aggregate choice. This uses neither a deterministic profile
nor uniqueness of terminal results. Entering a Wasm function is kept as an
explicit separate case: its body can contain the inlined site and needs the
recursive caller/callee simulation.

These lemmas cover computational heads. They do not assert closure of the full
inlining runtime relation under intermediate block-entry/parameter-store phases.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Validation Numerics SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Profile}

/-- Restoring the original function table recovers the exact original store,
including all mutable memories, tables, globals, heap objects and segments. -/
theorem SR.restore_original {s t : Store H} (related : SR p s t) :
    withFuncs t s.funcs = s := by
  rw [related.ht]
  rfl

/-- A selected transformed primitive reduct still has the actual inlining store
relation after its original function table is restored. -/
theorem SR.restore_reduct {s t next : Store H} (related : SR p s t)
    (functions : next.funcs = t.funcs) : SR p (withFuncs next s.funcs) next := by
  refine ⟨related.hg, related.hf, ?_⟩
  change next = { next with funcs := newFuncs p s.funcs }
  have same : newFuncs p s.funcs = next.funcs := by
    rw [functions, related.ht]
    rfl
  rw [same]

/-- Replay the chosen transformed simple head in the original store and frame.
Local accesses and structured administrative heads have their own frame-sensitive
rules; a Wasm function entry remains explicit instead of assuming its code equal. -/
theorem head_simple_reverse {s t : Store H} {originalFrame transformedFrame : Frame}
    {args : List Val} {head : Admin} {next : Config H}
    (related : SR p s t) (modules : transformedFrame.module = originalFrame.module)
    (simple : SimpleE head)
    (selected : Det.Head P t transformedFrame args head next) :
    CallData t transformedFrame args head next ∨
      ∃ originalNext : Config H,
        Det.Head P s originalFrame args head originalNext ∧
        originalNext.frame = originalFrame ∧ next.frame = transformedFrame ∧
        originalNext.code = next.code ∧ SR p originalNext.store next.store := by
  have types : SameTypes s.funcs t.funcs := by
    rw [related.ht]
    exact related.sameTypes.symm
  rcases head_simple selected simple types originalFrame.locals with call |
      ⟨frame, functions, actual⟩
  · exact .inl call
  · refine .inr ⟨⟨withFuncs next.store s.funcs, originalFrame, next.code⟩,
      ?_, rfl, frame, rfl, related.restore_reduct functions⟩
    have sameFrame : (⟨originalFrame.locals, transformedFrame.module⟩ : Frame) = originalFrame := by
      rw [modules]
    simpa only [related.restore_original, sameFrame] using actual

/-- The generic runtime mode retains the exact selected head outcome and the
actual mutable-store relation. No termination or profile-determinism assumption
is needed to choose the matching original computation. -/
theorem reverse_generic_simple_head {s t : Store H} {frame : Frame}
    {args : List Val} {head : Admin} {next : Config H}
    (related : SR p s t) (simple : SimpleE head)
    (selected : Det.Head P t frame args head next) :
    CallData t frame args head next ∨
      ∃ originalNext : Config H,
        Det.Head P s frame args head originalNext ∧
        MR p .gen originalNext next ∧ SR p originalNext.store next.store := by
  rcases head_simple_reverse related rfl simple selected with call |
      ⟨originalNext, actual, originalFrame, transformedFrame, code, stores⟩
  · exact .inl call
  · refine .inr ⟨originalNext, actual, ⟨transformedFrame.trans originalFrame.symm, ?_⟩, stores⟩
    rw [code]
    exact LN.refl p _

/-- For an actual non-call computational head, reverse matching is unconditional:
the selected transformed outcome has an original step and the exact runtime/store
relation. The remaining separate call-entry case is absent by its syntax. -/
theorem reverse_generic_noncall_head {s t : Store H} {frame : Frame}
    {args : List Val} {head : Admin} {next : Config H}
    (related : SR p s t) (simple : SimpleE head) (noncall : ¬ head.IsCallRef)
    (selected : Det.Head P t frame args head next) :
    ∃ originalNext : Config H,
      Det.Head P s frame args head originalNext ∧
      MR p .gen originalNext next ∧ SR p originalNext.store next.store := by
  rcases reverse_generic_simple_head related simple selected with call | matched
  · obtain ⟨_, _, _, _, _, _, _, isCall, _⟩ := call
    exact (noncall isCall).elim
  · exact matched

end Silmaril.Wasm.Binaryen.InlR
