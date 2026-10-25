module

public import Silmaril.Wasm.Binaryen.DirectizeRel

@[expose] public section

/-! # The profile-independent administrative operations used by Directize

Reading a table and casting a reference make no numerical or growth choice.
Their reductions can be transported between numerical profiles even when the
surrounding program has nondeterministic floating-point or growth operations.
-/

namespace Silmaril.Wasm.Binaryen.DirSim

open Silmaril.Wasm Execution.Core Numerics SingleThreaded

variable {H : Type} {P Q : Profile}

/-- All table operations except grow are independent of the numerical profile. -/
theorem tableStep_profile {c c' : Config H} (h : TableStep P c c')
    (hg : ∀ x, c.code.getLast? ≠ some (.plain (.tableGrow x))) : TableStep Q c c' := by
  cases h <;> first
    | exact (hg _ rfl).elim
    | (constructor <;> assumption)

theorem head_tableGet_profile {s : Store H} {f : Frame} {args : List Val} {x : TableIdx}
    {c : Config H} (h : Det.Head P s f args (.plain (.tableGet x)) c) :
    Det.Head Q s f args (.plain (.tableGet x)) c := by
  have hf := h.fam_inv (by simp [Det.famOf])
  exact .table (tableStep_profile hf (by simp [List.getLast?_append]))

theorem head_refCast_profile {s : Store H} {f : Frame} {args : List Val} {rt : RefType}
    {c : Config H} (h : Det.Head P s f args (.plain (.refCast rt)) c) :
    Det.Head Q s f args (.plain (.refCast rt)) c := by
  exact .reference (h.fam_inv (by simp [Det.famOf]))

end Silmaril.Wasm.Binaryen.DirSim
