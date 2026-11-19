module

public import Silmaril.Wasm.Execution.Core.Intrinsic.Observation.Defs
import Silmaril.Wasm.Execution.Core.Intrinsic.Thms
import Silmaril.Wasm.Behaviour.Semantics.CorePrefix

public section

namespace Silmaril.Proofs.Wasm.Execution.Core.Intrinsic

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Execution.Core.Intrinsic

variable {H : Type} {context : Context} {world : World H context}
  {locals input middle output : List IntType} {oracle : Oracle}

theorem observe_seq (op : Op locals input middle) (tail : Code locals middle output)
    (frame : LocalFrame world locals) (stack : Values input) (next : Values middle)
    (h : op.eval frame.values stack = .next next) :
    (Code.seq op tail).observe oracle frame stack = tail.observe oracle frame next := by
  have computed : (State.mk frame (.run stack (.seq op tail))).step? =
      some ⟨frame, .run next tail⟩ := by
    simp [State.step?, Control.step?, h, Effect.resume]
  refine behavioursOf_eq_of_step_unique (State.step_sound computed) ?_
  intro target rawStep
  obtain ⟨successor, successorStep, rfl⟩ := State.run_reflect frame stack (.seq op tail) rawStep
  cases Option.some.inj (computed.symm.trans successorStep)
  rfl

theorem append_congr (prefixCode : Code locals input middle) (valid : prefixCode.Nontrapping)
    {left right : Code locals middle output} (same : Code.ObsEq oracle left right) :
    Code.ObsEq oracle (prefixCode.append left) (prefixCode.append right) := by
  induction prefixCode with
  | done => exact same
  | seq op tail ih =>
    intro H context world frame stack
    obtain ⟨next, h⟩ := valid.1 frame.values stack
    rw [Code.append, Code.append, observe_seq op _ frame stack next h, observe_seq op _ frame stack next h]
    exact ih valid.2 same frame next

theorem nop_obsEq (code : Code locals input output) : Code.ObsEq oracle (.seq .nop code) code :=
  fun frame stack => observe_seq .nop code frame stack stack rfl

theorem nop_erasure_ne (code : Code locals input output) : (Code.seq .nop code).erase ≠ code.erase := by
  intro eq
  have lengths := congrArg List.length eq
  simp [Code.erase] at lengths

end Silmaril.Proofs.Wasm.Execution.Core.Intrinsic
