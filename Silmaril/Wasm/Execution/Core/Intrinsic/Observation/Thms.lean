module

public import Silmaril.Wasm.Execution.Core.Intrinsic.Observation.Defs
import Silmaril.Proofs.Wasm.Execution.Core.Intrinsic.Observation

public section

namespace Silmaril.Wasm.Execution.Core.Intrinsic

open Silmaril.Wasm.Validation

variable {H : Type} {context : Context} {world : World H context}
  {locals input middle output : List IntType} {oracle : Oracle}

theorem Code.observe_seq (op : Op locals input middle) (tail : Code locals middle output)
    (frame : LocalFrame world locals) (stack : Values input) (next : Values middle)
    (h : op.eval frame.values stack = .next next) :
    (Code.seq op tail).observe oracle frame stack = tail.observe oracle frame next :=
  Proofs.Wasm.Execution.Core.Intrinsic.observe_seq op tail frame stack next h

/-- A nontrapping typed left context respects equality of Core observations. -/
theorem Code.append_congr (prefixCode : Code locals input middle) (valid : prefixCode.Nontrapping)
    {left right : Code locals middle output} (same : Code.ObsEq oracle left right) :
    Code.ObsEq oracle (prefixCode.append left) (prefixCode.append right) :=
  Proofs.Wasm.Execution.Core.Intrinsic.append_congr prefixCode valid same

theorem Code.nop_obsEq (code : Code locals input output) : Code.ObsEq oracle (.seq .nop code) code :=
  Proofs.Wasm.Execution.Core.Intrinsic.nop_obsEq code

/-- The semantic quotient identifies two sequences that exact erasure does
not. This witnesses that the two quotients have different observations. -/
theorem Code.nop_quotient (code : Code locals input output) :
    Quotient.mk (Code.obsSetoid oracle locals input output) (Code.seq .nop code) =
      Quotient.mk (Code.obsSetoid oracle locals input output) code ∧
    (Code.seq .nop code).erase ≠ code.erase :=
  ⟨Quotient.sound (Code.nop_obsEq code), Proofs.Wasm.Execution.Core.Intrinsic.nop_erasure_ne code⟩

end Silmaril.Wasm.Execution.Core.Intrinsic
