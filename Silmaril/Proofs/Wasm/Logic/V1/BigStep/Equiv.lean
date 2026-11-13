module

public import Silmaril.Proofs.Wasm.Logic.V1.BigStep.Sound
public import Silmaril.Proofs.Wasm.Logic.V1.BigStep.Complete

/-!
# Equivalence of the big-step and small-step semantics

Theorem 1 of Watt et al., `reduce_trans_equiv_reduce_to`, for the WebAssembly
1.0 machine of `Silmaril.Wasm.V1.Execution`: the big-step semantics and the
transitive closure of the small-step semantics agree on both terminating runs
and traps.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1 Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

variable {H : Type*} {host : HostSemantics H}

/-- A run terminating with values is exactly a normal big-step derivation. -/
theorem bigStep_normal_iff_steps {s s' : Store H} {f f' : Frame} {vs ws : List Value}
    {es : List Admin} :
    BigStep host s f vs es ⟨s', f', .normal ws⟩ ↔
      Steps host ⟨s, f, values vs ++ es⟩ ⟨s', f', values ws⟩ :=
  ⟨BigStep.toSteps_normal, BigStep.ofSteps_normal⟩

/-- A run terminating in a trap is exactly a trapping big-step derivation. -/
theorem bigStep_trap_iff_steps {s s' : Store H} {f f' : Frame} {vs : List Value}
    {es : List Admin} :
    BigStep host s f vs es ⟨s', f', .trap⟩ ↔
      Steps host ⟨s, f, values vs ++ es⟩ ⟨s', f', [.trap]⟩ :=
  ⟨BigStep.toSteps_trap, BigStep.ofSteps_trap⟩

end Silmaril.Wasm.Logic.V1
