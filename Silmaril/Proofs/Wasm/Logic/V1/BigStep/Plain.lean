module

public import Silmaril.Wasm.Logic.V1.BigStep.Defs

/-!
# Non-control instructions as short reduction sequences

Each `Plain` or `PlainTrap` rule is realised by a reduction sequence of
`Silmaril.Wasm.V1.Execution.Step` on exactly the operands it mentions, with the
surrounding operand stack and code supplied by its evaluation-context rule.

Almost every rule is a single small step. Three are not: `Plain.intConst` and
`Plain.floatConst` take *no* step, because `Execution.value` already maps a
runtime value to its own constant instruction, and `Plain.localTee` takes
*two*, because `Execution.PureStep.localTee` duplicates the operand and defers
to `Execution.Step.localSet`. The conclusions below are therefore stated with
`Steps` rather than `Step`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1 Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

variable {H : Type*} {host : HostSemantics H}

/-- A non-control instruction step is a reduction sequence on its own operands. -/
theorem Plain.toStep {s s' : Store H} {f f' : Frame} {args rets : List Value} {i : Silmaril.Wasm.V1.Instr}
    (h : Plain s f args i s' f' rets) :
    Steps host ⟨s, f, values args ++ [.source i]⟩ ⟨s', f', values rets⟩ := by
  cases h with
  | nop => exact (Step.pure s f PureStep.nop).steps
  | drop v => exact (Step.pure s f (PureStep.drop v)).steps
  | selectZero a b sameType =>
      exact (Step.pure s f (PureStep.selectZero a b sameType)).steps
  | selectNonzero a b sameType c nonzero =>
      exact (Step.pure s f (PureStep.selectNonzero a b sameType c nonzero)).steps
  | intConst => exact .refl
  | floatConst => exact .refl
  | localGet i v found => exact (Step.localGet s f i v found).steps
  | localSet i v old found => exact (Step.localSet s f i v old found).steps
  | localTee i v old found =>
      exact .head (Step.pure s f (PureStep.localTee i v))
        ((Step.localSet s f i v old found).context [v] []).steps
  | globalGet i a g index found => exact (Step.globalGet s f i a g index found).steps
  | globalSet i a g v index found mutable =>
      exact (Step.globalSet s f i a g v index found mutable).steps
  | intLoad t packed arg c a m v memory loaded =>
      exact (Step.intLoad s f t packed arg c a m v memory loaded).steps
  | floatLoad t arg c a m v memory loaded =>
      exact (Step.floatLoad s f t arg c a m v memory loaded).steps
  | intStore t packed arg c x a m bytes memory stored =>
      exact (Step.intStore s f t packed arg c x a m bytes memory stored).steps
  | floatStore t arg c x a m bytes memory stored =>
      exact (Step.floatStore s f t arg c x a m bytes memory stored).steps
  | memorySize a m memory => exact (Step.memorySize s f a m memory).steps
  | memoryGrow a m c r bytes memory grown =>
      exact (Step.memoryGrow s f a m c r bytes memory grown).steps
  | intUnary t op x => exact (Step.pure s f (PureStep.intUnary t op x)).steps
  | intBinary t op x y z result =>
      exact (Step.pure s f (PureStep.intBinary t op x y z result)).steps
  | intTest t op x => exact (Step.pure s f (PureStep.intTest t op x)).steps
  | intRel t op x y => exact (Step.pure s f (PureStep.intRel t op x y)).steps
  | floatUnary t op x y result =>
      exact (Step.pure s f (PureStep.floatUnary t op x y result)).steps
  | floatBinary t op x y z result =>
      exact (Step.pure s f (PureStep.floatBinary t op x y z result)).steps
  | floatRel t op x y => exact (Step.pure s f (PureStep.floatRel t op x y)).steps
  | convert op x y result => exact (Step.pure s f (PureStep.convert op x y result)).steps

/-- A trapping non-control instruction reduces to `trap` on its own operands. -/
theorem PlainTrap.toStep {s : Store H} {f : Frame} {args : List Value} {i : Silmaril.Wasm.V1.Instr}
    (h : PlainTrap s f args i) :
    Steps host ⟨s, f, values args ++ [.source i]⟩ ⟨s, f, [.trap]⟩ := by
  cases h with
  | unreachable => exact (Step.pure s f PureStep.unreachable).steps
  | intBinary t op x y err result =>
      exact (Step.pure s f (PureStep.intBinaryTrap t op x y err result)).steps
  | convert op x err result =>
      exact (Step.pure s f (PureStep.convertTrap op x err result)).steps
  | intLoad t packed arg c a m memory loaded =>
      exact (Step.intLoadTrap s f t packed arg c a m memory loaded).steps
  | floatLoad t arg c a m memory loaded =>
      exact (Step.floatLoadTrap s f t arg c a m memory loaded).steps
  | intStore t packed arg c x a m memory stored =>
      exact (Step.intStoreTrap s f t packed arg c x a m memory stored).steps
  | floatStore t arg c x a m memory stored =>
      exact (Step.floatStoreTrap s f t arg c x a m memory stored).steps

/-- A trap anywhere in a configuration collapses it. -/
theorem Steps.trapCollapse (s : Store H) (f : Frame) (vs : List Value) (es : List Admin) :
    Steps host ⟨s, f, values vs ++ [.trap] ++ es⟩ ⟨s, f, [.trap]⟩ := by
  match vs, es with
  | v :: vs, es => exact (Step.pure s f (PureStep.trapValues v vs es)).steps
  | [], [] => exact .refl
  | [], i :: es => exact (Step.pure s f (PureStep.trapTail i es)).steps

end Silmaril.Wasm.Logic.V1
