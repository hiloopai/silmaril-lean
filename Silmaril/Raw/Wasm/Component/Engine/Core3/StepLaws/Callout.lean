module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.StepLaws.Callout.Defs
public import Silmaril.Wasm.Component.Engine.Core3.Defs

/-!
# A host-call redex takes no interpreter step

If `SingleThreaded.decompose?` finds a host-call redex
`val^n (ref.func a) (call_ref yy)` (with `a` a host function of arity `n`) under the evaluation
contexts `val* [_] instr*`, `label`, `handler` and `frame`, then the interpreter step
`SingleThreaded.Exec.stepI o` is `none` (`stepI_none_of_decompose?`), without any typing
hypothesis: the control head step does not call host code (`Exec.Ctl.callRef?` is `none` on a
host function), the head rules of `label`, `handler` and `frame` (`Exec.adminStep?`) fire only
on a body that is all values or whose first non-value is a branch, `return`, a tail call,
`throw_ref` or `trap` (never a `call_ref` or a nested context), and the driver recurses only into
the body that holds the redex.

This is the untyped analogue of `callout_no_internal` (SingleThreaded/Agreement.lean).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core

variable {H : Type}

namespace StepLaws

/-! ## The shape of a host-call redex -/

/-! ## The head rules of `label`, `handler` and `frame` do not fire on a redex -/

/-! ## The head step at a redex -/

/-! ## The driver at a redex -/

end StepLaws

end Silmaril.Wasm.Component.Engine.Core3
