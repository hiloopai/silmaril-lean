module

public import Silmaril.Wasm.Behaviour.Basic
public import Silmaril.Wasm.V2.Execution.Basic

/-!
# `V2.Execution.Result` as a behaviour

WebAssembly 2.0's `result ::= _VALS val* | TRAP` (`4-runtime:46`). 2.0 has
reference and vector values, so the behaviour is over `V2.Execution.Val` rather
than the flat numeric `Execution.Runtime.Value` of V1/Lime1; the comparison with
Core 3.0 requires a value translation, rather than equality of the two value
types. Cross-version execution simulations are not included in this release.

2.0 has no exception handling and keeps non-termination in `Diverges`, so
`throws` and `diverges` are outside the image.
-/

@[expose] public section

namespace Silmaril.Wasm.V2.Execution

/-- The observable behaviour of a 2.0 result. -/
def Result.toBehaviour : Result → Behaviour Val
  | .values vs => .returns vs
  | .trap => .traps

@[simp] theorem Result.toBehaviour_values (vs : List Val) :
    (Result.values vs).toBehaviour = .returns vs := rfl

@[simp] theorem Result.toBehaviour_trap : Result.trap.toBehaviour = .traps := rfl

/-! ## Range -/

/-- Wasm 2.0 has no exception handling. -/
@[simp] theorem Result.toBehaviour_ne_throws (r : Result) (a : Nat) :
    r.toBehaviour ≠ .throws a := by
  cases r <;> simp

/-- Divergence is not a result: it is the separate `Diverges` predicate. -/
@[simp] theorem Result.toBehaviour_ne_diverges (r : Result) :
    r.toBehaviour ≠ .diverges := by
  cases r <;> simp

/-- Every result is a terminating behaviour. -/
theorem Result.terminates_toBehaviour (r : Result) : r.toBehaviour.Terminates := by
  cases r <;> trivial

theorem Result.toBehaviour_injective : Function.Injective Result.toBehaviour := by
  intro r r' h
  cases r <;> cases r' <;> simp_all
