module

public import Silmaril.Wasm.Behaviour.Basic
public import Silmaril.Wasm.Execution.Core.Runtime

/-!
# `Execution.Core.Result` as a behaviour

Core 3.0's `result ::= _VALS val* | (REF.EXN_ADDR a) THROW_REF | TRAP` is the
only result type in this development with three alternatives, and it is the
reason `Behaviour` has a `throws` constructor: an exception that escapes an
invocation is a genuinely different observation from a trap, because the
embedder may catch it and resume. The adapter is total, and it is the only one
whose image meets `Behaviour.throws`.

As everywhere else, divergence is not a result — Core 3.0 keeps it in
`Execution.Core.Diverges` — so `Result.toBehaviour_ne_diverges` holds here too.
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.Core

/-- The observable behaviour of a Core 3.0 result. -/
def Result.toBehaviour : Result → Behaviour Val
  | .values vs => .returns vs
  | .throw a => .throws a
  | .trap => .traps

@[simp] theorem Result.toBehaviour_values (vs : List Val) :
    (Result.values vs).toBehaviour = .returns vs := rfl

@[simp] theorem Result.toBehaviour_throw (a : Nat) :
    (Result.throw a).toBehaviour = .throws a := rfl

@[simp] theorem Result.toBehaviour_trap : Result.trap.toBehaviour = .traps := rfl

/-! ## Range

Core 3.0 reaches every terminating constructor and no other. -/

/-- Divergence is not a result: it is the separate `Diverges` predicate. -/
@[simp] theorem Result.toBehaviour_ne_diverges (r : Result) :
    r.toBehaviour ≠ .diverges := by
  cases r <;> simp

/-- Every result is a terminating behaviour. -/
theorem Result.terminates_toBehaviour (r : Result) : r.toBehaviour.Terminates := by
  cases r <;> trivial

/-- `Result.toBehaviour` is a bijection onto the terminating behaviours; in
particular it loses nothing. -/
theorem Result.toBehaviour_injective : Function.Injective Result.toBehaviour := by
  intro r r' h
  cases r <;> cases r' <;> simp_all

/-- Every terminating behaviour is the image of a result: Core 3.0's result type
is exactly `Behaviour` minus `diverges`. -/
theorem Result.exists_toBehaviour {b : Behaviour Val} (h : b.Terminates) :
    ∃ r : Result, r.toBehaviour = b := by
  cases b with
  | returns vs => exact ⟨.values vs, rfl⟩
  | traps => exact ⟨.trap, rfl⟩
  | throws a => exact ⟨.throw a, rfl⟩
  | diverges => exact absurd h (by simp)
