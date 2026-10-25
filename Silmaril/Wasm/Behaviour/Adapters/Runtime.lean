module

public import Silmaril.Wasm.Behaviour.Basic
public import Silmaril.Wasm.Execution.Runtime

/-!
# `Execution.Runtime.Result` as a behaviour

`Execution.Runtime.Result` is the result type shared by WebAssembly 1.0 and
Lime1: `_VALS val*` or `TRAP`. It is *total* as a source of behaviours — both of
its alternatives are genuine observations — so the adapter is a plain function
`Result → Behaviour Value` rather than an `Option`-valued one.

Divergence is deliberately absent: like every small-step semantics here, V1 and
Lime1 keep non-termination outside the result type, in the separate `Diverges`
predicate, and `Behaviour.diverges` is produced only by the `behavioursOf`
definitions of `Silmaril/Wasm/Behaviour/Semantics/`. Exceptions are absent
because neither language has them. Both facts are recorded as range lemmas
(`Result.toBehaviour_ne_throws`, `Result.toBehaviour_ne_diverges`) rather than by
giving these semantics a narrower behaviour type; that is what lets the
cross-version refinement statements of `Silmaril/Wasm/Behaviour/Relations.lean`
compare a V1 behaviour set with a Core 3.0 one at all.
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.Runtime

/-- The observable behaviour of a V1/Lime1 result. -/
def Result.toBehaviour : Result → Behaviour Value
  | .values vs => .returns vs
  | .trap => .traps

@[simp] theorem Result.toBehaviour_values (vs : List Value) :
    (Result.values vs).toBehaviour = .returns vs := rfl

@[simp] theorem Result.toBehaviour_trap : Result.trap.toBehaviour = .traps := rfl

/-! ## Range

V1 and Lime1 have neither exceptions nor a divergent result. -/

/-- Neither V1 nor Lime1 has exception handling, so no result is an escaping
exception. -/
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

/-- `Result.toBehaviour` loses nothing: it is injective. -/
theorem Result.toBehaviour_injective : Function.Injective Result.toBehaviour := by
  intro r r' h
  cases r <;> cases r' <;> simp_all

@[simp] theorem Result.values?_toBehaviour (r : Result) :
    r.toBehaviour.values? = match r with | .values vs => some vs | .trap => none := by
  cases r <;> rfl
