module

public import Silmaril.Wasm.Replace.Thms

/-!
# The replacement congruence over a reachability predicate (Wasm 1.0): definitions

`Silmaril.Wasm.Replace` restricts silmaril-lean's call-boundary hypothesis `CallSim` to the stores
of a predicate `Reach`. This topic proves the congruence over that restriction: replacing the
function at `a` by the one at `b` gives an equivalent module, from `CallSimOn Reach`,
`StepClosed host Reach`, `HostRespectsReplace host a b` and the type side condition below.

* `SameFuncTypeOn Reach a b`: `SameFuncType s a b` at every `s` with `Reach s`. It is needed at
  every reachable store, not only the initial one, because `call_indirect` checks the type of
  the instance it calls before any invocation of `a` happens, and a host may write the function
  table during a run.

The theorems are in `Silmaril.Wasm.Replace.Congruence.Thms`. Ported from
an earlier development `Silmaril/Wasm/Equiv/Congruence.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.Replace

open Silmaril.Wasm.V1.Execution
open Silmaril.Wasm.Execution.Runtime

variable {H : Type}

/-- The type side condition `SameFuncType`, at the stores satisfying `Reach`. -/
def SameFuncTypeOn (Reach : Store H → Prop) (a b : FuncAddr) : Prop :=
  ∀ s : Store H, Reach s → SameFuncType s a b

end Silmaril.Wasm.Replace
