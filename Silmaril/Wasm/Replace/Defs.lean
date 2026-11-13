module

public import Silmaril.Wasm.Equiv.Module

/-!
# Function replacement on reachable stores (Wasm 1.0): definitions

silmaril-lean's `Silmaril.Wasm.Equiv.Module` states the replacement congruence
`V1.Execution.moduleEquiv_replace` with the call-boundary hypothesis `CallSim host a b s`
quantified over **every** store `s`. That hypothesis is refuted for `a ≠ b` by the same file's
`eq_of_forall_callSim`, so the congruence is true but vacuous. This topic restricts the
quantifier to a store predicate `Reach`, as the source's issue an earlier issue asks
("store states reachable in `M`").

* `Reachable host s₀ m imports`: the store `prepare?` hands to the start function, closed under
  one reduction step from any frame and any code. Closing over arbitrary configurations makes it
  closed under reduction by construction and over-approximates the stores a program can
  produce, so a `CallSimOn` hypothesis over it is stronger, hence sound.
* `StepClosed host Reach`: `Reach` is preserved by every step.
* `HostRespectsReplace host a b`: the host relation commutes with `Store.replaceFunc a b`, in
  both directions and for divergence. `CallSim` only constrains runs out of `invoke s a vs`,
  but a host function may read or write the whole store; this is the missing assumption.
* `CallSimOn Reach host a b`: `CallSim host a b s` at every `s` with `Reach s`.

The theorems are in `Silmaril.Wasm.Replace.Thms`. Ported from an earlier development
`Silmaril/Wasm/Equiv/Reach.lean`. The congruence over `CallSimOn`
(`Silmaril/Wasm/Equiv/Congruence.lean`) is `Silmaril.Wasm.Replace.Congruence`, and its
non-vacuity example is `Silmaril.Wasm.Replace.Example`.
-/

@[expose] public section

namespace Silmaril.Wasm.Replace

open Silmaril.Wasm.V1.Execution
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

variable {H : Type}

/-- The stores reachable by instantiating `m` against `s₀` and running: the store `prepare?`
produces, closed under one reduction step at any frame and any code. -/
inductive Reachable (host : HostSemantics H) (s₀ : Store H) (m : Silmaril.Wasm.V1.Module)
    (imports : List ExternVal) : Store H → Prop where
  /-- The store `prepare?` hands to the start function. -/
  | prepared {p : Prepared H} (h : prepare? s₀ m imports = some p) :
      Reachable host s₀ m imports p.store
  /-- Closure under one reduction, at any frame and any code. -/
  | step {s s' : Store H} {f f' : Frame} {X X' : List Admin}
      (hs : Reachable host s₀ m imports s) (hstep : Step host ⟨s, f, X⟩ ⟨s', f', X'⟩) :
      Reachable host s₀ m imports s'

/-- A store predicate is closed under reduction. -/
def StepClosed (host : HostSemantics H) (Reach : Store H → Prop) : Prop :=
  ∀ ⦃s s' : Store H⦄ ⦃f f' : Frame⦄ ⦃X X' : List Admin⦄,
    Reach s → Step host ⟨s, f, X⟩ ⟨s', f', X'⟩ → Reach s'

/-- The host neither observes nor modifies the function table at `a`: host returns transport
forwards and backwards along `Store.replaceFunc a b`, and divergence agrees. -/
structure HostRespectsReplace (host : HostSemantics H) (a b : FuncAddr) : Prop where
  /-- A host return transports forwards, replacing the final store too. -/
  forward : ∀ (fn : H) (s s' : Store H) (args : List Runtime.Value) (r : Runtime.Result),
    host fn s args (.returned s' r) →
      host fn (s.replaceFunc a b) args (.returned (s'.replaceFunc a b) r)
  /-- A host return after the replacement comes from one before it. -/
  backward : ∀ (fn : H) (s t' : Store H) (args : List Runtime.Value) (r : Runtime.Result),
    host fn (s.replaceFunc a b) args (.returned t' r) →
      ∃ s' : Store H, t' = s'.replaceFunc a b ∧ host fn s args (.returned s' r)
  /-- Host divergence is unaffected. -/
  diverges : ∀ (fn : H) (s : Store H) (args : List Runtime.Value),
    host fn s args .diverged ↔ host fn (s.replaceFunc a b) args .diverged

/-- The call-boundary hypothesis `CallSim`, at the stores satisfying `Reach` only. -/
def CallSimOn (Reach : Store H → Prop) (host : HostSemantics H) (a b : FuncAddr) : Prop :=
  ∀ s₁ : Store H, Reach s₁ → CallSim host a b s₁

end Silmaril.Wasm.Replace
