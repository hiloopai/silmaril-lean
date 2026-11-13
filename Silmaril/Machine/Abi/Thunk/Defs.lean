module

public import Silmaril.Machine.Abi.Defs
/-! # Cross-ABI thunks as forward simulations

`Convention.Thunk.Correct` (in `Abi.Defs`) asks every caller-side observation of
the adapted return to be a callee-side observation, *for every callee final
state*. That is too strong for real adapters. A System V caller does not care
whether an `ms_abi` callee restored RSI, but `B.Observe … (some r)` requires it.
So no adapter that leaves RSI alone can be `Correct`, including the one GCC
emits.

`Thunk.Simulates` asks only for a forward simulation of *well-behaved* callee
runs, and it can be stated relative to:

* a caller-side assumption `Room` on the entry state (for example, writable
  stack below RSP for the adapter's own frame). Translated value-level contracts
  do not provide it, so the composite contract is `within`
  the assumption;
* a callee-side guarantee `Guar` relating callee entry and final states (for
  example, that the callee left the adapter's frame and return address alone).
  This is a frame property, which value-level contracts do not state either.

`Simulates.sound` (in `Thms`) is the composition theorem. If the callee
satisfies `B`'s translation of a *strict* C contract (one that never accepts an
ABI-breaking return) and provides `Guar`, then the adapted callee satisfies
`A`'s translation of the same C contract on every entry state that meets `Room`.
`Correct.simulates` shows that `Correct` thunks simulate with trivial `Room` and
`Guar`.
-/

@[expose] public section
namespace Silmaril.Machine.Abi

open Silmaril.Logic.Institution.Bridges

/-- Strengthen a contract's precondition by an assumption on its inputs. -/
def within {Input Obs : Type} (c : Contracts.Contract Input Obs)
    (assume : Input → Prop) : Contracts.Contract Input Obs where
  pre input := c.pre input ∧ assume input
  post := c.post

namespace Convention

variable {V : Vocab} {St D : Type}

/-- A C contract is strict when, on admitted arguments, it rejects the
observation `none` of an ABI-breaking or undecodable return. -/
def Strict {p : V.Proto} (c : Contracts.Contract (V.Args p) (Option (V.Ret p))) : Prop :=
  ∀ a, c.pre a → ¬ c.post a none

/-- A callee final state is well behaved under `B`: it returns by the ABI's
discipline with a decodable result. -/
def Proper (B : Convention V St D) (p : V.Proto) (s₁ s₂ : St) : Prop :=
  B.Return p s₁ s₂ ∧ ∃ r, B.ResultAt p s₁ s₂ r

/-- A thunk from caller convention `A` to callee convention `B` simulates the
callee: on `A`-entry states meeting `room`, it builds `B`-entry states, and it
turns every well-behaved `B` return that meets `guar` into an `A` return whose
results are results of the callee. -/
structure Thunk.Simulates {A B : Convention V St D} {p : V.Proto} (t : Thunk A B p)
    (room : St → Prop) (guar : St → St → Prop) : Prop where
  enter_entry : ∀ a s, A.Entry p a s → room s → ∀ s₁ ∈ t.enter s, B.Entry p a s₁
  enter_progress : ∀ a s, A.Entry p a s → room s → (t.enter s).Nonempty
  leave_progress : ∀ a s, A.Entry p a s → room s → ∀ s₁ ∈ t.enter s, ∀ s₂,
    B.Proper p s₁ s₂ → guar s₁ s₂ → (t.leave s s₂).Nonempty
  leave_return : ∀ a s, A.Entry p a s → room s → ∀ s₁ ∈ t.enter s, ∀ s₂,
    B.Proper p s₁ s₂ → guar s₁ s₂ → ∀ s₃ ∈ t.leave s s₂, A.Return p s s₃
  leave_result : ∀ a s, A.Entry p a s → room s → ∀ s₁ ∈ t.enter s, ∀ s₂,
    B.Proper p s₁ s₂ → guar s₁ s₂ → ∀ s₃ ∈ t.leave s s₂,
      (∃ r, A.ResultAt p s s₃ r) ∧ ∀ r, A.ResultAt p s s₃ r → B.ResultAt p s₁ s₂ r

/-- A callee relation provides `guar` on every admitted `B`-entry. -/
def Guarantees (B : Convention V St D) (p : V.Proto)
    (c : Contracts.Contract (V.Args p) (Option (V.Ret p)))
    (model : Contracts.Model St St) (guar : St → St → Prop) : Prop :=
  ∀ a s₁, B.Entry p a s₁ → c.pre a → ∀ s₂ ∈ model s₁, guar s₁ s₂

end Convention

end Silmaril.Machine.Abi
