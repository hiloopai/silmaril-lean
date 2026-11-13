module

public import Silmaril.Wasm.Det.Shared.Defs

/-!
# Statelessness under store-writing hosts: definitions

The store-writing oracle of `Silmaril.Wasm.Det.Shared` (`RunsS`: each import call is resumed with
its answer in the store the host returned) applied to statelessness
(`Silmaril.Wasm.Det.Core.StatelessFn`).

* `ObsAgreeS P A c₁ c₂`: two runs, from `c₁` and from `c₂`, with the same calls, answers and
  returned stores (each admissible, `A`, for the store at its call) that both reach a
  non-trapping stop have the same output. Stores are not compared.
* `StatelessFnS P A S a`: typed invocations of `a` on the same arguments from any two stores of
  `S` are `ObsAgreeS`.
* `StatelessModuleS P A S Entry`: every entry function is `StatelessFnS P A S`.

As for `DetModuleS`, the call states `S` are a parameter: a host writing the store may change
whatever the code reads between two calls, so the right `S` is a property of the code (for
example: every store holding its functions, or every store agreeing on the globals it reads).

New definitions (no source file).
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Shared

open Silmaril.Wasm.Det.Core Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- **Output agreement modulo traps and store-writing imports.** -/
def ObsAgreeS (P : Profile) (A : Store Nat → Store Nat → Prop) (c₁ c₂ : Config Nat) : Prop :=
  ∀ tr d₁ d₂ o₁ o₂, RunsS P A c₁ tr d₁ → RunsS P A c₂ tr d₂ → OutAt d₁ o₁ → OutAt d₂ o₂ →
    o₁ = o₂

/-- **Per function, statelessness under store-writing hosts**: typed invocations of `a` on the
same arguments in any two stores of `S` have the same non-trapping outputs, against the same
answers and returned stores. -/
def StatelessFnS (P : Profile) (A : Store Nat → Store Nat → Prop) (S : Store Nat → Prop)
    (a : Nat) : Prop :=
  ∀ s₁ s₂ vs, S s₁ → S s₂ → InvokeOk s₁ a vs → InvokeOk s₂ a vs →
    ObsAgreeS P A (invoke s₁ a vs) (invoke s₂ a vs)

/-- **Per module, statelessness under store-writing hosts**. -/
def StatelessModuleS (P : Profile) (A : Store Nat → Store Nat → Prop) (S : Store Nat → Prop)
    (Entry : Nat → Prop) : Prop :=
  ∀ a, Entry a → StatelessFnS P A S a

end Silmaril.Wasm.Det.Shared
