module

public import Silmaril.Wasm.Det.Shared.Defs

/-!
# Statelessness against hosts whose returned stores differ between runs

`Silmaril.Wasm.Det.Shared.ObsAgreeS` compares two runs resumed in the **same** returned stores. In
the shared world of a static link the consumer's host is the provider, which runs in the shared
store: from two different call states it returns different stores even when its answers agree.
These notions compare runs whose traces agree on the calls and the answers only.

* `SCall.call x`: the call and answer of `x`, without the returned store.
* `ObsAgreeW P A c₁ c₂`: two runs, from `c₁` and from `c₂`, against admissible store-writing
  hosts (`A`), whose traces agree on calls and answers (returned stores may differ) and that both
  reach a non-trapping stop have the same output.
* `StatelessModuleW P A S Entry`: every entry function satisfies `ObsAgreeW` between any two call
  states of `S`, on any arguments.

New definitions (no source file).
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Shared

open Silmaril.Wasm.Det.Core Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- The call and the answer of an answered call, without the returned store. -/
def SCall.call (x : SCall) : Nat × List Val × Result := (x.host, x.args, x.ans)

/-- **Output agreement against hosts whose returned stores may differ**: two runs whose traces
agree on calls and answers and that both reach a non-trapping stop have the same output. -/
def ObsAgreeW (P : Profile) (A : Store Nat → Store Nat → Prop) (c₁ c₂ : Config Nat) : Prop :=
  ∀ tr₁ tr₂ d₁ d₂ o₁ o₂, tr₁.map SCall.call = tr₂.map SCall.call → RunsS P A c₁ tr₁ d₁ →
    RunsS P A c₂ tr₂ d₂ → OutAt d₁ o₁ → OutAt d₂ o₂ → o₁ = o₂

/-- **Per module**: every entry function agrees between any two call states of `S`, on any
arguments, against hosts whose returned stores may differ. -/
def StatelessModuleW (P : Profile) (A : Store Nat → Store Nat → Prop) (S : Store Nat → Prop)
    (Entry : Nat → Prop) : Prop :=
  ∀ a, Entry a → ∀ s₁ s₂ vs, S s₁ → S s₂ → ObsAgreeW P A (invoke s₁ a vs) (invoke s₂ a vs)

end Silmaril.Wasm.Det.Shared
