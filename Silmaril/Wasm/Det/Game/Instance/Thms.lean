module

public import Silmaril.Wasm.Det.Game.Instance.Defs
public import Silmaril.Wasm.Det.Game.Thms
public import Silmaril.Wasm.Det.Core.Thms
public import Silmaril.Wasm.Game.Strategy.Thms
import Silmaril.Proofs.Wasm.Det.Game.Instance
import Silmaril.Proofs.Wasm.Det.Game.InstanceObs

/-!
# Determinism of instance strategies: theorems

The run-based notions of `Silmaril.Wasm.Det.Core` give the game-level notions of
`Silmaril.Wasm.Det.Game` for the strategy `I.strategy P s₀` of a scalar instance, at every profile
`P`. Imports are Opponent moves: the environment's answers in a play are the shared oracle of
`Silmaril.Wasm.Det.Core.Runs`.

* `detMod_strategy`: if the module is `DetModule P (entry I) s₀`, its strategy is
  deterministic modulo traps: after a play in which no export call trapped, Proponent's next
  move (an import call with its arguments, or an export answer) is unique unless one of the
  candidates is a trap answer.
* `statelessMod_strategy`: if the module is `StatelessModule P (entry I) s₀`, its strategy is
  stateless modulo traps: after any two plays ending idle (traps allowed in them), the same
  trap-free continuation leads to the same next Proponent move up to traps.
* `strict_strategy`: every instance strategy is strict: after an import answers with a trap,
  the pending export call answers with a trap (Wasm cannot catch traps).

`ExportsTyped I s₀` (the `export_type` field of `ScalarInstance.WellFormed`) makes the game's
export calls typed invocations at every call state.

* `obsAgree_of_detMod` (**converse, first call**): if the strategy from `s₀` is deterministic
  modulo traps, then for every export `f`, two Core runs of the invocation from `s₀` against the
  same typed trace (`TypedTrace`, the traces a game environment can produce) that reach
  non-trapping stops visible in the game (`GameOut`) have the same output.

So, at the first call and against game environments, determinism of the strategy and output
determinism of the export calls coincide. The full converse (a deterministic strategy gives
`DetModule`) fails as stated: `DetModule` compares stores, which the game hides, and constrains
calls after traps, which `DetMod` does not.

* `obsModule_of_detMod` (**converse after earlier activations**): a deterministic strategy gives
  `ObsModule`, output agreement of export invocations at every call state reached by trap-free
  activations; `obsStateless_of_statelessMod`: a stateless strategy gives `ObsStateless`,
  output agreement across any two call states reached by activations. `obsModule_of_detModule`
  and `obsStateless_of_statelessModule` compose them with the forward direction.

Proofs: `Silmaril.Proofs.Wasm.Det.Game.{Instance,InstanceObs}` (and `Trapped` for strictness).
-/

public section

namespace Silmaril.Wasm.Det.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Det.Core Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {I : ScalarInstance} {P : Profile}

/-- Well-formed instances have typed exports. -/
theorem ExportsTyped.of_wellFormed {s : Store Nat} (hw : I.WellFormed s) : ExportsTyped I s :=
  hw.export_type

/-- **A deterministic module has a deterministic strategy, modulo traps** (every profile). -/
theorem detMod_strategy {s₀ : Store Nat} (hD : DetModule P (entry I) s₀)
    (ht : ExportsTyped I s₀) : DetMod (wasmTraps I.exports) (I.strategy P s₀) :=
  Silmaril.Proofs.Wasm.Det.Game.detMod_strategy hD ht

/-- **A stateless module has a stateless strategy, modulo traps** (every profile). -/
theorem statelessMod_strategy {s₀ : Store Nat} (hD : StatelessModule P (entry I) s₀)
    (ht : ExportsTyped I s₀) : StatelessMod (wasmTraps I.exports) (I.strategy P s₀) :=
  Silmaril.Proofs.Wasm.Det.Game.statelessMod_strategy hD ht

/-- **Instance strategies are trap-strict** (every profile, every store). -/
theorem strict_strategy (s₀ : Store Nat) :
    Strict (wasmTraps I.imports) (wasmTraps I.exports) (I.strategy P s₀) :=
  Silmaril.Proofs.Wasm.Det.Game.strict_strategy s₀

/-- **Converse at the first call: a deterministic strategy gives output agreement of every
export invocation against game environments** (every profile). -/
theorem obsAgree_of_detMod {s₀ : Store Nat} (hD : DetMod (wasmTraps I.exports) (I.strategy P s₀))
    (f : I.F.Op) {tr : List Call} {d₁ d₂ : Config Nat} {o₁ o₂ : Out} (htr : TypedTrace I tr)
    (h₁ : Runs P (invoke s₀ (I.addr f.1) f.2.1) tr d₁)
    (h₂ : Runs P (invoke s₀ (I.addr f.1) f.2.1) tr d₂) (ho₁ : OutAt d₁ o₁) (ho₂ : OutAt d₂ o₂)
    (hg₁ : GameOut I f o₁) (hg₂ : GameOut I f o₂) : o₁ = o₂ :=
  Silmaril.Proofs.Wasm.Det.Game.obsAgree_of_detMod hD f htr h₁ h₂ ho₁ ho₂ hg₁ hg₂

/-- **Characterisation at the first call**: for a module that is deterministic, its strategy is
deterministic, and the strategy's determinism gives back output agreement of every export
invocation from `s₀` against game environments. -/
theorem detModule_detMod_obsAgree {s₀ : Store Nat} (hD : DetModule P (entry I) s₀)
    (ht : ExportsTyped I s₀) :
    DetMod (wasmTraps I.exports) (I.strategy P s₀) ∧
      ∀ (f : I.F.Op) (tr : List Call) (d₁ d₂ : Config Nat) (o₁ o₂ : Out), TypedTrace I tr →
        Runs P (invoke s₀ (I.addr f.1) f.2.1) tr d₁ → Runs P (invoke s₀ (I.addr f.1) f.2.1) tr d₂ →
        OutAt d₁ o₁ → OutAt d₂ o₂ → GameOut I f o₁ → GameOut I f o₂ → o₁ = o₂ :=
  ⟨detMod_strategy hD ht, fun f _ _ _ _ _ htr h₁ h₂ ho₁ ho₂ hg₁ hg₂ =>
    obsAgree_of_detMod (detMod_strategy hD ht) f htr h₁ h₂ ho₁ ho₂ hg₁ hg₂⟩

/-- **Converse after earlier activations**: a deterministic strategy gives observable
determinism at every call state reached by trap-free activations (every profile). -/
theorem obsModule_of_detMod {s₀ : Store Nat}
    (hD : DetMod (wasmTraps I.exports) (I.strategy P s₀)) : ObsModule P I s₀ :=
  Silmaril.Proofs.Wasm.Det.Game.obsModule_of_detMod hD

/-- **Converse for statelessness**: a stateless strategy gives observable statelessness across
call states reached by activations (every profile). -/
theorem obsStateless_of_statelessMod {s₀ : Store Nat}
    (hD : StatelessMod (wasmTraps I.exports) (I.strategy P s₀)) : ObsStateless P I s₀ :=
  Silmaril.Proofs.Wasm.Det.Game.obsStateless_of_statelessMod hD

/-- A deterministic module is observably deterministic. -/
theorem obsModule_of_detModule {s₀ : Store Nat} (hD : DetModule P (entry I) s₀)
    (ht : ExportsTyped I s₀) : ObsModule P I s₀ :=
  obsModule_of_detMod (detMod_strategy hD ht)

/-- A stateless module is observably stateless. -/
theorem obsStateless_of_statelessModule {s₀ : Store Nat} (hD : StatelessModule P (entry I) s₀)
    (ht : ExportsTyped I s₀) : ObsStateless P I s₀ :=
  obsStateless_of_statelessMod (statelessMod_strategy hD ht)

end Silmaril.Wasm.Det.Game
