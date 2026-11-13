module

public import Silmaril.Wasm.Det.Game.Defs
public import Silmaril.Wasm.Det.Core.Defs
public import Silmaril.Wasm.Game.Strategy.Defs

/-!
# Determinism of instance strategies: definitions

The game reading of `Silmaril.Wasm.Det.Core` for a scalar Core 3.0 instance
(`Silmaril.Wasm.Game.ScalarInstance`) and its strategy `I.strategy P s`:

* `wasmTraps ts`: the trap answers of the interface `ifaceSig ts` are the answers
  `Answer.trap` (exceptions are not traps);
* `I.entry`: the entry function addresses of the instance, the addresses of its exports;
* `I.ExportsTyped s`: every export address of `s` holds a function of the declared export
  type (the `export_type` field of `ScalarInstance.WellFormed`); it makes every export call
  of the game an `InvokeOk` invocation at every call state;
* `TypedTrace I tr` and `GameOut I f o`: the import traces and outputs of
  `Silmaril.Wasm.Det.Core.Runs` that are visible as plays of the game (typed import calls answered
  by game answers; outputs read as moves);
* `ObsModule P I s₀`: the observable part of `DetModule`: output agreement of export calls at
  every call state reached by trap-free activations, against typed traces; `ObsStateless P I s₀`
  likewise across any two call states reached by activations.

New definitions (no source file).
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation

/-- The trap answers of a scalar interface. -/
def wasmTraps (ts : List FnType) : Traps (ifaceSig ts) := fun _ v => v = .trap

/-- The entry function addresses of an instance: its export addresses. -/
def entry (I : ScalarInstance) : Nat → Prop := fun a => ∃ j, I.addr j = a

/-- Every export address holds a function of the declared export type. -/
def ExportsTyped (I : ScalarInstance) (s : Store Nat) : Prop :=
  ∀ j, ∃ fi : FuncInst Nat, s.funcs[I.addr j]? = some fi ∧ Expand fi.type (I.exports.get j).toComp

/-- The calls of a trace are typed import calls of `I`, answered by game answers: the traces a
game environment can produce. -/
def TypedTrace (I : ScalarInstance) (tr : List Det.Core.Call) : Prop :=
  ∀ x ∈ tr, ∃ (e : I.E.Op) (v : I.E.Ar e), I.importOp? x.host x.args = some e ∧ x.ans = v.toResult

/-- Outputs of export call `f` that the game can play: typed import calls, and results read as
answers of the export type. -/
def GameOut (I : ScalarInstance) (f : I.F.Op) : Det.Core.Out → Prop
  | .call h args => ∃ e, I.importOp? h args = some e
  | .ret r => ∃ v, Answer.ofResult? (I.exports.get f.1) r = some v

/-- **Observable determinism of an instance from `s₀`**: at every call state `s` reached from
`s₀` by complete activations in which no export call trapped, two Core runs of an export
invocation against the same typed trace that reach non-trapping stops visible in the game have
the same output. This is the part of `DetModule` that the game observes: stores are not
compared, and call states after traps are not constrained. -/
def ObsModule (P : Silmaril.Wasm.Numerics.Profile) (I : ScalarInstance) (s₀ : Store Nat) :
    Prop :=
  ∀ c s, I.Activation P s₀ c s → TrapFree (wasmTraps I.exports) c →
    ∀ (f : I.F.Op) (tr : List Det.Core.Call) (d₁ d₂ : Config Nat) (o₁ o₂ : Det.Core.Out),
      TypedTrace I tr → Det.Core.Runs P (invoke s (I.addr f.1) f.2.1) tr d₁ →
      Det.Core.Runs P (invoke s (I.addr f.1) f.2.1) tr d₂ → Det.Core.OutAt d₁ o₁ →
      Det.Core.OutAt d₂ o₂ → GameOut I f o₁ → GameOut I f o₂ → o₁ = o₂

/-- **Observable statelessness of an instance from `s₀`**: at any two call states reached from
`s₀` by complete activations (traps allowed in them), Core runs of the same export invocation
against the same typed trace that reach non-trapping stops visible in the game have the same
output. -/
def ObsStateless (P : Silmaril.Wasm.Numerics.Profile) (I : ScalarInstance) (s₀ : Store Nat) :
    Prop :=
  ∀ c₁ s₁ c₂ s₂, I.Activation P s₀ c₁ s₁ → I.Activation P s₀ c₂ s₂ →
    ∀ (f : I.F.Op) (tr : List Det.Core.Call) (d₁ d₂ : Config Nat) (o₁ o₂ : Det.Core.Out),
      TypedTrace I tr → Det.Core.Runs P (invoke s₁ (I.addr f.1) f.2.1) tr d₁ →
      Det.Core.Runs P (invoke s₂ (I.addr f.1) f.2.1) tr d₂ → Det.Core.OutAt d₁ o₁ →
      Det.Core.OutAt d₂ o₂ → GameOut I f o₁ → GameOut I f o₂ → o₁ = o₂

end Silmaril.Wasm.Det.Game
