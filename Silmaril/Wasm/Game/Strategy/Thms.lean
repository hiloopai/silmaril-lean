module

public import Silmaril.Wasm.Game.Strategy.Defs
public import Silmaril.Games.LTS.Thms
import Silmaril.Proofs.Wasm.Game.Strategy.Basic

/-!
# The strategy of a scalar instance: theorems (M1)

* `mem_strategy_iff`: the plays of `I.strategy P s` are exactly the runs of
  the hidden-state transition system from `idle s` (no completion is needed:
  these runs are already legal, prefix closed and receptive), so `I.lts P s`
  denotes the strategy (`denotes`).
* The strategy is defined for an **arbitrary** silmaril profile `P`: host-free
  runs are relational (`Reach P`), so `I.strategy P s` is a nondeterministic
  strategy (a set of plays in which Proponent may have several next moves:
  NaN payloads, relaxed operators, `memory.grow`/`table.grow` failure).
  It is monotone in the profile (`strategy_mono`); in particular the
  deterministic strategy refines the spec one
  (`strategy_profile_le_spec`).
* `strategy_deterministic` (deterministic profiles `profile o` only):
  Proponent's next move is unique (from determinism of the deterministic
  profile up to bubbling). It fails for general `P`.
* Agreement with Core reduction (`ask_ans_iff`, `ask_call_iff`): the instance
  answers an export call `f` with `w` without calling an import exactly when
  the host-free Core run of `$invoke(addr f, args)` reaches a result read as
  `w`; it calls the import `e` first exactly when that run reaches a host-call
  redex denoting `e`.
* Persistence: after a complete activation ending in store `s'`, the strategy
  continues with the strategy from `s'` (`append_mem_of`, every profile); for
  `profile o` the store is determined by the play and the strategy continues
  *exactly* as the strategy from `s'` (`append_mem_iff`). The whole store
  persists, the thread does not.

Proofs: `Silmaril.Proofs.Wasm.Game.Strategy.Basic`.
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.ScalarInstance

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

variable {I : ScalarInstance}

/-- The plays of the strategy are the runs of the transition system. -/
theorem mem_strategy_iff {P : Profile} {s : Store Nat} {p : List (Move I.E I.F)} :
    p ∈ I.strategy P s ↔ ∃ q, I.Path P (.idle s) p q :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.mem_strategy_iff

/-- The transition system of the instance denotes its strategy. -/
theorem denotes (P : Profile) (s : Store Nat) : (I.lts P s).Denotes (I.strategy P s) :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.denotes P s

/-- The strategy is monotone in the profile: if every host-free step of `P` is one of `Q`,
then every play under `P` is a play under `Q`. -/
theorem strategy_mono {P Q : Profile}
    (hPQ : ∀ c c' : Config Nat, Step P Det.noHost c c' → Step Q Det.noHost c c')
    (s : Store Nat) : I.strategy P s ≤ I.strategy Q s :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.strategy_mono hPQ s

/-- The strategy in a deterministic profile refines the strategy of the spec semantics
(`$ND = false`, default relaxed choices). -/
theorem strategy_profile_le_spec (o : GrowOracle) (s : Store Nat) :
    I.strategy (profile o) s ≤ I.strategy (Silmaril.Wasm.Numerics.Profile.spec false {}) s :=
  strategy_mono (fun _ _ h => Step.deterministic_refines h) s

/-- In a deterministic profile, the strategy of an instance is deterministic: Proponent's next
move is unique. -/
theorem strategy_deterministic {o : GrowOracle} {s : Store Nat} {p : List (Move I.E I.F)}
    {m m' : Move I.E I.F} (h : p ++ [m] ∈ I.strategy (profile o) s)
    (h' : p ++ [m'] ∈ I.strategy (profile o) s) (hm : m.IsP) : m = m' :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.strategy_deterministic h h' hm

/-- **Agreement (answers).** The instance answers the export call `f` with `w` before any
import call exactly when the host-free Core run of the invocation reaches a result read as
`w`. -/
theorem ask_ans_iff {P : Profile} {s : Store Nat} {f : I.F.Op} {w : I.F.Ar f} :
    [.inr (.ask f), .inr (.ans f w)] ∈ I.strategy P s ↔
      ∃ d r, Steps P (Det.noHost : HostSemantics Nat) (invoke s (I.addr f.1) f.2.1) d ∧
        d.code = r.toAdmin ∧ Answer.ofResult? (I.exports.get f.1) r = some w :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.ask_ans_iff

/-- **Agreement (calls).** The instance calls the import `e` first exactly when the
host-free Core run of the invocation reaches a host-call redex denoting `e`. -/
theorem ask_call_iff {P : Profile} {s : Store Nat} {f : I.F.Op} {e : I.E.Op} :
    [.inr (.ask f), .inl (.ask e)] ∈ I.strategy P s ↔
      ∃ d, Steps P (Det.noHost : HostSemantics Nat) (invoke s (I.addr f.1) f.2.1) d ∧
        ∃ E a h args, decompose? d.store d.code = some (E, a, h, args) ∧
          I.importOp? h args = some e :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.ask_call_iff

/-- **Persistence, every profile.** After a complete activation `c` from `s` ending in
`s'`, every play from `s'` continues `c`. -/
theorem append_mem_of {P : Profile} {s s' : Store Nat} {c p : List (Move I.E I.F)}
    (hc : I.Activation P s c s') (hp : p ∈ I.strategy P s') : c ++ p ∈ I.strategy P s := by
  rw [mem_strategy_iff] at hp ⊢
  exact Silmaril.Proofs.Wasm.Game.ScalarInstance.append_mem_plays_of hc hp

/-- In a deterministic profile, the store after an activation is determined by the store
before and the play. -/
theorem activation_functional {o : GrowOracle} {s s₁ s₂ : Store Nat}
    {c : List (Move I.E I.F)} (h₁ : I.Activation (profile o) s c s₁)
    (h₂ : I.Activation (profile o) s c s₂) : s₁ = s₂ :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.activation_functional h₁ h₂

/-- **Persistence, deterministic profiles.** After a complete activation `c` from `s` ending
in `s'`, the strategy continues exactly as the strategy from `s'`. -/
theorem append_mem_iff {o : GrowOracle} {s s' : Store Nat} {c p : List (Move I.E I.F)}
    (hc : I.Activation (profile o) s c s') :
    c ++ p ∈ I.strategy (profile o) s ↔ p ∈ I.strategy (profile o) s' := by
  rw [mem_strategy_iff, mem_strategy_iff]
  exact Silmaril.Proofs.Wasm.Game.ScalarInstance.append_mem_plays_iff hc

end Silmaril.Wasm.Game.ScalarInstance
