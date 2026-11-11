module

public import Silmaril.Wasm.Game.Env.Defs
import Silmaril.Proofs.Wasm.Game.Env.Basic

/-!
# Environments and strategy-definable hosts: theorems

* `Env.mem_strategy_iff`: the plays of `K.strategy` are the event lists
  agreeing with `K`, as upper moves.
* `Env.mem_comp_iff`: the plays of the closed program `K.strategy ≫ σ` are the
  upper projections of the plays of `σ` whose lower projection agrees with
  `K` (the empty lower signature makes the composite hide exactly the import
  interface).
* `isStrategyHost_iff`: the strategy-definable hosts are exactly the
  store-preserving hosts given by a partial answer function on valid import
  calls, diverging where it is undefined.
* `hostOf_nil` (no imports: the empty host), `hostOf_silent` (the silent
  environment: the diverging host on valid import calls).

Proofs: `Silmaril.Proofs.Wasm.Game.Env.Basic`.
-/

public section

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core

namespace Env

variable {E : Sig.{0}} {K : Env E}

/-- An environment answers each question at most once. -/
theorem Answers.unique {e : E.Op} {w w' : E.Ar e} (h : K.Answers e w) (h' : K.Answers e w') :
    w = w' :=
  Silmaril.Proofs.Wasm.Game.Env.Answers.unique h h'

/-- The plays of the strategy of an environment. -/
theorem mem_strategy_iff {p : List (Move Sig.empty E)} :
    p ∈ K.strategy ↔ ∃ u, K.Agrees u ∧ p = u.map .inr :=
  Silmaril.Proofs.Wasm.Game.Env.mem_strategy_iff

/-- **Composition with an environment.** -/
theorem mem_comp_iff {F : Sig.{0}} {σ : Strategy E F} {p : List (Move Sig.empty F)} :
    p ∈ K.strategy.comp σ ↔ ∃ t ∈ σ, K.Agrees (lower t) ∧ p = (upper t).map .inr :=
  Silmaril.Proofs.Wasm.Game.Env.mem_comp_iff

/-- Answers in agreeing events are answers of the environment. -/
theorem Agrees.answers {u : List (Ev E)} (h : K.Agrees u) {e : E.Op} {w : E.Ar e}
    (hm : (Ev.ans e w : Ev E) ∈ u) : K.Answers e w :=
  Silmaril.Proofs.Wasm.Game.Env.Agrees.answers h hm

end Env

/-- The induced host, read through the answer function. -/
theorem hostOf_iff (ts : List FnType) (K : Env (ifaceSig ts)) (h : Nat) (s : Store Nat)
    (args : List Val) (out : HostOutcome Nat) :
    hostOf ts K h s args out ↔ ∃ e, ifaceOp? ts h args = some e ∧
      match K e with
      | some w => out = .returned s (Answer.toResult (ft := ts.get e.1) w)
      | none => out = .diverged :=
  Silmaril.Proofs.Wasm.Game.hostOf_iff ts K h s args out

/-- **Strategy-definable hosts** are exactly the store-preserving hosts given by a partial
answer function on valid import calls, diverging where it is undefined. -/
theorem isStrategyHost_iff (ts : List FnType) (host : HostSemantics Nat) :
    IsStrategyHost ts host ↔
      ∃ ans : (e : (ifaceSig ts).Op) → Option ((ifaceSig ts).Ar e),
        ∀ h s args out, host h s args out ↔ ∃ e, ifaceOp? ts h args = some e ∧
          match ans e with
          | some w => out = .returned s (Answer.toResult (ft := ts.get e.1) w)
          | none => out = .diverged :=
  Silmaril.Proofs.Wasm.Game.isStrategyHost_iff ts host

/-- With no imports the induced host is the empty host. -/
theorem hostOf_nil (K : Env (ifaceSig [])) :
    hostOf [] K = (fun _ _ _ _ => False : HostSemantics Nat) :=
  Silmaril.Proofs.Wasm.Game.hostOf_nil K

/-- The silent environment induces the diverging host on valid import calls. -/
theorem hostOf_silent (ts : List FnType) (h : Nat) (s : Store Nat) (args : List Val)
    (out : HostOutcome Nat) :
    hostOf ts (Env.silent _) h s args out ↔ (ifaceOp? ts h args).isSome ∧ divHost h s args out :=
  Silmaril.Proofs.Wasm.Game.hostOf_silent ts h s args out

/-- With no imports every environment throws below every bound. -/
theorem throwsBelow_nil (K : Env (ifaceSig [])) (n : Nat) : ThrowsBelow K n :=
  Silmaril.Proofs.Wasm.Game.throwsBelow_nil K n

/-- The silent environment never throws. -/
theorem throwsBelow_silent (ts : List FnType) (n : Nat) :
    ThrowsBelow (Env.silent (ifaceSig ts)) n :=
  Silmaril.Proofs.Wasm.Game.throwsBelow_silent ts n

end Silmaril.Wasm.Game
