module

public import Silmaril.Wasm.Abstract.HostClosingInf.Defs

/-!
# The exact-log commuting square for host calls (stage H2): definitions

The observations of an invocation `invoke s a vs` against a Core 3.0 host `host`, each with
**exactly** the host-event log it makes, on two sides:

* `FullObs H`: a finished end after a log (`done`); a pending host call after a log, with no
  host outcome (`blocked`) or one the host diverges on (`hostDiv`); host-free divergence after a
  log (`div`); a productive run, infinitely many answered host calls (`prod`);
* `NatObs host s a vs`: the native side, host-independent apart from the filter
  `coreHostRel host` on the answers: finished behaviours of `wasmEvFun`, pending calls of
  `wasmEvPend`, divergence of `wasmEvFunD` and productive runs of `wasmEvInfN`;
* `CoreObsL P host s a vs`: the Core side, labelled runs (`EvRun`, `CoreInf`) with exactly the
  log: to values in the empty frame, to a trap in some store (`End.trap` carries none), to a
  configuration at the host call (`decompose?`), or to host-free divergence. A thrown exception
  and `End.div` are no finished Core end.

Theorems in `Silmaril.Wasm.Abstract.HostSquare.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **What a run of an invocation against a host shows**, with its exact host-event log. -/
inductive FullObs (H : Type) where
  /-- A finished end after the host calls `cs`. -/
  | done (cs : List (Call (wasmHostSig H))) (e : End (Store H) (List Val ⊕ Nat))
  /-- The pending host call `m` after the host calls `cs`, with no host outcome. -/
  | blocked (cs : List (Call (wasmHostSig H))) (m : (wasmHostSig H).Op)
  /-- The pending host call `m` after the host calls `cs`, on which the host diverges. -/
  | hostDiv (cs : List (Call (wasmHostSig H))) (m : (wasmHostSig H).Op)
  /-- Host-free divergence after the host calls `cs`. -/
  | div (cs : List (Call (wasmHostSig H)))
  /-- A productive run: infinitely many answered host calls. -/
  | prod (ω : Nat → Call (wasmHostSig H))

/-- **The native observations**: the logged native semantics, its answers filtered by the
host. -/
def NatObs (host : HostSemantics H) (s : Store H) (a : Nat) (vs : List Val) :
    FullObs H → Prop
  | .done cs e => (cs, e) ∈ wasmEvFun s (a, vs) ∧ (coreHostRel host).Consistent cs
  | .blocked cs m => (cs, m) ∈ wasmEvPend s (a, vs) ∧ (coreHostRel host).Consistent cs ∧
      ∀ ans, ¬ coreHostRel host m ans
  | .hostDiv cs m => (cs, m) ∈ wasmEvPend s (a, vs) ∧ (coreHostRel host).Consistent cs ∧
      coreHostRel host m .diverge
  | .div cs => (cs, .div) ∈ wasmEvFunD s (a, vs) ∧ (coreHostRel host).Consistent cs
  | .prod ω => ω ∈ hostObsInf (coreHostRel host) wasmEvInfN s (a, vs)

/-- **The Core observations**, at exactly their log. -/
def CoreObsL (P : Numerics.Profile) (host : HostSemantics H) (s : Store H) (a : Nat)
    (vs : List Val) : FullObs H → Prop
  | .done cs (.ret (.inl ws) s₂) => EvRun P host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩
  | .done cs .trap => ∃ s₂, EvRun P host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩
  | .done _ _ => False
  | .blocked cs (hh, s', us) => ∃ (c : Config H) (E : SingleThreaded.Ctx) (a' : Nat),
      EvRun P host (invoke s a vs) cs c ∧
      SingleThreaded.decompose? c.store c.code = some (E, a', hh, us) ∧ c.store = s' ∧
      ∀ o, ¬ host hh s' us o
  | .hostDiv cs (hh, s', us) => ∃ (c : Config H) (E : SingleThreaded.Ctx) (a' : Nat),
      EvRun P host (invoke s a vs) cs c ∧
      SingleThreaded.decompose? c.store c.code = some (E, a', hh, us) ∧ c.store = s' ∧
      host hh s' us .diverged
  | .div cs => ∃ c' : Config H, EvRun P host (invoke s a vs) cs c' ∧
      Diverges P (fun _ _ _ _ => False) c'
  | .prod ω => CoreInf P host (invoke s a vs) ω

end Silmaril.Wasm.Abstract
