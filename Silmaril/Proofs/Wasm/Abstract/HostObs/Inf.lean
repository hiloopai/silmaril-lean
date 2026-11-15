module

public import Silmaril.Wasm.Abstract.HostObs.Defs
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Games.Abstract.HostRunInf.Thms

/-!
# Productive runs of invocations against a relational host (proofs)

`wasmEvInf P s (a, vs)`: the productive runs of an invocation, host-independently: Core runs
under the universal host `anyHost` (every answer and divergence allowed), cut at their host
events (`CoreInf`). One coherent run witnesses each stream.

`wasmEvInf_hostObsInf`: **the productive observations against a host are exactly its
productive Core runs**: `ω ∈ hostObsInf (coreHostRel host) (wasmEvInf P) s (a, vs)` iff
`CoreInf P host (invoke s a vs) ω`. Stutters the universal host allows but `host` does not are
removed (they leave the configuration unchanged), and answered events are allowed by `host`
exactly when they are consistent.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostObs

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- A host step labelled with a host's event is one with the universal host. -/
theorem hEvStep_any {c c' : Config H} {e : Option (Call (wasmHostSig H))}
    (h : HEvStep P host c e c') : HEvStep P anyHost c e c' := by
  cases e with
  | none =>
    rcases h with h | ⟨rfl, E, a, hh, us, hd, -⟩
    · exact .inl h
    · exact .inr ⟨rfl, E, a, hh, us, hd, trivial⟩
  | some e =>
    obtain ⟨E, a, hd, hs, -, hc⟩ := h
    exact ⟨E, a, hd, hs, trivial, hc⟩

/-- An answered step with the universal host whose event the host allows is a host step. -/
theorem hEvStep_of_any {c c' : Config H} {e : Call (wasmHostSig H)}
    (h : HEvStep P anyHost c (some e) c') (he : coreHostRel host e.1 (.answer e.2)) :
    HEvStep P host c (some e) c' := by
  obtain ⟨E, a, hd, hs, -, hc⟩ := h
  exact ⟨E, a, hd, hs, by simpa [coreHostRel, hs] using he, hc⟩

/-- Event-free runs with the universal host reach the same configurations without stutters,
so with any host. -/
theorem silent_of_any {c c' : Config H}
    (h : Relation.ReflTransGen (fun a b => HEvStep P anyHost a none b) c c') :
    Relation.ReflTransGen (fun a b => HEvStep P host a none b) c c' := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    rcases hs with hs | ⟨rfl, -⟩
    · exact ih.tail (.inl hs)
    · exact ih

theorem silent_any {c c' : Config H}
    (h : Relation.ReflTransGen (fun a b => HEvStep P host a none b) c c') :
    Relation.ReflTransGen (fun a b => HEvStep P anyHost a none b) c c' := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (hEvStep_any hs)

theorem coreInf_any {c : Config H} {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf P host c ω) : CoreInf P anyHost c ω := by
  obtain ⟨g, hg0, hg⟩ := h
  refine ⟨g, hg0, fun n => ?_⟩
  obtain ⟨c₁, hr, he⟩ := hg n
  exact ⟨c₁, silent_any hr, hEvStep_any he⟩

theorem coreInf_of_any {c : Config H} {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf P anyHost c ω) (hc : ∀ n, coreHostRel host (ω n).1 (.answer (ω n).2)) :
    CoreInf P host c ω := by
  obtain ⟨g, hg0, hg⟩ := h
  refine ⟨g, hg0, fun n => ?_⟩
  obtain ⟨c₁, hr, he⟩ := hg n
  exact ⟨c₁, silent_of_any hr, hEvStep_of_any he (hc n)⟩

/-- **The productive observations against a host are its productive Core runs.** -/
theorem wasmEvInf_hostObsInf {s : Store H} {a : Nat} {vs : List Val}
    {ω : Nat → Call (wasmHostSig H)} :
    ω ∈ hostObsInf (coreHostRel host) (wasmEvInf P) s (a, vs) ↔
      CoreInf P host (invoke s a vs) ω :=
  ⟨fun h => coreInf_of_any h.1 h.2, fun h => ⟨coreInf_any h, coreInf_consistent h⟩⟩

end Silmaril.Proofs.Wasm.Abstract.HostObs
