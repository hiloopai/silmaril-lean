module

public import Silmaril.Wasm.Component.Reference.LegalBoundaryRuns.Defs
public import Silmaril.Wasm.Component.Reference.LegalBoundary.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary.Machine
import Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.Twin

/-!
# A core activation that threw and the same activation trapped are twins (proofs)

On `core3P P`, with any profile, host readiness and dispatcher: the configuration running
`throwing a` and the one running `[.trap]` (same everything else) are `StepTwin`s; the rest of
the session call from either is exactly the trap, resuming from `resumeCfg m₀ (trapCfg m)`; and
neither has any infinite rest (divergence, infinite run with host events, quiet divergence, host
chatter).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Machine.StepDefs Silmaril.Wasm.Component.Reference
  Silmaril.Wasm.Component.Reference.LegalBoundaryRuns
  Silmaril.Wasm.Component.Reference.LegalBoundary
open Silmaril.Wasm.Execution.Core (throwing Frame)

/-- `trapCfg m` has no quiet divergence. -/
theorem not_quietDiverges_trapCfg {E : CoreEngine} {σ : Type} {prof : ProfileKind}
    {hr : HostReady σ} {dispatch : Call E → P E σ (Ret E)} {st : σ} {m : Config E σ} :
    ¬ QuietDiverges prof hr dispatch st (trapCfg m) := by
  intro d
  obtain ⟨z, ⟨-, -, tr, s, hne, -⟩, -⟩ := d.unfold
  obtain ⟨l, tr, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨_, s', -⟩ := Steps.cons_iff.1 s
  exact Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary.not_step_trapCfg s'

variable {P : Silmaril.Wasm.Numerics.Profile} {σ : Type} {prof : ProfileKind}
  {th : Option ThreadId} {f : Frame} {a : Nat}

section Machine

variable {hr : HostReady σ} {dispatch : Call (core3P P) → Canon.P (core3P P) σ (Ret (core3P P))}
  {m : Config (core3P P) σ} {k : List FlatValue → Canon.P (core3P P) σ (Ret (core3P P))}
  {segs : List (Seg (core3P P) σ)} {rest : List (Activation (core3P P) σ)}

theorem stepTwin_throw_trap :
    StepTwin prof hr dispatch (coreCfg m th (.active f (throwing a)) k segs rest)
      (coreCfg m th (.active f [.trap]) k segs rest) :=
  ⟨fun _ _ => step_throw_iff_step_trap, rfl, rfl, rfl, by simp [coreCfg], by simp [coreCfg]⟩

theorem coreCfg_throw_ne_trap :
    coreCfg m th (.active f (throwing a)) k segs rest ≠
      coreCfg m th (.active f [.trap]) k segs rest := by
  intro h
  have := congrArg (fun x => x.ctl) h
  simp only [coreCfg, List.cons.injEq, Activation.mk.injEq, and_true, true_and] at this
  injection this with h1
  injection h1 with h2 h3
  simp [throwing] at h3

theorem not_divergesWithHost_throw :
    ¬ DivergesWithHost prof hr dispatch (coreCfg m th (.active f (throwing a)) k segs rest) := by
  intro d
  obtain ⟨z, ⟨l, s⟩, d'⟩ := d.unfold
  obtain ⟨-, rfl⟩ := step_throw_iff.1 s
  obtain ⟨_, ⟨_, s'⟩, -⟩ := d'.unfold
  exact Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary.not_step_trapCfg s'

theorem not_quietRest_throw {st : σ} :
    ¬ QuietRest prof hr dispatch st (coreCfg m th (.active f (throwing a)) k segs rest) := by
  rintro ⟨tr, m₂, s, -, d⟩
  rcases steps_throw_iff.1 s with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · obtain ⟨z, ⟨-, -, tr', s', hne, -⟩, d'⟩ := d.unfold
    obtain ⟨l, tr', rfl⟩ := List.exists_cons_of_ne_nil hne
    rcases steps_throw_iff.1 s' with ⟨h, -⟩ | ⟨-, rfl⟩
    · cases h
    · exact not_quietDiverges_trapCfg d'
  · exact not_quietDiverges_trapCfg d

end Machine

theorem not_hostProdRest_throw {ε : Type} {hr : HostReady (σ × List ε)}
    {dispatch : Call (core3P P) → Canon.P (core3P P) (σ × List ε) (Ret (core3P P))}
    {m : Config (core3P P) (σ × List ε)}
    {k : List FlatValue → Canon.P (core3P P) (σ × List ε) (Ret (core3P P))}
    {segs : List (Seg (core3P P) (σ × List ε))} {rest : List (Activation (core3P P) (σ × List ε))}
    {base : List ε} {ev : ℕ → ε} :
    ¬ HostProdRest prof hr dispatch base
      (coreCfg m th (.active f (throwing a)) k segs rest) ev := by
  rintro ⟨t, h0, hs, -⟩
  obtain ⟨_, -, s⟩ := hs 0
  rw [h0] at s
  obtain ⟨-, h1⟩ := step_throw_iff.1 s
  obtain ⟨_, -, s'⟩ := hs 1
  rw [h1] at s'
  exact Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary.not_step_trapCfg s'

theorem sessRest_throw_iff {h : Host (core3P P) σ} {m m₀ m₁ : Config (core3P P) σ}
    {k : List FlatValue → Canon.P (core3P P) σ (Ret (core3P P))}
    {segs : List (Seg (core3P P) σ)} {rest : List (Activation (core3P P) σ)} {n : Nat}
    {o : Option (List Value.Val)} :
    SessRest prof h m₀ (coreCfg m th (.active f (throwing a)) k segs rest) n o m₁ ↔
      o = none ∧ m₁ = resumeCfg m₀ (trapCfg m) := by
  constructor
  · rintro (⟨tr, s, -, -, hout⟩ | ⟨tr, s, -, -, -⟩)
    · rcases steps_throw_iff.1 s with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact absurd hout.1 (by simp [coreCfg])
      · simp [CallOutcome.Holds] at hout
    · rcases steps_throw_iff.1 s with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .trap ⟨[.trap .coreTrap], steps_throw_iff.2 (.inr ⟨rfl, rfl⟩), by simp, by simp,
      trapCfg_lockdown m⟩

end Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns
