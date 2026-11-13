module

public import Silmaril.Raw.Wasm.Component.Machine.Soundness

/-!
# Inverting steps of the copied component machine

The copied machine (`Silmaril.Raw.Wasm.Component.Machine`) has a relational step `Machine.Step` and
an executable step `step?`, with soundness `step?_sound` but no completeness. This module proves
the completeness needed to invert relational traces:

* `Step.step?_of_det`: a relational step that is not a choice, an internal core step or a host
  event is the step `step?` computes, for every core stepper `X` and every oracle `o` (neither is
  consulted outside choices and internal core steps);
* `Step.det`: such steps are deterministic.

Choices (`Step.choose`), internal core steps (`Step.coreInternal`) and host events are the only
non-deterministic rules; they are inverted directly by `cases` on the step.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine

variable {E : CoreEngine} {σ : Type}

/-- A label of a deterministic rule: not a choice, an internal core step or a host event. -/
def Label.Det (l : Label E σ) : Prop :=
  (∀ k r, l ≠ .choice k r) ∧ l ≠ .core ∧ ∀ ev, l ≠ .host ev

theorem Label.Det.tau : Label.Det (E := E) (σ := σ) .tau :=
  ⟨fun _ _ h => (by cases h), fun h => (by cases h), fun _ h => (by cases h)⟩

variable {prof : ProfileKind} {hr : HostReady σ} {dispatch : Call E → P E σ (Ret E)}
  (X : E.Exec) (o : Oracle E)

/-- **Completeness of `step?` for deterministic rules.** -/
theorem Step.step?_of_det {m m' : Config E σ} {l : Label E σ}
    (h : Step prof hr dispatch m l m') (hl : Label.Det l) :
    ∃ st, step? dispatch X o m = some (l, st, m') := by
  cases h with
  | popProg hc => exact ⟨_, by simp only [step?, hc, retStep, tauStep]; rfl⟩
  | popCore hc => exact ⟨_, by simp only [step?, hc, retStep, tauStep]; rfl⟩
  | threadExit hc => exact ⟨_, by simp only [step?, hc, retStep, finish, tauStep]; rfl⟩
  | @hostDone r rest hc =>
    refine ⟨o.state, ?_⟩
    simp only [step?, hc, retStep, finish, StepDefs.hostFinish, ← lastCall?_eq]
    generalize m.lastCall? = lc
    cases rest <;> cases r <;> cases lc <;> rfl
  | call hc => exact ⟨_, by simp only [step?, hc, opStep, tauStep]; rfl⟩
  | callCore hc => exact ⟨_, by simp only [step?, hc, opStep, tauStep]; rfl⟩
  | coreInternal => exact absurd rfl hl.2.1
  | coreReturned hc hs => exact ⟨_, by simp only [step?, hc, coreStep, hs, tauStep]; rfl⟩
  | coreTrap hc hs => exact ⟨_, by simp only [step?, hc, coreStep, hs, trapStep]; rfl⟩
  | coreCallout hc hs => exact ⟨_, by simp only [step?, hc, coreStep, hs, tauStep]; rfl⟩
  | get hc => exact ⟨_, by simp only [step?, hc, opStep, tauStep]; rfl⟩
  | modify hc => exact ⟨_, by simp only [step?, hc, opStep, tauStep]; rfl⟩
  | trap hc => exact ⟨_, by simp only [step?, hc, opStep, trapStep]; rfl⟩
  | choose r => exact absurd rfl (hl.1 _ r)
  | currentThread hc => exact ⟨_, by simp only [step?, hc, opStep, tauStep]; rfl⟩
  | newThread hc ha => exact ⟨_, by simp only [step?, hc, opStep, tauStep, ha]; rfl⟩
  | block hc => exact ⟨_, by simp only [step?, hc, opStep, tauStep]; rfl⟩
  | @blockSwitch t u k segs rest b hc hb =>
    have hb' : (((m.setCont t (some ⟨some t, .prog (k ()), segs⟩)).mapStore
        (CStoreOps.setThreadStatus t .blocked)).cont? u) = some b := hb
    exact ⟨_, by simp only [step?, hc, opStep, blockSave, tauStep]; rw [hb']; rfl⟩
  | resumeThread hc hb => exact ⟨_, by simp only [step?, hc, opStep, tauStep, hb]; rfl⟩
  | hostGet hc => exact ⟨_, by simp only [step?, hc, opStep, tauStep]; rfl⟩
  | hostSet hc => exact ⟨_, by simp only [step?, hc, opStep, tauStep]; rfl⟩
  | emit hc => exact ⟨_, by simp only [step?, hc, opStep, observe_eq]; rfl⟩
  | fault hf => exact Fault.step?_of hf
  | hostInvoke => exact absurd rfl (hl.2.2 _)
  | hostTick => exact absurd rfl (hl.2.2 _)
  | hostCancel => exact absurd rfl (hl.2.2 _)
  | hostRun => exact absurd rfl (hl.2.2 _)
where
  Fault.step?_of {m : Config E σ} {msg : String} (hf : Fault m msg) :
      ∃ st, step? dispatch X o m = some (.trap (.internal msg), st, StepDefs.trapCfg m) := by
    cases hf with
    | blockNoThread hc => exact ⟨_, by simp only [step?, hc, opStep, trapStep]; rfl⟩
    | @switchMissing t u k segs rest hc hu =>
      have hu' : (((m.setCont t (some ⟨some t, .prog (k ()), segs⟩)).mapStore
          (CStoreOps.setThreadStatus t .blocked)).cont? u) = none := hu
      exact ⟨_, by simp only [step?, hc, opStep, blockSave, trapStep]; rw [hu']; rfl⟩
    | resumeMissing hc hu => exact ⟨_, by simp only [step?, hc, opStep, hu, trapStep]; rfl⟩
    | calloutBadRet hc hnf =>
      refine ⟨o.state, ?_⟩
      simp only [step?, hc, retStep]
      rfl

/-- The core stepper that takes no step. -/
def noStep : E.Exec := ⟨fun _ => none, fun h => by cases h⟩

/-- **Deterministic rules are deterministic.** -/
theorem Step.det {m m₁ m₂ : Config E σ} {l₁ l₂ : Label E σ}
    (h₁ : Step prof hr dispatch m l₁ m₁) (hl₁ : Label.Det l₁)
    (h₂ : Step prof hr dispatch m l₂ m₂) (hl₂ : Label.Det l₂) : l₁ = l₂ ∧ m₁ = m₂ := by
  obtain ⟨st₁, e₁⟩ := Step.step?_of_det noStep Oracle.first h₁ hl₁
  obtain ⟨st₂, e₂⟩ := Step.step?_of_det noStep Oracle.first h₂ hl₂
  rw [e₁] at e₂
  simp only [Option.some.injEq, Prod.mk.injEq] at e₂
  exact ⟨e₂.1, e₂.2.2⟩

end Silmaril.Proofs.Wasm.Component.Reference
