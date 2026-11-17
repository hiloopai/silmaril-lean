module

public import Silmaril.Wasm.Abstract.HostDet.Defs
import Silmaril.Proofs.Wasm.Abstract.HostDet

/-!
# Deterministic hosts: determinism, normal forms and logs of Core runs

At the deterministic profile `SingleThreaded.profile o` (canonical NaNs, `$ND = false`, grow
decided by the oracle `o`), against a host with at most one outcome per call (`HostDet`):

* `Step.join_of_hostDet`: **two steps of a configuration join in at most one step each**
  (`Det.Join`), and `Step.eq_or_shrink_of_hostDet`: they are equal or the first has strictly
  smaller code. Host-free steps join by `Det.DStep.join'` (Core reduction is a function up to
  trap bubbling); a configuration at a host callout has no host-free step, and its host steps
  coincide because the callout (`decompose?`) and the host's outcome are unique.
* `Steps.nf_unique_of_hostDet`: **normal forms are unique**.
* `Steps.always_of_hostDet`: **a run to a normal form excludes infinite runs** (including a host
  call that diverges), and every finite run extends to that normal form.
* `LStep.toStep`, `Step.toLStep`, `LSteps.toSteps`, `Steps.toLSteps`, `LStep.nf_iff`: logged runs
  are exactly the runs, with the log of answered host calls.
* `LSteps.nf_unique_of_hostDet`: **the normal form and the host-call log of a run to it are
  unique**: two logged runs from one configuration and log to normal forms end in the same
  configuration with the same log.

No typing hypothesis: determinism of `Step` at `profile o` needs none. Proofs:
`Silmaril.Proofs.Wasm.Abstract.HostDet`.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Proofs.Wasm.Abstract.HostDet

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

theorem LStep.toStep {x y : Config H × HostLog H} (h : LStep P host x y) :
    Step P host x.1 y.1 :=
  lstep_toStep h

theorem Step.toLStep {c c' : Config H} (h : Step P host c c') (l : HostLog H) :
    ∃ l', LStep P host (c, l) (c', l') :=
  step_toLStep h l

theorem LSteps.toSteps {x y : Config H × HostLog H} (h : LSteps P host x y) :
    Steps P host x.1 y.1 :=
  lsteps_toSteps h

theorem Steps.toLSteps {c c' : Config H} (h : Steps P host c c') (l : HostLog H) :
    ∃ l', LSteps P host (c, l) (c', l') :=
  steps_toLSteps h l

/-- A pair is `LStep`-normal exactly when its configuration is `Step`-normal. -/
theorem LStep.nf_iff {c : Config H} {l : HostLog H} :
    (∀ y, ¬ LStep P host (c, l) y) ↔ ∀ c', ¬ Step P host c c' :=
  lstep_nf_iff

variable {o : GrowOracle}

/-- **Determinism up to bubbling, with a deterministic host.** -/
theorem Step.join_of_hostDet (hd : HostDet host) {c c₁ c₂ : Config H}
    (h₁ : Step (profile o) host c c₁) (h₂ : Step (profile o) host c c₂) :
    Det.Join (Step (profile o) host) c₁ c₂ :=
  step_join hd h₁ h₂

theorem Step.eq_or_shrink_of_hostDet (hd : HostDet host) {c c₁ c₂ : Config H}
    (h₁ : Step (profile o) host c c₁) (h₂ : Step (profile o) host c c₂) :
    c₁ = c₂ ∨ sizeOf c₁.code < sizeOf c.code :=
  step_shrink hd h₁ h₂

/-- **Normal forms are unique, with a deterministic host.** -/
theorem Steps.nf_unique_of_hostDet (hd : HostDet host) {c₀ c c' : Config H}
    (h : Steps (profile o) host c₀ c) (hn : ∀ x, ¬ Step (profile o) host c x)
    (h' : Steps (profile o) host c₀ c') (hn' : ∀ x, ¬ Step (profile o) host c' x) : c = c' :=
  nf_unique_of_join (fun ha hb => step_join hd ha hb) h h' hn hn'

/-- **A run to a normal form excludes infinite runs, with a deterministic host**, and every
finite run extends to that normal form. -/
theorem Steps.always_of_hostDet (hd : HostDet host) {c₀ c : Config H}
    (h : Steps (profile o) host c₀ c) (hn : ∀ x, ¬ Step (profile o) host c x) :
    ¬ Diverges (profile o) host c₀ ∧
      ∀ c', Steps (profile o) host c₀ c' → Steps (profile o) host c' c :=
  steps_always hd h hn

theorem LStep.join_of_hostDet (hd : HostDet host) {x a b : Config H × HostLog H}
    (ha : LStep (profile o) host x a) (hb : LStep (profile o) host x b) :
    Det.Join (LStep (profile o) host) a b :=
  lstep_join hd ha hb

/-- **The normal form and the host-call log are unique, with a deterministic host.** -/
theorem LSteps.nf_unique_of_hostDet (hd : HostDet host) {x : Config H × HostLog H}
    {c c' : Config H} {l l' : HostLog H} (h : LSteps (profile o) host x (c, l))
    (hn : ∀ y, ¬ Step (profile o) host c y) (h' : LSteps (profile o) host x (c', l'))
    (hn' : ∀ y, ¬ Step (profile o) host c' y) : c = c' ∧ l = l' := by
  have := nf_unique_of_join (fun ha hb => lstep_join hd ha hb) h h' (lstep_nf_iff.mpr hn)
    (lstep_nf_iff.mpr hn')
  simp only [Prod.mk.injEq] at this
  exact this

end Silmaril.Wasm.Abstract

end
