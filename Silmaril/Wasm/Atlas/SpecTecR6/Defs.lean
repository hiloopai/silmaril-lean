module

public import Silmaril.Wasm.Atlas.SpecTec.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Defs

/-!
# The SpecTec step charts at the backend reading

`Atlas.SpecTec` relates the Core step chart to SpecTec's declarative `SStep` only conditionally,
and the conditional hypotheses are false on the valid fragment (round 6 refuted them at the
declarative reading). Round 6 proved the whole-step simulation at the **backend reading**
`Round6.Int.backend` (`Round6.Int.wholeStepValidR_backend`, `runsR_backend`). This module fixes
the charts that the proved theorem speaks about; `Atlas.SpecTecR6.Thms` builds the transitions.

* `readChart Rd B`: SpecTec values, observed through the successors of a reading `Rd` of
  SpecTec's whole-machine `Step` at builtins `B`. At `Rd := Round6.Int.backend` this is
  `Reading.SStepB (simEnv B)`.
* `Dom P host c`: the domain of the round-6 theorem. `c` is valid (`ConfigOk c ts` for some
  `ts`), `BoundedSel`, and every Core successor of `c` is `BoundedSel`.
* `DomDet P host c`: `Dom` and Core has at most one successor at `c`. On it the forward half of
  the theorem is exact, so the transition is an equality.
* `runObs`, `detRunObs`, `readRunObs`: multi-step observations (all reachable configurations,
  those reachable by `DetSteps`, and reading runs). `runChart`, `readRunChart`: the multi-step
  charts. `RunDom` is `ConfigOk` and `BoundedReachSel`; `RunDomDet` also asks every reachable
  configuration to have at most one successor.
* `BTrans`-style constructors for the backward-only direction (`ofSupUpToUniv`,
  `ofSupUpToExist`): every target observation is related to a source observation.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas

universe u u' u'' v

namespace BSen

variable {C : Type u} {B : Type v}

/-- A sentence that respects `R` respects its converse. -/
theorem Respects.flip {R : B → B → Prop} {s : BSen C B} (h : s.Respects R) :
    s.Respects (fun b b' => R b' b) := by
  induction s with
  | always _ _ => exact (fun b b' r => (h b' b r).symm)
  | may _ _ => exact (fun b b' r => (h b' b r).symm)
  | «and» s t ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | top => trivial

end BSen

namespace BTrans

variable {Pt : Type u} {Pt' : Type u''} {C : Type u'} {C' : Type u'} {B : Type v}
  {dom : Pt → Prop} {dom' : Pt' → Prop} {obs : Pt → C → Set B} {obs' : Pt' → C' → Set B}

/-- **Target observations simulated up to `R` in the source** (completeness of the source chart
up to `R`): universal `R`-respecting sentences of the source hold in the target. -/
def ofSupUpToUniv (R : B → B → Prop) (f : Pt → Pt') (σ : C → C')
    (hdom : ∀ p, dom p → dom' (f p))
    (h₂ : ∀ p, dom p → ∀ c, ∀ b' ∈ obs' (f p) (σ c), ∃ b ∈ obs p c, R b b') :
    Transition (BChart Pt C B dom obs) (BChart Pt' C' B dom' obs') where
  pt := f
  sen := BSen.rename σ
  cls s := s.Universal ∧ s.Respects R
  dir := .preserves
  dom_pt := hdom
  sat p s hp hs := ⟨fun _ hsrc => (BSen.sat_rename σ _ s).2
      (BSen.sat_upto_univ (obs := fun c => obs' (f p) (σ c)) (obs' := obs p)
        (R := fun b b' => R b' b) (h₂ p hp) hs.1 hs.2.flip hsrc),
    fun e => absurd e (by decide)⟩

/-- **Target observations simulated up to `R` in the source**: existential `R`-respecting
witnesses of the target are witnesses of the source. -/
def ofSupUpToExist (R : B → B → Prop) (f : Pt → Pt') (σ : C → C')
    (hdom : ∀ p, dom p → dom' (f p))
    (h₂ : ∀ p, dom p → ∀ c, ∀ b' ∈ obs' (f p) (σ c), ∃ b ∈ obs p c, R b b') :
    Transition (BChart Pt C B dom obs) (BChart Pt' C' B dom' obs') where
  pt := f
  sen := BSen.rename σ
  cls s := s.Existential ∧ s.Respects R
  dir := .reflects
  dom_pt := hdom
  sat p s hp hs := ⟨fun e => absurd e (by decide), fun _ ht =>
    BSen.sat_upto_exist (obs := fun c => obs' (f p) (σ c)) (obs' := obs p)
      (R := fun b b' => R b' b) (h₂ p hp) hs.1 hs.2.flip ((BSen.sat_rename σ _ s).1 ht)⟩

end BTrans

namespace SpecTecR6

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec
open Silmaril.Wasm.SpecTec.Sim.Round6 (Target.Reading)

variable {H : Type}

/-! ## One step -/

/-- **The step chart of a reading** `Rd` of SpecTec's `Step` at builtins `B`. -/
def readChart (Rd : Target.Reading) (B : Builtins) : Chart :=
  BChart Value Unit Value (fun _ => True) (fun v _ => {w | Rd.step B v w})

/-- **The domain of the round-6 theorem**: valid, `BoundedSel`, with `BoundedSel` Core
successors. -/
def Dom (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  (∃ ts : List CValType, ConfigOk c ts) ∧ Sim.Round5.Target.BoundedSel c ∧
    ∀ c₁, Step P host c c₁ → Sim.Round5.Target.BoundedSel c₁

/-- Core has at most one successor at `c`. -/
def StepDet (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  ∀ c₁ c₂, Step P host c c₁ → Step P host c c₂ → c₁ = c₂

/-- **The deterministic part of the domain**: there the forward half is exact. -/
def DomDet (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  Dom P host c ∧ StepDet P host c

/-- The forward conjunct for a reading on `D`, up to Core's choice of successor. -/
def FwdOnR (Rd : Target.Reading) (B : Builtins) (P : Profile) (host : HostSemantics H)
    (hn : H → String) (D : Config H → Prop) : Prop :=
  ∀ c, D c → ∀ c', Step P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Sim.Bwd.ConfigEq c'' d' ∧ Rd.step B (Sim.configV hn c) (Sim.configV hn d')

/-- The backward conjunct for a reading on `D`. -/
def BwdOnR (Rd : Target.Reading) (B : Builtins) (P : Profile) (host : HostSemantics H)
    (hn : H → String) (D : Config H → Prop) : Prop :=
  ∀ c, D c → ∀ w, Rd.step B (Sim.configV hn c) w →
    ∃ c' d', Sim.Bwd.ConfigEq c' d' ∧ w = Sim.configV hn d' ∧ Step P host c c'

/-! ## Runs -/

/-- The SpecTec values of all configurations reachable by Core. -/
def runObs (P : Profile) (host : HostSemantics H) (hn : H → String) (c : Config H) (_ : Unit) :
    Set Value :=
  {w | ∃ c', Steps P host c c' ∧ w = Sim.configV hn c'}

/-- The SpecTec values of the configurations reachable by deterministic Core runs. -/
def detRunObs (P : Profile) (host : HostSemantics H) (hn : H → String) (c : Config H)
    (_ : Unit) : Set Value :=
  {w | ∃ c', Sim.Round6.Target.DetSteps P host c c' ∧ w = Sim.configV hn c'}

/-- The values reachable by runs of a reading. -/
def readRunObs (Rd : Target.Reading) (B : Builtins) (v : Value) (_ : Unit) : Set Value :=
  {w | Sim.Round6.Target.RSteps Rd B v w}

/-- **The Core run chart** on `D`: observations are all reachable configurations. -/
def runChart (P : Profile) (host : HostSemantics H) (hn : H → String) (D : Config H → Prop) :
    Chart :=
  BChart (Config H) Unit Value D (runObs P host hn)

/-- **The run chart of a reading.** -/
def readRunChart (Rd : Target.Reading) (B : Builtins) : Chart :=
  BChart Value Unit Value (fun _ => True) (readRunObs Rd B)

/-- The domain of the multi-step corollary: valid, and every reachable configuration is
`BoundedSel`. -/
def RunDom (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  (∃ ts : List CValType, ConfigOk c ts) ∧ Sim.Round5.Target.BoundedReachSel P host c

/-- `RunDom` and every reachable configuration has at most one Core successor. -/
def RunDomDet (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  RunDom P host c ∧ ∀ c', Steps P host c c' → StepDet P host c'

end SpecTecR6

end Silmaril.Wasm.Atlas
