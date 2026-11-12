module

public import Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.TyElim.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Refute.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Thms

/-!
# SpecTec ↔ Core 3.0, round 6, integration (pass 4): the target, proved

Pass 3 reduced `Round6.Task.wholeStepValidR Int.backend` to the store-free `RefOkV.AgreeTy`
(`Int.wholeStepValidR_backend_of_agreeTy`). Pass 4 proved its four fields on the concrete
builtins:

* `okIntro`: `AgreeOk.okIntro_BI`;
* `subIntro`: `AgreeSub.subIntro_BI`;
* `okElim`, `subElim`: `TyElim.okElim_BI`, `TyElim.subElim_BI`, assembled
  with the two introduction fields by `TyElim.agreeTy_of_intro`.

This file composes them: `agreeTy_BI` (every profile, encoding and host), then
`openR_backend`, `wholeStepValidR_backend` and the multi-step corollary `runsR_backend`.
`round6_summary` puts the proved target next to the formal refutations of the targets it
replaces and of the same statement at the declarative reading.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Int

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4Int (BI)
open Round5.Target (BoundedReachSel)
open Target (DetSteps RSteps)

variable {H : Type}

/-- **`RefOkV.AgreeTy` holds on the concrete builtins**, for every profile, encoding and host. -/
theorem agreeTy_BI (P : Profile) (hn : H → String) (host : HostSemantics H) :
    RefOkV.AgreeTy (simEnv (BI P hn host)) :=
  TyElim.agreeTy_of_intro ⟨AgreeOk.okIntro_BI P hn host, AgreeSub.subIntro_BI P hn host⟩

/-- **`Target.OpenR Int.backend`** at every injective encoding, finite `HostOk` host and spec
profile. -/
theorem openR_backend {hn : H → String} {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host) :
    Target.OpenR Int.backend hn (Profile.spec nd r) host :=
  openR_backend_of_agreeTy hinj hf hh (agreeTy_BI _ hn host)

/-- **The restated round-6 target, proved**: `Round6.Task.wholeStepValidR` at the backend
reading `Int.backend`. -/
theorem wholeStepValidR_backend : Round6.Task.wholeStepValidR Int.backend :=
  wholeStepValidR_backend_of_agreeTy fun _ hn _ host _ _ _ _ => agreeTy_BI _ hn host

/-- **The multi-step corollary at the backend reading**: from a valid configuration whose whole
reachable set is `BoundedSel`, every run of Core steps that each go to the only successor is
matched (up to `ConfigEq`) by a run of `Int.backend`, and every run of `Int.backend` is the image
(up to `ConfigEq`) of a Core run. -/
theorem runsR_backend {hn : H → String} {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host) :
    (∀ (c₀ c : Config H) (ts : List CValType), ConfigOk c₀ ts →
      BoundedReachSel (Profile.spec nd r) host c₀ → DetSteps (Profile.spec nd r) host c₀ c →
      ∃ d, Bwd.ConfigEq c d ∧
        RSteps Int.backend (BI (Profile.spec nd r) hn host) (configV hn c₀) (configV hn d)) ∧
    (∀ (c₀ : Config H) (ts : List CValType) (w : Value), ConfigOk c₀ ts →
      BoundedReachSel (Profile.spec nd r) host c₀ →
      RSteps Int.backend (BI (Profile.spec nd r) hn host) (configV hn c₀) w →
      ∃ c d, Bwd.ConfigEq c d ∧ w = configV hn d ∧ Steps (Profile.spec nd r) host c₀ c) :=
  runsR_backend_of_agreeTy hinj hf hh (agreeTy_BI _ hn host)

/-- **Round 6 in one statement**: the restated target holds at the backend reading, while the
same statement at the declarative reading and the targets it replaces are false. -/
theorem round6_summary :
    Round6.Task.wholeStepValidR Int.backend ∧
    ¬ Round6.Task.wholeStepValidR Target.declarative ∧
    ¬ Round5.Task.wholeStepValidSel ∧
    ¬ Round5.Task.wholeStepValidOk ∧
    ¬ Round4.Task.wholeStepValid :=
  ⟨wholeStepValidR_backend, not_wholeStepValidR_declarative, Refute.not_wholeStepValidSel,
    Round5.Target.not_wholeStepValidOk, Round5.Pos.not_wholeStepValid⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.Int
