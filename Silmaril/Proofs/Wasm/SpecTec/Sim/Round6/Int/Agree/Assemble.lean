module

public import Silmaril.Wasm.SpecTec.Sim.Round6.CastsV.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.Thms

/-!
# SpecTec ↔ Core 3.0, round 6, integration (pass 3): the target from the interpreter half

Pass 3 reduced `Round6.Task.wholeStepValidR Int.backend` to one interpreter statement:

* track casts-v proved the target and its multi-step corollary from `RefOkB.RefOkBV`
  (`CastsV.openR_backend_of_refOkBV`, `wholeStepValidR_backend_of_refOkBV`,
  `runsR_backend_of_refOkBV`);
* track refokbv-prove proved `RefOkBV` from `RefOkV.Agree` (`RefOkV.refOkBV_of_agree`), with the
  Core half `RefOkV.refOkS_iff` proved outright.

This file composes them: `openR_backend_of_agree`, `wholeStepValidR_backend_of_agree`,
`runsR_backend_of_agree`, and the same from track refokbv-prove's store-free `RefOkV.AgreeTy`
(`RefOkV.agree_of_agreeTy`): `openR_`/`wholeStepValidR_`/`runsR_backend_of_agreeTy`. Both
`RefOkV.Agree` (that `DDerivesB` reads `Ref_ok` as `RefOkS`) and `RefOkV.AgreeTy` are open.
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

variable {H : Type} {hn : H → String} {host : HostSemantics H}

/-- `Target.OpenR Int.backend` from the interpreter half `RefOkV.Agree`. -/
theorem openR_backend_of_agree {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host)
    (A : RefOkV.Agree (simEnv (BI (Profile.spec nd r) hn host))) :
    Target.OpenR backend hn (Profile.spec nd r) host :=
  CastsV.openR_backend_of_refOkBV hinj hf hh (RefOkV.refOkBV_of_agree A)

/-- **`Round6.Task.wholeStepValidR Int.backend` from the interpreter half `RefOkV.Agree`** at
every injective encoding, finite `HostOk` host and spec profile. -/
theorem wholeStepValidR_backend_of_agree
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice),
          RefOkV.Agree (simEnv (BI (Profile.spec nd r) hn host))) :
    Round6.Task.wholeStepValidR backend :=
  CastsV.wholeStepValidR_backend_of_refOkBV fun H hn hinj host hf hh nd r =>
    RefOkV.refOkBV_of_agree (h H hn hinj host hf hh nd r)

/-- **The multi-step corollary at the backend reading, from `RefOkV.Agree`**
(`Target.runsR_of_open` at `Int.backend`). -/
theorem runsR_backend_of_agree {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host)
    (A : RefOkV.Agree (simEnv (BI (Profile.spec nd r) hn host))) :
    (∀ (c₀ c : Config H) (ts : List CValType), ConfigOk c₀ ts →
      BoundedReachSel (Profile.spec nd r) host c₀ → DetSteps (Profile.spec nd r) host c₀ c →
      ∃ d, Bwd.ConfigEq c d ∧
        RSteps backend (BI (Profile.spec nd r) hn host) (configV hn c₀) (configV hn d)) ∧
    (∀ (c₀ : Config H) (ts : List CValType) (w : Value), ConfigOk c₀ ts →
      BoundedReachSel (Profile.spec nd r) host c₀ →
      RSteps backend (BI (Profile.spec nd r) hn host) (configV hn c₀) w →
      ∃ c d, Bwd.ConfigEq c d ∧ w = configV hn d ∧ Steps (Profile.spec nd r) host c₀ c) :=
  Target.runsR_of_open hinj hf hh (openR_backend_of_agree hinj hf hh A)

/-! ## From `RefOkV.AgreeTy` (no store) -/

/-- `Target.OpenR Int.backend` from `RefOkV.AgreeTy`, the four store-free statements about
`Reftype_ok {}` and `Reftype_sub {}` (`RefOkV.agree_of_agreeTy`). -/
theorem openR_backend_of_agreeTy {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host)
    (A : RefOkV.AgreeTy (simEnv (BI (Profile.spec nd r) hn host))) :
    Target.OpenR backend hn (Profile.spec nd r) host :=
  openR_backend_of_agree hinj hf hh (RefOkV.agree_of_agreeTy A)

/-- **`Round6.Task.wholeStepValidR Int.backend` from `RefOkV.AgreeTy`.** -/
theorem wholeStepValidR_backend_of_agreeTy
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice),
          RefOkV.AgreeTy (simEnv (BI (Profile.spec nd r) hn host))) :
    Round6.Task.wholeStepValidR backend :=
  wholeStepValidR_backend_of_agree fun H hn hinj host hf hh nd r =>
    RefOkV.agree_of_agreeTy (h H hn hinj host hf hh nd r)

/-- **The multi-step corollary at the backend reading, from `RefOkV.AgreeTy`.** -/
theorem runsR_backend_of_agreeTy {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host)
    (A : RefOkV.AgreeTy (simEnv (BI (Profile.spec nd r) hn host))) :
    (∀ (c₀ c : Config H) (ts : List CValType), ConfigOk c₀ ts →
      BoundedReachSel (Profile.spec nd r) host c₀ → DetSteps (Profile.spec nd r) host c₀ c →
      ∃ d, Bwd.ConfigEq c d ∧
        RSteps backend (BI (Profile.spec nd r) hn host) (configV hn c₀) (configV hn d)) ∧
    (∀ (c₀ : Config H) (ts : List CValType) (w : Value), ConfigOk c₀ ts →
      BoundedReachSel (Profile.spec nd r) host c₀ →
      RSteps backend (BI (Profile.spec nd r) hn host) (configV hn c₀) w →
      ∃ c d, Bwd.ConfigEq c d ∧ w = configV hn d ∧ Steps (Profile.spec nd r) host c₀ c) :=
  runsR_backend_of_agree hinj hf hh (RefOkV.agree_of_agreeTy A)

end Silmaril.Wasm.SpecTec.Sim.Round6.Int
