module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.CastsV.Valid
public import Silmaril.Wasm.SpecTec.Sim.Round6.Casts.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Transfer.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB.Thms

/-!
# Round 6: the cast leaf at the backend reading, from `RefOkBV`

Track casts' generalized recursions (`Casts.castsFwdG`, `Casts.castsBwdG`) are run at
`W := CastsInv`. `CastsInv` holds at the witness of a valid configuration
(`castsInv_of_configOk`, `castsInv_of_configEq`) and is closed under the context rules
(`castsInv_closed`). Together with the bounded frame module from `Bounded`/`ReadValidS`, it gives
`CastRefOk` from `RefOkBV` (`castRefOk_of_refOkBV`).

* `castsFwdV`, `castsBwdV`: the two halves of `Target.Casts Int.backend`, from `RefOkBV`.
* `casts_backend_of_refOkBV`, `casts_backend_spec_of_refOkBV`: **`Target.Casts Int.backend`
  from `RefOkBV`**.
* `openR_backend_of_refOkBV`, `wholeStepValidR_backend_of_refOkBV`, `runsR_backend_of_refOkBV`:
  the target and its multi-step corollary at the backend reading, from `RefOkBV` (with track
  transfer's unconditional `Transfer.transfer_backend_BI`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.CastsV

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4 (SimRel Bounded)
open Round4Int (BI)
open Round5.Target (BoundedSel BoundedReachSel)
open Target (DetSteps RSteps)
open RefOkB (RefOkBV)
open Reading (SStepB)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- `CastsInv` at the witness of a valid configuration. -/
theorem castsInv_witness {B : Builtins} {c d : Config H} {ts : List CValType} (hc : ConfigOk c ts)
    (hd : SimRel B hn c d) : CastsInv d :=
  castsInv_of_configEq hd.1 (castsInv_of_configOk hc)

/-- **The forward half of the cast leaf at the backend reading, from `RefOkBV`.** -/
theorem castsFwdV (hh : HostOk host) (KV : RefOkBV (simEnv (BI P hn host))) (c d c' : Config H)
    (ts : List CValType) (hc : ConfigOk c ts) (hb : BoundedSel c)
    (hsucc : ∀ c₁, Step P host c c₁ → BoundedSel c₁) (hd : SimRel (BI P hn host) hn c d)
    (hx : Target.CastRedex d.code) (hs : Step P host c c') :
    ∃ d', SimRel (BI P hn host) hn c' d' ∧
      SStepB (simEnv (BI P hn host)) (configV hn d) (configV hn d') :=
  Casts.castsFwdG hh castsInv_closed
    (castRefOk_of_refOkBV KV (fun _ h => h.1.frame) fun _ h => h.2) c d c' ts hc hb hsucc hd
    (castsInv_witness hc hd) hx hs

/-- **The backward half of the cast leaf at the backend reading, from `RefOkBV`.** It does not
use the cast redex. -/
theorem castsBwdV (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (KV : RefOkBV (simEnv (BI P hn host))) (c d : Config H) (ts : List CValType) (w : Value)
    (hc : ConfigOk c ts) (hb : BoundedSel c) (hd : SimRel (BI P hn host) hn c d)
    (hs : SStepB (simEnv (BI P hn host)) (configV hn d) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧
      (Typed (simEnv (BI P hn host)) hn c' → Typed (simEnv (BI P hn host)) hn d') ∧
      w = configV hn d' ∧ Step P host c c' :=
  Casts.castsBwdG hinj hf hPs hPf castsInv_closed
    (castRefOk_of_refOkBV KV (fun _ h => h.1.frame) fun _ h => h.2) c d ts w hc hb hd
    (castsInv_witness hc hd) hs

/-- **The cast leaf of the round-6 target at the backend reading, from `RefOkBV`**, for an
injective encoding, a finite `HostOk` host and a profile in which growth may both succeed and
fail. -/
theorem casts_backend_of_refOkBV (hinj : Function.Injective hn) (hf : HostFinite host)
    (hh : HostOk host) (hPs : ∀ k a n d, P.growMaySucceed k a n d)
    (hPf : ∀ k a n d, P.growMayFail k a n d) (KV : RefOkBV (simEnv (BI P hn host))) :
    Target.Casts Int.backend (BI P hn host) hn P host where
  fwd c d c' ts hc hb hsucc hd hx hs := castsFwdV hh KV c d c' ts hc hb hsucc hd hx hs
  bwd c d ts w hc hb hd _ hs := castsBwdV hinj hf hPs hPf KV c d ts w hc hb hd hs

/-- **`Target.Casts Int.backend` from `RefOkBV`, at the spec profile.** -/
theorem casts_backend_spec_of_refOkBV {nd : Bool} {r : RelaxedChoice}
    (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    (KV : RefOkBV (simEnv (BI (Profile.spec nd r) hn host))) :
    Target.Casts Int.backend (BI (Profile.spec nd r) hn host) hn (Profile.spec nd r) host :=
  casts_backend_of_refOkBV hinj hf hh (Round5.BwdStep.growMaySucceed_spec nd r)
    (Round4.growMayFail_spec nd r) KV

/-- `RefOkBV` is weaker than `RefOkBB`, so this re-derives track casts' leaf. -/
theorem casts_backend_spec_of_refOkBB' {nd : Bool} {r : RelaxedChoice}
    (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    (KB : Reading.RefOkBB (simEnv (BI (Profile.spec nd r) hn host))) :
    Target.Casts Int.backend (BI (Profile.spec nd r) hn host) hn (Profile.spec nd r) host :=
  casts_backend_spec_of_refOkBV hinj hf hh (RefOkB.refOkBV_of_refOkBB KB)

/-! ## The target, from `RefOkBV` -/

/-- `Target.OpenR Int.backend` from `RefOkBV`: track transfer's transfer lemma and the cast
leaf. -/
theorem openR_backend_of_refOkBV {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host)
    (KV : RefOkBV (simEnv (BI (Profile.spec nd r) hn host))) :
    Target.OpenR Int.backend hn (Profile.spec nd r) host :=
  ⟨Transfer.transfer_backend_BI hn _ host, casts_backend_spec_of_refOkBV hinj hf hh KV⟩

/-- **`Round6.Task.wholeStepValidR Int.backend` from `RefOkBV`** at every injective encoding,
finite `HostOk` host and spec profile. -/
theorem wholeStepValidR_backend_of_refOkBV
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice),
          RefOkBV (simEnv (BI (Profile.spec nd r) hn host))) :
    Round6.Task.wholeStepValidR Int.backend :=
  Int.wholeStepValidR_backend_of_open fun H hn hinj host hf hh nd r =>
    openR_backend_of_refOkBV hinj hf hh (h H hn hinj host hf hh nd r)

/-- **The multi-step corollary at the backend reading, from `RefOkBV`** (`Target.runsR_of_open`
at `Int.backend`). -/
theorem runsR_backend_of_refOkBV {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host)
    (KV : RefOkBV (simEnv (BI (Profile.spec nd r) hn host))) :
    (∀ (c₀ c : Config H) (ts : List CValType), ConfigOk c₀ ts →
      BoundedReachSel (Profile.spec nd r) host c₀ → DetSteps (Profile.spec nd r) host c₀ c →
      ∃ d, Bwd.ConfigEq c d ∧
        RSteps Int.backend (BI (Profile.spec nd r) hn host) (configV hn c₀) (configV hn d)) ∧
    (∀ (c₀ : Config H) (ts : List CValType) (w : Value), ConfigOk c₀ ts →
      BoundedReachSel (Profile.spec nd r) host c₀ →
      RSteps Int.backend (BI (Profile.spec nd r) hn host) (configV hn c₀) w →
      ∃ c d, Bwd.ConfigEq c d ∧ w = configV hn d ∧ Steps (Profile.spec nd r) host c₀ c) :=
  Target.runsR_of_open hinj hf hh (openR_backend_of_refOkBV hinj hf hh KV)

end Silmaril.Wasm.SpecTec.Sim.Round6.CastsV
