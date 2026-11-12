module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.FwdRef.HostRules

/-!
# Round 5, pass 2, track fwdref: the restated target from `OpenT`

* `oblT`: `Round5.Fwd.Obl` (`Round5.Fwd.obl_of`) with the host fields from
  `HostRespectsT` (`fwd_callRefHostT`, `fwd_callRefHostDivT`);
* `forward_validT`: the forward conjunct from `TypesB`, `RefOkB`, `HostRespectsT` and the
  non-bitwise SIMD operators; `array.new_data-num` is `newDataNumB_builtins`;
* `openT_of_open`: `OpenT` is no stronger than `Round5.Int.Open`;
* `partsOkR_of_openT`, `wholeStepValidOk_of_openT`: the pass-1 integration's
  `partsOkR_of_open`/`wholeStepValidOk_of_open` from `OpenT`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4 (Bounded)
open Round4Int (BI)
open Round5.Fwd (TypesB Obl Rest)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **`Obl` from `TypesB`, `Rest` and `HostRespectsT`** (`Round5.Fwd.obl_of` with
the host fields from `HostRespectsT`). -/
theorem oblT (TB : TypesB (simEnv (BI P hn host))) (hf : HostFinite host)
    (hr : HostRespectsT (simEnv (BI P hn host)) hn host) (R : Rest (BI P hn host) hn P host) :
    Obl (BI P hn host) hn P host where
  vector := R.vector
  aggregate := R.aggregate
  refTest := R.refTest
  refCast := R.refCast
  brOnCast := R.brOnCast
  brOnCastFail := R.brOnCastFail
  block _ _ _ _ _ _ _ h₁ h₂ hb := Round5.Fwd.fwd_block5 TB h₁ h₂ hb.frame
  loop _ _ _ _ _ _ _ h₁ h₂ hb := Round5.Fwd.fwd_loop5 TB h₁ h₂ hb.frame
  tryTable _ _ _ _ _ _ _ _ h₁ h₂ hb := Round5.Fwd.fwd_tryTable5 TB h₁ h₂ hb.frame
  callRefFunc _ _ _ _ _ _ _ _ _ hc hfa hex hlen hcode hb :=
    Round5.Fwd.fwd_callRefFunc5 TB hc hfa hex hlen hcode
      (Round5.Fwd.tyBnd_funcType hb.storeBnd hfa)
  callRefHost _ _ _ _ _ _ _ _ _ _ _ hc hfa hex hlen hcode hh hb :=
    fwd_callRefHostT TB hf hr hc hfa hex hlen hcode hh (Round5.Fwd.tyBnd_funcType hb.storeBnd hfa)
  callRefHostDiv _ _ _ _ _ _ _ _ _ hc hfa hex hlen hcode hh hb :=
    fwd_callRefHostDivT TB hf hr hc hfa hex hlen hcode hh
      (Round5.Fwd.tyBnd_funcType hb.storeBnd hfa)
  returnCallRefFrameAddr _ _ _ _ _ _ _ _ _ _ _ _ hc hfn hex hlen hb :=
    Round5.Fwd.fwdUp_returnCallRefFrameAddr5 TB hc hfn hex hlen
      (Round5.Fwd.tyBnd_funcType hb.storeBnd hfn)
  throw _ _ _ _ _ _ _ htag hex hlen hb := Round5.Fwd.fwd_throw5 TB htag hex hlen hb.storeBnd
  throwRefHandlerCatch _ _ _ _ _ _ _ _ he ht _ := Round5.Fwd.fwd_throwRefHandlerCatch5 he ht
  throwRefHandlerCatchRef _ _ _ _ _ _ _ _ he ht _ := Round5.Fwd.fwd_throwRefHandlerCatchRef5 he ht
  throwRefHandlerNext _ _ _ _ _ _ hnm _ := Round5.Fwd.fwd_throwRefHandlerNext5 hnm

/-- **The forward conjunct on valid, bounded sources**, from `TypesB`, `RefOkB`, a finite host
respecting the encoding at typed store images, and the non-bitwise SIMD operators
(`Round5.Fwd.forward_valid_final` with `HostRespectsT` and `newDataNumB_builtins`). -/
theorem forward_validT (TB : TypesB (simEnv (BI P hn host)))
    (KB : Round5.Fwd.RefOkB (simEnv (BI P hn host))) (hf : HostFinite host)
    (hr : HostRespectsT (simEnv (BI P hn host)) hn host) (vector : Int.VectorFwd hn P host) :
    R4Fwd.Forward (BI P hn host) hn P host Round4Int.Valid :=
  Round5.Fwd.forward_valid5 (oblT TB hf hr (Round5.Fwd.rest_of KB vector
    fun _ _ h hb => Round5.Fwd.fwd_aggregate5 (Round5.Fwd.aggTypesB_of TB)
      (newDataNumB_builtins hn host) (Round5.Fwd.initDataZeroB_builtins hn host) h hb))

/-- **`OpenT` is no stronger than `Round5.Int.Open`.** -/
theorem openT_of_open (O : Int.Open hn P host) : OpenT hn P host where
  simd := O.simd
  refOk := O.refOk
  hostRespects := hostRespectsT_of O.hostRespects
  vector := O.vector
  vecAgree := O.vecAgree
  pureOpen := O.pureOpen
  read := O.read

/-- **`Round5.Int.PartsOkR` from `OpenT`**, for a finite host, in a profile where growth may both
succeed and fail (`Round5.Int.partsOkR_of_open` with `HostRespectsT`). -/
theorem partsOkR_of_openT (hf : HostFinite host) (hPs : ∀ k a n d, P.growMaySucceed k a n d)
    (hPf : ∀ k a n d, P.growMayFail k a n d) (O : OpenT hn P host) : Int.PartsOkR hn P host where
  pos := Pos.posTypingNE_of_simd O.simd hn
  fwd := R4Fwd.Forward.mono (fun _ h => h.1)
    (forward_validT (Int.typesB _) O.refOk hf O.hostRespects O.vector)
  hostSteps := hostStepsV_of_T hf O.hostRespects
  rem := ⟨fun i h₀ h₁ h₂ s f is w hv hc hf =>
      BwdStep.remPure_of_open O.vecAgree O.pureOpen i h₀ h₁ h₂ s f is w hv.read hc hf,
    O.read,
    fun i h6 h₀ h₁ c w hv hc hf => BwdStep.remStep hPs hPf i h6 h₀ h₁ c w hv.read hc hf⟩

/-- **`Round5.Task.wholeStepValidOk` from `OpenT`**, at every injective encoding, finite
`HostOk` host and `Profile.spec nd r`. -/
theorem wholeStepValidOk_of_openT
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), OpenT hn (Profile.spec nd r) host) :
    Round5.Task.wholeStepValidOk :=
  Int.wholeStepValidOk_of_partsOkR fun H hn hinj host hfin hok nd r =>
    partsOkR_of_openT hfin (BwdStep.growMaySucceed_spec nd r) (Round4.growMayFail_spec nd r)
      (h H hn hinj host hfin hok nd r)

end Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef
