module

public import Silmaril.Wasm.SpecTec.Sim.Round5.RefOk.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int3.Thms

/-!
# Round 5: the restated target from `Open5`, which has no `refOk`

`Fwd.RefOkB` was used at exactly two places: the four forward cast fields of
`Round5.Fwd.Rest` (`Round5.Fwd.rest_of`) and the eight backward cast rules of `Step_read`
(`Round5.Read.read_doneK`). `Open5` asks for those obligations directly (`CastsFwd`,
`CastsBwd`). The assembly copies pass 2's `Round5.Int2.partsOkS_of_open2`, with the
discharges of pass 3 (`Round5.Int3.open2_of_open4`) for `hostRespects`, `vector`, `vtestop` and
`read`, and the casts in place of `RefOkB`.

* `castsFwd_of_refOkB`, `castsBwd_of_refOkB`, `open5_of_open4`: `Open5` asks no more than
  `Open4`.
* `partsOkS_of_open5`, `wholeStepValidOk_of_open5`: the restated target from `Open5`.
* `not_open5`: `Open5` is unsatisfiable through `simd`, so `wholeStepValidOk_of_open5` is
  vacuous as stated.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.RefOk

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- `RefOkB` gives the forward cast obligations (`Round5.Fwd.rest_of`'s cast fields). -/
theorem castsFwd_of_refOkB (KB : Fwd.RefOkB (simEnv (BI P hn host))) :
    CastsFwd (BI P hn host) hn where
  refTest s f r rt hb := Fwd.fwd_refTest5 KB s f r rt hb.frame
  refCast s f r rt hb := Fwd.fwd_refCast5 KB s f r rt hb.frame
  brOnCast s f r l rt₁ rt₂ hb := Fwd.fwd_brOnCast5 KB s f r l rt₁ rt₂ hb.frame
  brOnCastFail s f r l rt₁ rt₂ hb := Fwd.fwd_brOnCastFail5 KB s f r l rt₁ rt₂ hb.frame

/-- `RefOkB` gives the backward cast obligations (`Round5.Read.read_doneK`). -/
theorem castsBwd_of_refOkB (KB : Fwd.RefOkB (simEnv (BI P hn host))) : CastsBwd hn P host :=
  fun i hi c w hv hc hf => Round5.Read.read_doneK KB i hi c w hv hc hf

/-- **`Open5` asks no more than `Round5.Int3.Open4`.** -/
theorem open5_of_open4 (O : Int3.Open4 hn P host) : Open5 hn P host where
  simd := O.simd
  vecOps := O.vecOps
  castsFwd := castsFwd_of_refOkB O.refOk
  castsBwd := castsBwd_of_refOkB O.refOk

/-- **`Open5` never holds**: its `simd` leaf is false for every builtins. -/
theorem not_open5 : ¬ Open5 hn P host := fun O => SimdTy.not_simdTyping _ O.simd

/-- `Round5.Fwd.Rest` from the forward cast obligations and the two other classes
(`Round5.Fwd.rest_of` with `CastsFwd` for `RefOkB`). -/
theorem rest_of_casts (C : CastsFwd (BI P hn host) hn)
    (vector : ∀ (s : Store H) (f : Frame) (is is' : List Admin), VectorStep P is is' →
      (∃ i, Admin.plain i ∈ is ∧ R4Fwd.VecArith i = true) → Round4.Bounded ⟨s, f, is⟩ →
      FwdP (simEnv (BI P hn host)) hn ⟨s, f, is⟩ ⟨s, f, is'⟩)
    (aggregate : ∀ c c' : Config H, AggregateStep c c' → Round4.Bounded c →
      FwdP (simEnv (BI P hn host)) hn c c') :
    Fwd.Rest (BI P hn host) hn P host where
  vector := vector
  aggregate := aggregate
  refTest := C.refTest
  refCast := C.refCast
  brOnCast := C.brOnCast
  brOnCastFail := C.brOnCastFail

/-- **The forward conjunct on valid, bounded sources** (`Round5.FwdRef.forward_validT` with
`CastsFwd` for `RefOkB`). -/
theorem forward_validC (TB : Fwd.TypesB (simEnv (BI P hn host))) (C : CastsFwd (BI P hn host) hn)
    (hf : HostFinite host) (hr : FwdRef.HostRespectsT (simEnv (BI P hn host)) hn host)
    (vector : Int.VectorFwd hn P host) :
    R4Fwd.Forward (BI P hn host) hn P host Round4Int.Valid :=
  Fwd.forward_valid5 (FwdRef.oblT TB hf hr (rest_of_casts C vector
    fun _ _ h hb => Fwd.fwd_aggregate5 (Fwd.aggTypesB_of TB)
      (FwdRef.newDataNumB_builtins hn host) (Fwd.initDataZeroB_builtins hn host) h hb))

/-- **`ReadOpenS` from the backward cast obligations and what is left** (`ReadRest`):
`Round5.Read.readOpenS_of_rest` with `CastsBwd` for `RefOkB`. -/
theorem readOpenS_of_casts (K : CastsBwd hn P host) (R : Round5.Read.ReadRest hn P host) :
    Round5.Read.ReadOpenS hn P host :=
  fun i h₀ h₁ h₂ h₃ c w hv hc hf => by
    by_cases h₄ : i ∈ Round5.Read.readDoneS
    · exact Bwd.read_upTo (Round5.Read.read_doneS i h₄ c w hv hc hf)
    by_cases h₅ : i ∈ Round5.Read.readDoneK
    · exact Bwd.read_upTo (K i h₅ c w hv hc hf)
    · exact R i (Round5.Read.lt_of_fires_read hf) h₀ h₁ h₂ h₃ h₄ h₅ c w hv hc hf

/-- **`PartsOkS` from `Open5`**, at an injective encoding, for a finite host, in a
profile where growth may both succeed and fail. -/
theorem partsOkS_of_open5 (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (O : Open5 hn P host) : Round5.Read.PartsOkS hn P host where
  pos := Pos.posTypingNE_of_simd O.simd hn
  fwd := R4Fwd.Forward.mono (fun _ h => h.1)
    (forward_validC (Int.typesB _) O.castsFwd hf (FwdRef2.hostRespectsT_all _ hinj host)
      (SimdTy.vectorFwd_of_ops O.vecOps))
  hostSteps := FwdRef.hostStepsV_of_T hf (FwdRef2.hostRespectsT_all _ hinj host)
  pure := fun i h₀ h₁ h₂ s f is w hv hc hfi =>
    BwdStep.remPure_of_open (Simd.vecAgree_of_ops O.vecOps) (Simd.pureOpenV_of_vtestop
      Simd.pureOpenVtestop) i h₀ h₁ h₂ s f is w hv.read hc hfi
  read := readOpenS_of_casts O.castsBwd Read2.readRest
  step := fun i h6 h₀ h₁ c w hv hc hfi => BwdStep.remStep hPs hPf i h6 h₀ h₁ c w hv.read hc hfi

/-- **`Round5.Task.wholeStepValidOk` from `Open5`**, at every injective encoding, finite
`HostOk` host and `Profile.spec nd r`. Vacuous: see `not_open5`. -/
theorem wholeStepValidOk_of_open5
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), Open5 hn (Profile.spec nd r) host) :
    Round5.Task.wholeStepValidOk :=
  Round5.Read.wholeStepValidOk_of_partsOkS fun H hn hinj host hfin hok nd r =>
    partsOkS_of_open5 hinj hfin (BwdStep.growMaySucceed_spec nd r) (Round4.growMayFail_spec nd r)
      (h H hn hinj host hfin hok nd r)

end Silmaril.Wasm.SpecTec.Sim.Round5.RefOk
