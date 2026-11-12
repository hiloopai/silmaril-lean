module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int2.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Simd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Read.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef.Thms

/-!
# Round 5, pass-2 integration: the restated target from `Open2`

* `partsOkS_of_open2`: `PartsOkS` from `Open2`. It combines track fwdref's
  `forward_validT` and `hostStepsV_of_T` (from `HostRespectsT`, with `array.new_data-num`
  proved), `vecAgree_of_ops` and `pureOpenV_of_vtestop`, track read's
  `readOpenS_of_rest`, and pass 1's `remStep`.
* `wholeStepValidOk_of_open2`: `Round5.Task.wholeStepValidOk` from `Open2`.
* `vecAgreeOps_of`, `open2_of_openT`: `Open2` asks no more than `OpenT`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Int2

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **`PartsOkS` from `Open2`**, for a finite host, in a profile where growth may
both succeed and fail. -/
theorem partsOkS_of_open2 (hf : HostFinite host) (hPs : ∀ k a n d, P.growMaySucceed k a n d)
    (hPf : ∀ k a n d, P.growMayFail k a n d) (O : Open2 hn P host) :
    Round5.Read.PartsOkS hn P host where
  pos := Pos.posTypingNE_of_simd O.simd hn
  fwd := R4Fwd.Forward.mono (fun _ h => h.1)
    (FwdRef.forward_validT (Int.typesB _) O.refOk hf O.hostRespects O.vector)
  hostSteps := FwdRef.hostStepsV_of_T hf O.hostRespects
  pure := fun i h₀ h₁ h₂ s f is w hv hc hfi =>
    BwdStep.remPure_of_open (Simd.vecAgree_of_ops O.vecOps) (Simd.pureOpenV_of_vtestop O.vtestop)
      i h₀ h₁ h₂ s f is w hv.read hc hfi
  read := Round5.Read.readOpenS_of_rest O.refOk O.read
  step := fun i h6 h₀ h₁ c w hv hc hfi => BwdStep.remStep hPs hPf i h6 h₀ h₁ c w hv.read hc hfi

/-- **`Round5.Task.wholeStepValidOk` from the leaves still open after round 5, pass 2**, at
every injective encoding, finite `HostOk` host and `Profile.spec nd r`. -/
theorem wholeStepValidOk_of_open2
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), Open2 hn (Profile.spec nd r) host) :
    Round5.Task.wholeStepValidOk :=
  Round5.Read.wholeStepValidOk_of_partsOkS fun H hn hinj host hfin hok nd r =>
    partsOkS_of_open2 hfin (BwdStep.growMaySucceed_spec nd r) (Round4.growMayFail_spec nd r)
      (h H hn hinj host hfin hok nd r)

/-- Family V's `VecAgree` gives `VecAgreeOps` (a sub-structure). -/
theorem vecAgreeOps_of {env : Env} (V : Vec.VecAgree env P) : Simd.VecAgreeOps env P where
  intUnOp := V.intUnOp
  floatUnOp := V.floatUnOp
  intBinOp := V.intBinOp
  floatBinOp := V.floatBinOp
  intTernOp := V.intTernOp
  floatTernOp := V.floatTernOp
  intRelOp := V.intRelOp
  floatRelOp := V.floatRelOp
  shiftOp := V.shiftOp
  bitmask := V.bitmask
  swizzle := V.swizzle
  relaxedSwizzle := V.relaxedSwizzle
  shuffle := V.shuffle
  extUnOp := V.extUnOp
  extBinOp := V.extBinOp
  extTernOp := V.extTernOp
  narrow := V.narrow
  convert := V.convert

/-- **`Open2` asks no more than `OpenT`** (and so than pass 1's `Int.Open`,
`Round5.FwdRef.openT_of_open`). -/
theorem open2_of_openT (O : FwdRef.OpenT hn P host) : Open2 hn P host where
  simd := O.simd
  refOk := O.refOk
  hostRespects := O.hostRespects
  vector := O.vector
  vecOps := vecAgreeOps_of O.vecAgree
  vtestop := O.pureOpen 64 (by simp [BwdStep.pureOpenR5])
  read := fun i _ h₀ h₁ h₂ h₃ _ _ c w hv hc hfi => O.read i h₀ h₁ h₂ h₃ c w hv.r hc hfi

end Silmaril.Wasm.SpecTec.Sim.Round5.Int2
