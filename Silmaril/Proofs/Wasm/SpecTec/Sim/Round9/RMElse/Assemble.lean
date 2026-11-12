module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMRead.Thms
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.RMElse.RefOk

/-!
# Round 9, rm: `firesRead` from the backward firing at 68 pairs

At round 6's primitives (`CodeErase.EraseAll.hyps_sim`), `fires_erase_else` gives round 8's
`firesRead` (`RMCode.FiresEraseD` at the 28 `otherwise` rules of `Step_read`) from
`ElseBwd.ElseBwdDRest`. So `RMRead.RestMSHCJ` follows from `ElseBwdDRest`, and
`Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDPK`.

`elseBwdDRest_of_left` proves 64 of the 68 pairs of `ElseBwdDRest` (48 simple pairs, 16 chain
pairs of two levels), so `wholeStepValidRM` follows from `OpenRMRestDPL`, whose `elseLeft` asks
the backward firing at the 4 pairs of `leftPairsC` only.

`RefOk` proves those four (`elseBwdDLeftC_sim`), so `ElseBwdDRest` holds at round 6's primitives
(`elseBwdDRest_sim`), `RMRead.RestMSHCJ` holds outright (`restMSHCJ_sim`), and `wholeStepValidRM`
follows from `OpenRMRestDPM`: `forward`, `castsFwd` and `castsBwd` outside `EasyP`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMElse

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {hn : H → String} {host : HostSemantics H}

/-- **`RMRead.RestMSHCJ` from the backward firing at the 68 pairs.** -/
theorem restMSHCJ_of_rest (hR : ElseBwd.ElseBwdDRest (simEnv (Prims.builtins P hn host))) :
    RMRead.RestMSHCJ hn P host where
  firesRead _ hi := firesEraseD_else (Round8.CodeErase.EraseAll.hyps_sim P hn host) hR hn hi

/-- **`OpenRMRestDPK` gives `RMRead.OpenRMRestDPJ`.** -/
theorem openRMRestDPJ_of_K (O : OpenRMRestDPK hn P host) : RMRead.OpenRMRestDPJ hn P host :=
  ⟨O.forward, restMSHCJ_of_rest O.elseBwd, O.castsFwd, O.castsBwd⟩

/-- **`Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDPK`.** -/
theorem wholeStepValidRM_of_restDPK
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice),
          OpenRMRestDPK hn (Profile.spec nd r) host) :
    Round7.MemSimd.Task.wholeStepValidRM :=
  RMRead.wholeStepValidRM_of_restDPJ fun H hn hinj host hf hh nd r =>
    openRMRestDPJ_of_K (h H hn hinj host hf hh nd r)

/-- **`OpenRMRestDPL` gives `OpenRMRestDPK`.** -/
theorem openRMRestDPK_of_L (O : OpenRMRestDPL hn P host) : OpenRMRestDPK hn P host :=
  ⟨O.forward, elseBwdDRest_of_left (Round8.CodeErase.EraseAll.hyps_sim P hn host) O.elseLeft,
    O.castsFwd, O.castsBwd⟩

/-- **`Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDPL`.** -/
theorem wholeStepValidRM_of_restDPL
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice),
          OpenRMRestDPL hn (Profile.spec nd r) host) :
    Round7.MemSimd.Task.wholeStepValidRM :=
  wholeStepValidRM_of_restDPK fun H hn hinj host hf hh nd r =>
    openRMRestDPK_of_L (h H hn hinj host hf hh nd r)

/-- **The backward firing along code erasure at all 68 pairs**, at round 6's primitives. -/
theorem elseBwdDRest_builtins : ElseBwd.ElseBwdDRest (simEnv (Prims.builtins P hn host)) :=
  elseBwdDRest_sim (Round8.CodeErase.EraseAll.hyps_sim P hn host)

/-- **`firesRead` holds**: round 8's `FiresEraseD` at the 28 `otherwise` rules of `Step_read`. -/
theorem restMSHCJ_sim : RMRead.RestMSHCJ hn P host :=
  restMSHCJ_of_rest elseBwdDRest_builtins

/-- **`OpenRMRestDPM` gives `RMRead.OpenRMRestDPJ`.** -/
theorem openRMRestDPJ_of_M (O : OpenRMRestDPM hn P host) : RMRead.OpenRMRestDPJ hn P host :=
  ⟨O.forward, restMSHCJ_sim, O.castsFwd, O.castsBwd⟩

/-- **`Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDPM`** (`forward`, `castsFwd`,
`castsBwd` outside `EasyP`). -/
theorem wholeStepValidRM_of_restDPM
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice),
          OpenRMRestDPM hn (Profile.spec nd r) host) :
    Round7.MemSimd.Task.wholeStepValidRM :=
  RMRead.wholeStepValidRM_of_restDPJ fun H hn hinj host hf hh nd r =>
    openRMRestDPJ_of_M (h H hn hinj host hf hh nd r)

end Silmaril.Wasm.SpecTec.Sim.Round9.RMElse
