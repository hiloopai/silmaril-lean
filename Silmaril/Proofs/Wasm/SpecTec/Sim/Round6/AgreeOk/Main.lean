module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.AgreeOk.Trans
public import Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Agree.Thms

/-!
# Round 6: `AgreeTy.okIntro`, proved

`okIntro`: at a bounded reference type valid in Core's `{}`, SpecTec's `Reftype_ok {}` holds
under `DDerivesB` in `simEnv (BI P hn host)`, under every reading of `otherwise`. Core's
derivation is made canonical (`tyOkB_empty`: Silmaril's checker rebuilds every subtyping premise
inside a group with bounded middle types) and then read rule for rule (`okD_of`).

With `subIntro_BI`, `AgreeTy` in `simEnv (BI P hn host)` reduces to its
two elimination fields (`agreeTy_of_elim`), and so does the round-6 target at the backend reading
(`wholeStepValidR_backend_of_elim`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk

open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4Int (BI)
open Round4 (tyBnd)

variable {H : Type}

/-- `{}` has no `RECS`. -/
theorem recsBnd_empty : RecsBnd {} := fun _ h => absurd h List.not_mem_nil

/-- **`AgreeTy.okIntro`**: `Reftype_ok {}` holds at every bounded reference type valid in
Core's `{}`, in `simEnv (BI P hn host)`, under every reading of `otherwise`. -/
theorem okIntro {P : Profile} {hn : H → String} {host : HostSemantics H} (O : ElseI)
    (rt : CRefType) (hb : tyBnd rt = true) (h : TyOk {} rt) :
    Round6.Reading.DDerivesB (simEnv (BI P hn host)) O "Reftype_ok" "%|-%:OK" []
      (.tuple [RefOkV.ctxEmptyV, tyV rt]) :=
  okD_of O (tyOkB_empty h hb) recsBnd_empty hb

/-- **`AgreeTy.okIntro` holds** in `simEnv (BI P hn host)`, for every profile. -/
theorem okIntro_BI (P : Profile) (hn : H → String) (host : HostSemantics H) :
    AgreeSub.OkIntro (simEnv (BI P hn host)) :=
  fun O rt hb h => okIntro O rt hb h

/-- **`AgreeTy` in `simEnv (BI P hn host)` from its two elimination fields**: `okIntro` is
`okIntro_BI`, `subIntro` is `subIntro_BI`. -/
theorem agreeTy_of_elim {P : Profile} {hn : H → String} {host : HostSemantics H}
    (hokE : AgreeSub.OkElim (simEnv (BI P hn host)))
    (hsubE : AgreeSub.SubElim (simEnv (BI P hn host))) : RefOkV.AgreeTy (simEnv (BI P hn host)) :=
  AgreeSub.agreeTy_of_rest (okIntro_BI P hn host) hokE hsubE

/-- **The round-6 target at the backend reading, from the two elimination fields of
`AgreeTy`** (`okElim`, `subElim`), at every encoding, host and profile `Profile.spec nd r`. -/
theorem wholeStepValidR_backend_of_elim
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice),
          AgreeSub.OkElim (simEnv (BI (Profile.spec nd r) hn host)) ∧
            AgreeSub.SubElim (simEnv (BI (Profile.spec nd r) hn host))) :
    Round6.Task.wholeStepValidR Int.backend :=
  Int.wholeStepValidR_backend_of_agreeTy fun H hn hinj host hf hh nd r =>
    agreeTy_of_elim (h H hn hinj host hf hh nd r).1 (h H hn hinj host hf hh nd r).2

end Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk
