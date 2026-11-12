module

public import Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.Defs

/-!
# SpecTec ↔ Core 3.0, round 6, track agreety-elim: the introduction half of `AgreeTy`

`RefOkV.AgreeTy` has two introduction fields (`okIntro`, `subIntro`) and two elimination fields
(`okElim`, `subElim`). Track agreety-elim proves the elimination fields on the concrete builtins
(`TyElim.okElim_BI`, `TyElim.subElim_BI`), so `AgreeTy` on the concrete builtins reduces to
`AgreeTyIntro`, its two introduction fields, verbatim (`TyElim.agreeTy_of_intro`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.TyElim

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Validation
open Silmaril.SpecTec.Equiv.Validation (tyV)

/-- **The introduction half of `RefOkV.AgreeTy`**: its fields `okIntro` and `subIntro`, verbatim. -/
structure AgreeTyIntro (env : Env) : Prop where
  /-- `Reftype_ok {}` holds at a bounded, Core-valid reference type. -/
  okIntro : ∀ (O : ElseI) (rt : CRefType), Round4.tyBnd rt = true → TyOk {} rt →
    Round6.Reading.DDerivesB env O "Reftype_ok" "%|-%:OK" [] (.tuple [RefOkV.ctxEmptyV, tyV rt])
  /-- `Reftype_sub {}` holds between bounded, Core-valid reference types in Core's `Sub {}`. -/
  subIntro : ∀ (O : ElseI) (p rt : CRefType), Round4.tyBnd p = true → Round4.tyBnd rt = true →
    TyOk {} p → TyOk {} rt → Sub {} p rt →
    Round6.Reading.DDerivesB env O "Reftype_sub" "%|-%<:%" []
      (.tuple [RefOkV.ctxEmptyV, tyV p, tyV rt])

end Silmaril.Wasm.SpecTec.Sim.Round6.TyElim
