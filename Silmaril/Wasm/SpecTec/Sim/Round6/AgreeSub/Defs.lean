module

public import Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.Defs

/-!
# SpecTec ↔ Core 3.0, round 6, track agreety-subintro: the four fields of `AgreeTy`, as statements

`Round6.RefOkV.AgreeTy` (open) bundles four statements about SpecTec's `Reftype_ok {}` and
`Reftype_sub {}` under `DDerivesB`. This file names each field's statement on its own, so that
the fields can be proved (or refuted) separately and reassembled
(`Round6.AgreeSub.agreeTy_iff`). Each definition is the field's type, verbatim.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Round6.RefOkV (ctxEmptyV CohH refHeap SubE)

/-- `AgreeTy.okIntro`: `Reftype_ok {}` holds at a bounded, Core-valid reference type. -/
def OkIntro (env : Env) : Prop :=
  ∀ (O : ElseI) (rt : CRefType), Round4.tyBnd rt = true → TyOk {} rt →
    Round6.Reading.DDerivesB env O "Reftype_ok" "%|-%:OK" [] (.tuple [ctxEmptyV, tyV rt])

/-- `AgreeTy.subIntro`: `Reftype_sub {}` holds between bounded, Core-valid reference types in
Core's `Sub {}`. -/
def SubIntro (env : Env) : Prop :=
  ∀ (O : ElseI) (p rt : CRefType), Round4.tyBnd p = true → Round4.tyBnd rt = true →
    TyOk {} p → TyOk {} rt → Sub {} p rt →
    Round6.Reading.DDerivesB env O "Reftype_sub" "%|-%<:%" [] (.tuple [ctxEmptyV, tyV p, tyV rt])

/-- `AgreeTy.okElim`: `Reftype_ok {}` at the image of a reference type makes its heap type
coherent. -/
def OkElim (env : Env) : Prop :=
  ∀ (O : ElseI) (rt : CRefType),
    Round6.Reading.DDerivesB env O "Reftype_ok" "%|-%:OK" [] (.tuple [ctxEmptyV, tyV rt]) →
      CohH (refHeap rt)

/-- `AgreeTy.subElim`: `Reftype_sub {}` from the image of a reference type is `SubE`, to an
image. -/
def SubElim (env : Env) : Prop :=
  ∀ (O : ElseI) (p : CRefType) (w : Value),
    Round6.Reading.DDerivesB env O "Reftype_sub" "%|-%<:%" [] (.tuple [ctxEmptyV, tyV p, w]) →
      ∃ rt, w = tyV rt ∧ SubE p rt

end Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub
