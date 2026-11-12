module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FwdMem.Wide

/-!
# The forward recursion on the round-3 fragment

`forward_upTo`: `Integrate.forward_wide`'s recursion over Core's `Step`, on `Covered3 mem`, up to
call annotations. The base cases are round 2's (`fwdUp_of_fwdP`), except the memory constructors
(`fwd_memory3`: every scalar load and store when `mem`) and `return_call_ref-frame-addr`
(`fwdUp_returnCallRefFrameAddr`); the context rules are `fwdUp_ctxt*`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.FwdMem

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **The forward simulation on the round-3 fragment, up to call annotations.** Under the
families' `Assumptions`, `Integrate.Extra`, `FloatB P B`, `BytesFuns` and `FwdSimdAgg.VVB B`, and `SliceTotal` when
`mem`, every Core step from a configuration in `Covered3 mem` is a SpecTec `Step` of the images in
`simEnv B` to the image of a typed configuration `ConfigEq`-related to Core's successor, whenever
both configurations are typed. -/
theorem forward_upTo {B : Builtins} {hn : H → String} {P : Numerics.Profile}
    {host : HostSemantics H} (A : Whole.Assumptions B hn host) (X : Integrate.Extra (simEnv B))
    (hF : Floats.FloatB P B) (Bf : BytesFuns (simEnv B)) (hV : FwdSimdAgg.VVB B) {mem : Bool}
    (hT : mem = true → SliceTotal) {c c' : Config H}
    (h : Step P host c c') : Covered3 mem c → FwdUp (simEnv B) hn c c' :=
  have T := A.typing
  have Ty := A.ctrlTyping
  have U {c c' : Config H} : FwdP (simEnv B) hn c c' → FwdUp (simEnv B) hn c c' := fwdUp_of_fwdP
  Step.rec (motive := fun c c' _ => Covered3 mem c → FwdUp (simEnv B) hn c c')
    (fun hs _ => U (IntNumeric.fwd_parametric T hs))
    (fun hs _ => U (Whole.fwd_numeric_covered A hF hs))
    (fun hs hc => U (fwd_vector3 A.intB hV hs hc.1))
    (fun hs _ => U (State.fwd_variable_ B T A.state hs))
    (fun hs hc => U (Memory.fwd_table_bounded B T A.state X.mem X.grow X.inst hs hc.2.2.tables))
    (fun hs hc => U (fwd_memory3 A X hF Bf hT hs hc))
    (fun hs _ => U (RefsGC.fwd_reference B T A.rTyping A.rFuns A.rStore A.refOk hs))
    (fun hs hc => U (FwdSimdAgg.fwd_aggregate_wide' hV T A.rTyping A.rStore X.agg hs hc.2.2.aggs
      hc.2.1 fun _ ha => aggOpenW_of_open3 (hc.1.mem ha)))
    (fun _ hne ih hc => fwdUp_ctxtInstrs T hne (ih (covered3_mid hc)))
    (fun _ ih hc => fwdUp_ctxtLabel T (ih (covered3_label hc)))
    (fun _ ih hc => fwdUp_ctxtHandler T (ih (covered3_handler hc)))
    (fun _ ih hc => fwdUp_ctxtFrame T (ih (covered3_frame hc)))
    (fun h₁ h₂ _ => U (fwd_block B T Ty A.ctrlState h₁ h₂))
    (fun h₁ h₂ _ => U (fwd_loop B T Ty A.ctrlState h₁ h₂))
    (fun h₁ _ => U (fwd_ifTrue B T Ty h₁))
    (fun _ => U (fwd_ifFalse B T Ty))
    (fun _ => U (fwd_labelVals B T))
    (fun h₁ h₂ _ => U (fwd_brLabelZero B T Ty h₁ h₂))
    (fun h₁ _ => U (fwd_brLabelSucc B T Ty h₁))
    (fun _ => U (fwd_brHandler B T Ty))
    (fun h₁ _ => U (fwd_brIfTrue B T Ty h₁))
    (fun _ => U (fwd_brIfFalse B T Ty))
    (fun h₁ _ => U (fwd_brTableLt B T Ty h₁))
    (fun h₁ _ => U (fwd_brTableGe B T Ty h₁))
    (fun _ => U (fwd_brOnNullNull B T Ty))
    (fun h₁ _ => U (fwd_brOnNullAddr B T Ty h₁))
    (fun _ => U (fwd_brOnNonNullNull B T Ty))
    (fun h₁ _ => U (fwd_brOnNonNullAddr B T Ty h₁))
    (fun h₁ _ => U (RefsGC.fwd_brOnCastSucceed B T A.rTyping A.rStore A.refOk h₁))
    (fun h₁ _ => U (RefsGC.fwd_brOnCastFail B T A.rTyping A.rStore A.refOk h₁))
    (fun h₁ _ => U (RefsGC.fwd_brOnCastFailSucceed B T A.rTyping A.rStore A.refOk h₁))
    (fun h₁ _ => U (RefsGC.fwd_brOnCastFailFail B T A.rTyping A.rStore A.refOk h₁))
    (fun h₁ h₂ _ => U (fwd_call B T Ty A.ctrlState h₁ h₂))
    (fun h₁ _ => U (fwd_callRefNull B T Ty h₁))
    (fun h₁ h₂ h₃ h₄ h₅ _ => U (fwd_callRefFunc B T Ty A.ctrlState A.ctrlCall A.ctrlHost
      h₁ h₂ h₃ h₄ h₅))
    (fun h₁ h₂ h₃ h₄ h₅ h₆ _ => U (fwd_callRefHost B T Ty A.ctrlState A.ctrlCall A.ctrlHost
      h₁ h₂ h₃ h₄ h₅ h₆))
    (fun h₁ h₂ h₃ h₄ h₅ h₆ _ => U (fwd_callRefHostDiv B T Ty A.ctrlState A.ctrlCall A.ctrlHost
      h₁ h₂ h₃ h₄ h₅ h₆))
    (fun h₁ h₂ _ => U (fwd_returnCall B T Ty A.ctrlState h₁ h₂))
    (fun h₁ _ => U (fwd_returnCallRefLabel B T Ty h₁))
    (fun h₁ _ => U (fwd_returnCallRefHandler B T Ty h₁))
    (fun h₁ _ => U (fwd_returnCallRefFrameNull B T Ty h₁))
    (fun h₁ h₂ h₃ h₄ _ =>
      fwdUp_returnCallRefFrameAddr T Ty A.ctrlState A.ctrlCall h₁ h₂ h₃ h₄)
    (fun _ => U (fwd_callIndirect B T Ty))
    (fun _ => U (fwd_returnCallIndirect B T Ty))
    (fun h₁ _ => U (fwd_frameVals B T h₁))
    (fun h₁ _ => U (fwd_returnFrame B T Ty h₁))
    (fun _ => U (fwd_returnLabel B T))
    (fun _ => U (fwd_returnHandler B T))
    (fun h₁ h₂ h₃ _ => U (Exn.fwd_throw B T A.exnTyping A.exnHelpers h₁ h₂ h₃))
    (fun _ => U (Exn.fwd_throwRefNull B T))
    (fun h₁ _ => U (Exn.fwd_throwRefInstrs B T A.exnTyping h₁))
    (fun _ => U (Exn.fwd_throwRefLabel B T A.exnTyping))
    (fun _ => U (Exn.fwd_throwRefFrame B T A.exnTyping))
    (fun _ => U (Exn.fwd_throwRefHandlerEmpty B T A.exnTyping))
    (fun h₁ h₂ _ => U (Exn.fwd_throwRefHandlerCatch B T A.exnTyping A.exnHelpers h₁ h₂))
    (fun h₁ h₂ _ => U (Exn.fwd_throwRefHandlerCatchRef B T A.exnTyping A.exnHelpers h₁ h₂))
    (fun _ => U (Exn.fwd_throwRefHandlerCatchAll B T A.exnTyping))
    (fun _ => U (Exn.fwd_throwRefHandlerCatchAllRef B T A.exnTyping))
    (fun h₁ _ => U (Exn.fwd_throwRefHandlerNext B T A.exnTyping A.exnHelpers h₁))
    (fun h₁ h₂ _ => U (Exn.fwd_tryTable B T A.exnTyping A.exnHelpers h₁ h₂))
    (fun _ => U (Exn.fwd_handlerVals B T))
    (fun h₁ _ => U (fwd_trapInstrs B T h₁))
    (fun _ => U (fwd_trapLabel B T))
    (fun _ => U (fwd_trapHandler B T))
    (fun _ => U (fwd_trapFrame B T))
    h

end Silmaril.Wasm.SpecTec.Sim.FwdMem
