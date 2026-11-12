module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.Dispatch

/-!
# Round 5: the forward recursion on bounded configurations

`forward5` is `R4Fwd.forward_all` at the concrete `B`, with the motive
`Round4.Bounded c` (instead of `StoreOk c.store`) and with **no** `Whole.Assumptions`,
`Integrate.Extra` or `Open4`: every family structure is the one proved for the concrete `B`,
and the rules whose earlier proofs used a refuted field come from `Obl`. The context rules pass
`Bounded` to the inner configuration (`bounded_ctxt*`).

`forward_valid5` is the forward conjunct `R4Fwd.Forward … Round4Int.Valid` from `Obl`, and
`parts_of_obl` assembles `Round4Int.Parts` with it in place of the `fwd` field.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Fwd

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4 (Bounded)
open Round4Int (BI)
open FwdMem (FwdUp fwdUp_of_fwdP)

variable {H : Type}

/-- **The forward simulation from bounded configurations, up to call annotations, for the
concrete `B`, from the per-rule obligations `Obl`.** No refuted bundle is assumed. -/
theorem forward5 {hn : H → String} {P : Profile} {host : HostSemantics H}
    (O : Obl (BI P hn host) hn P host) {c c' : Config H} (h : Step P host c c') :
    Bounded c → FwdUp (simEnv (BI P hn host)) hn c c' :=
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  have Ty := Typing.ctrlTyping_simEnv (BI P hn host)
  have St := Typing.stateTyping_simEnv (BI P hn host)
  have X := Typing.exnTyping_simEnv' (BI P hn host)
  have U {c c' : Config H} : FwdP (simEnv (BI P hn host)) hn c c' →
      FwdUp (simEnv (BI P hn host)) hn c c' := fwdUp_of_fwdP
  Step.rec (motive := fun c c' _ => Bounded c → FwdUp (simEnv (BI P hn host)) hn c c')
    (fun hs _ => U (IntNumeric.fwd_parametric T hs))
    (fun hs _ => U (fwd_numeric5 hs))
    (fun hs hb => U (fwd_vector5 O hs hb))
    (fun hs _ => U (State.fwd_variable_ _ T St hs))
    (fun hs hb => U (Memory.fwd_table_bounded _ T St (ConfigOk.memTyping_simEnv _)
      (RefOk.growFuns_builtins hn host) (ConfigOk.instTyping_simEnv _) hs hb.store.tables))
    (fun hs hb => U (fwd_memory5 hs hb))
    (fun hs hb => U (fwd_reference5 O hs hb))
    (fun hs hb => U (O.aggregate _ _ hs hb))
    (fun _ hne ih hb => FwdMem.fwdUp_ctxtInstrs T hne (ih (bounded_ctxtInstrs hb)))
    (fun _ ih hb => FwdMem.fwdUp_ctxtLabel T (ih (bounded_ctxtLabel hb)))
    (fun _ ih hb => FwdMem.fwdUp_ctxtHandler T (ih (bounded_ctxtHandler hb)))
    (fun _ ih hb => FwdMem.fwdUp_ctxtFrame T (ih (bounded_ctxtFrame hb)))
    (fun h₁ h₂ hb => U (O.block _ _ _ _ _ _ _ h₁ h₂ hb))
    (fun h₁ h₂ hb => U (O.loop _ _ _ _ _ _ _ h₁ h₂ hb))
    (fun h₁ _ => U (fwd_ifTrue _ T Ty h₁))
    (fun _ => U (fwd_ifFalse _ T Ty))
    (fun _ => U (fwd_labelVals _ T))
    (fun h₁ h₂ _ => U (fwd_brLabelZero _ T Ty h₁ h₂))
    (fun h₁ _ => U (fwd_brLabelSucc _ T Ty h₁))
    (fun _ => U (fwd_brHandler _ T Ty))
    (fun h₁ _ => U (fwd_brIfTrue _ T Ty h₁))
    (fun _ => U (fwd_brIfFalse _ T Ty))
    (fun h₁ _ => U (fwd_brTableLt _ T Ty h₁))
    (fun h₁ _ => U (fwd_brTableGe _ T Ty h₁))
    (fun _ => U (fwd_brOnNullNull _ T Ty))
    (fun h₁ _ => U (fwd_brOnNullAddr _ T Ty h₁))
    (fun _ => U (fwd_brOnNonNullNull _ T Ty))
    (fun h₁ _ => U (fwd_brOnNonNullAddr _ T Ty h₁))
    (fun h₁ hb => U ((O.brOnCast _ _ _ _ _ _ hb).1 h₁))
    (fun h₁ hb => U ((O.brOnCast _ _ _ _ _ _ hb).2 h₁))
    (fun h₁ hb => U ((O.brOnCastFail _ _ _ _ _ _ hb).1 h₁))
    (fun h₁ hb => U ((O.brOnCastFail _ _ _ _ _ _ hb).2 h₁))
    (fun h₁ h₂ _ => U (fwd_call5 h₁ h₂))
    (fun h₁ _ => U (fwd_callRefNull _ T Ty h₁))
    (fun h₁ h₂ h₃ h₄ h₅ hb => U (O.callRefFunc _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ hb))
    (fun h₁ h₂ h₃ h₄ h₅ h₆ hb =>
      U (O.callRefHost _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ hb))
    (fun h₁ h₂ h₃ h₄ h₅ h₆ hb =>
      U (O.callRefHostDiv _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ hb))
    (fun h₁ h₂ _ => U (fwd_returnCall5 h₁ h₂))
    (fun h₁ _ => U (fwd_returnCallRefLabel _ T Ty h₁))
    (fun h₁ _ => U (fwd_returnCallRefHandler _ T Ty h₁))
    (fun h₁ _ => U (fwd_returnCallRefFrameNull _ T Ty h₁))
    (fun h₁ h₂ h₃ h₄ hb => O.returnCallRefFrameAddr _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ hb)
    (fun _ => U (fwd_callIndirect _ T Ty))
    (fun _ => U (fwd_returnCallIndirect _ T Ty))
    (fun h₁ _ => U (fwd_frameVals _ T h₁))
    (fun h₁ _ => U (fwd_returnFrame _ T Ty h₁))
    (fun _ => U (fwd_returnLabel _ T))
    (fun _ => U (fwd_returnHandler _ T))
    (fun h₁ h₂ h₃ hb => U (O.throw _ _ _ _ _ _ _ h₁ h₂ h₃ hb))
    (fun _ => U (Exn.fwd_throwRefNull _ T))
    (fun h₁ _ => U (Exn.fwd_throwRefInstrs _ T X h₁))
    (fun _ => U (Exn.fwd_throwRefLabel _ T X))
    (fun _ => U (Exn.fwd_throwRefFrame _ T X))
    (fun _ => U (Exn.fwd_throwRefHandlerEmpty _ T X))
    (fun h₁ h₂ hb => U (O.throwRefHandlerCatch _ _ _ _ _ _ _ _ h₁ h₂ hb))
    (fun h₁ h₂ hb => U (O.throwRefHandlerCatchRef _ _ _ _ _ _ _ _ h₁ h₂ hb))
    (fun _ => U (Exn.fwd_throwRefHandlerCatchAll _ T X))
    (fun _ => U (Exn.fwd_throwRefHandlerCatchAllRef _ T X))
    (fun h₁ hb => U (O.throwRefHandlerNext _ _ _ _ _ _ h₁ hb))
    (fun h₁ h₂ hb => U (O.tryTable _ _ _ _ _ _ _ _ h₁ h₂ hb))
    (fun _ => U (Exn.fwd_handlerVals _ T))
    (fun h₁ _ => U (fwd_trapInstrs _ T h₁))
    (fun _ => U (fwd_trapLabel _ T))
    (fun _ => U (fwd_trapHandler _ T))
    (fun _ => U (fwd_trapFrame _ T))
    h

/-- **The forward conjunct on valid, bounded sources, from `Obl`** (the `fwd` field of
`Round4Int.Parts`). -/
theorem forward_valid5 {hn : H → String} {P : Profile} {host : HostSemantics H}
    (O : Obl (BI P hn host) hn P host) :
    R4Fwd.Forward (BI P hn host) hn P host Round4Int.Valid := by
  intro c c' hv _ hc hc' h
  obtain ⟨d', he, -, hs⟩ := forward5 O h hv.2 hc hc'
  exact ⟨d', he, hs⟩

/-- `Round4Int.Parts` with its `fwd` field from `Obl`. -/
theorem parts_of_obl {hn : H → String} {P : Profile} {host : HostSemantics H}
    (pos : Round4.PosTyping (BI P hn host) hn)
    (succTyped : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → Bounded c →
      Bounded c' → Step P host c c' → Typed (simEnv (BI P hn host)) hn c')
    (O : Obl (BI P hn host) hn P host)
    (fam : Round4Int.FamBwdV (simEnv (BI P hn host)) hn P host)
    (rem : Round4Read.RemainingV (simEnv (BI P hn host)) hn P host) :
    Round4Int.Parts hn P host :=
  ⟨pos, succTyped, forward_valid5 O, fam, rem⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd
