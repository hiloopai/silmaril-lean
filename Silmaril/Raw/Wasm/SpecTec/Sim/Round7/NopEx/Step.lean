module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NopEx.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Head

/-!
# a run-domain witness with exports: call-free steps ignore the host (unrefined)

`step_noHost_of_callFree`: on code without `call_ref` (`callFreeL`), a step for any host is a step
for `noHost`. It is Silmaril's `Step.of_noHost` read backwards: the induction is the same, the
context rules pass call-freeness to the inner code, and the two host-call rules are ruled out
because they fire at a `call_ref`. One case per rule, kept unrefined.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NopEx

open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

theorem callFreeL_append : ∀ l r : List Admin, callFreeL (l ++ r) = (callFreeL l && callFreeL r)
  | [], _ => rfl
  | a :: l, r => by simp only [List.cons_append, callFreeL, callFreeL_append l r, Bool.and_assoc]

theorem callFreeA_of_isCallRef {a : Admin} (h : a.IsCallRef) : callFreeA a = false := by
  cases a with
  | plain i => cases i <;> first | rfl | exact absurd h id
  | callRefType _ => rfl
  | _ => exact absurd h id

theorem not_callFree_call {vs : List Val} {r : Ref} {a : Admin} (h : a.IsCallRef) :
    callFreeL (vals vs ++ [.ref r, a]) ≠ true := by
  simp [callFreeL_append, callFreeL, callFreeA, callFreeA_of_isCallRef h]

/-- **On call-free code, a step for any host is a step for `noHost`.** -/
theorem step_noHost_of_callFree {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hcf : callFreeL c.code = true) :
    Step P (fun _ _ _ _ => False) c c' := by
  induction h with
  | parametric h => exact .parametric h
  | numeric h => exact .numeric h
  | vector h => exact .vector h
  | «variable» h => exact .«variable» h
  | table h => exact .table h
  | memory h => exact .memory h
  | reference h => exact .reference h
  | aggregate h => exact .aggregate h
  | ctxtInstrs _ hne ih =>
      simp only [callFreeL_append, Bool.and_eq_true] at hcf
      exact .ctxtInstrs (ih hcf.1.2) hne
  | ctxtLabel _ ih =>
      simp only [callFreeL, callFreeA, Bool.and_true] at hcf
      exact .ctxtLabel (ih hcf)
  | ctxtHandler _ ih =>
      simp only [callFreeL, callFreeA, Bool.and_true] at hcf
      exact .ctxtHandler (ih hcf)
  | ctxtFrame _ ih =>
      simp only [callFreeL, callFreeA, Bool.and_true] at hcf
      exact .ctxtFrame (ih hcf)
  | block hbt hm => exact .block hbt hm
  | loop hbt hm => exact .loop hbt hm
  | ifTrue hc => exact .ifTrue hc
  | ifFalse => exact .ifFalse
  | labelVals => exact .labelVals
  | brLabelZero hl hn => exact .brLabelZero hl hn
  | brLabelSucc hl => exact .brLabelSucc hl
  | brHandler => exact .brHandler
  | brIfTrue hc => exact .brIfTrue hc
  | brIfFalse => exact .brIfFalse
  | brTableLt hi => exact .brTableLt hi
  | brTableGe hi => exact .brTableGe hi
  | brOnNullNull => exact .brOnNullNull
  | brOnNullAddr hv => exact .brOnNullAddr hv
  | brOnNonNullNull => exact .brOnNonNullNull
  | brOnNonNullAddr hv => exact .brOnNonNullAddr hv
  | brOnCastSucceed h => exact .brOnCastSucceed h
  | brOnCastFail h => exact .brOnCastFail h
  | brOnCastFailSucceed h => exact .brOnCastFailSucceed h
  | brOnCastFailFail h => exact .brOnCastFailFail h
  | call hx hf => exact .call hx hf
  | callRefNull hc => exact .callRefNull hc
  | callRefFunc hc hf he hn hcode => exact .callRefFunc hc hf he hn hcode
  | callRefHost hc' _ _ _ _ _ => exact absurd hcf (not_callFree_call hc')
  | callRefHostDiv hc' _ _ _ _ _ => exact absurd hcf (not_callFree_call hc')
  | returnCall hx hf => exact .returnCall hx hf
  | returnCallRefLabel hc => exact .returnCallRefLabel hc
  | returnCallRefHandler hc => exact .returnCallRefHandler hc
  | returnCallRefFrameNull hc => exact .returnCallRefFrameNull hc
  | returnCallRefFrameAddr hc hf he hn => exact .returnCallRefFrameAddr hc hf he hn
  | callIndirect => exact .callIndirect
  | returnCallIndirect => exact .returnCallIndirect
  | frameVals hn => exact .frameVals hn
  | returnFrame hn => exact .returnFrame hn
  | returnLabel => exact .returnLabel
  | returnHandler => exact .returnHandler
  | throw ht he hn => exact .throw ht he hn
  | throwRefNull => exact .throwRefNull
  | throwRefInstrs hne => exact .throwRefInstrs hne
  | throwRefLabel => exact .throwRefLabel
  | throwRefFrame => exact .throwRefFrame
  | throwRefHandlerEmpty => exact .throwRefHandlerEmpty
  | throwRefHandlerCatch he ht => exact .throwRefHandlerCatch he ht
  | throwRefHandlerCatchRef he ht => exact .throwRefHandlerCatchRef he ht
  | throwRefHandlerCatchAll => exact .throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef => exact .throwRefHandlerCatchAllRef
  | throwRefHandlerNext h => exact .throwRefHandlerNext h
  | tryTable hbt hm => exact .tryTable hbt hm
  | handlerVals => exact .handlerVals
  | trapInstrs hne => exact .trapInstrs hne
  | trapLabel => exact .trapLabel
  | trapHandler => exact .trapHandler
  | trapFrame => exact .trapFrame

end Silmaril.Wasm.SpecTec.Sim.Round7.NopEx
