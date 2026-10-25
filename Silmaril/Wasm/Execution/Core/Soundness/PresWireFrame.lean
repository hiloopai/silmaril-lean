module

public import Silmaril.Wasm.Execution.Core.Soundness.PresBasic
public import Silmaril.Wasm.Execution.Core.Soundness.PresReturn
public import Silmaril.Wasm.Execution.Core.Soundness.PresControl

@[expose] public section

/-! # Preservation wiring for the frame/return rules

`PresConcl`-level wrappers for `Step.frameVals`, `returnFrame`, `returnLabel`
and `returnHandler`, in the shape used by the cases of `Preservation.lean`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

theorem StoreTypesOk.heapTypesOk {s : Store H} (h : StoreTypesOk s) : StoreHeapTypesOk s := h

/-- Values typed in a frame's context can be retyped at a closed supertype. -/
theorem frame_transfer_wire {s : Store H} {fi : Frame} (hs : StoreOk s) (hh : StoreHeapTypesOk s) :
    ∀ C' : Context, FrameOk s fi C' → ∀ (v : Val) (t t' : CValType), ValOk s v t →
      Sub C'.toTypeCtx t t' → TyOk {} t' → ValOk s v t' := by
  intro C' hf v t t' hv hsub ht'
  have hTC : ∀ d ∈ C'.toTypeCtx.types, TyOk {} d := by
    intro d hd
    obtain ⟨C₀, hm, -⟩ := hf.inv
    rw [hf.types_eq] at hd
    exact hm.inv.2.1 d hd
  exact ValOk.transferRet hs hh hTC hv hsub ht'

theorem pres_frameVals {s : Store H} {f fi : Frame} {n : Nat} {vs : List Val}
    (_hn : vs.length = n) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [.frame n fi (vals vs)] it →
      PresConcl ⟨s, f, [.frame n fi (vals vs)]⟩ ⟨s, f, vals vs⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu _hwf hts hty
  exact PresConcl.same hs hf hu
    (Step.frameVals_presCtl hty (frame_transfer_wire hs hts.heapTypesOk))

theorem pres_returnFrame {s : Store H} {f fi : Frame} {n : Nat} {vs' vs : List Val}
    {rest : List Admin} (hn : vs.length = n) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s →
      AdminsOk s Ct [.frame n fi (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)] it →
      PresConcl ⟨s, f, [.frame n fi (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)]⟩
        ⟨s, f, vals vs⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu _hwf hts hty
  exact PresConcl.same hs hf hu (Step.returnFrame_presRet hty hs hts.heapTypesOk hn)

theorem pres_returnLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {vs : List Val} {rest : List Admin} :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s →
      AdminsOk s Ct [.label n cont (vals vs ++ [.plain .return_] ++ rest)] it →
      PresConcl ⟨s, f, [.label n cont (vals vs ++ [.plain .return_] ++ rest)]⟩
        ⟨s, f, vals vs ++ [.plain .return_]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _hts hty
  exact PresConcl.same hs hf hu (Step.returnLabel_presRet hty hwf)

theorem pres_returnHandler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch}
    {vs : List Val} {rest : List Admin} :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s →
      AdminsOk s Ct [.handler n cs (vals vs ++ [.plain .return_] ++ rest)] it →
      PresConcl ⟨s, f, [.handler n cs (vals vs ++ [.plain .return_] ++ rest)]⟩
        ⟨s, f, vals vs ++ [.plain .return_]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf hts hty
  have hreg := AdminsOk.regular hs hts hwf hty
  exact PresConcl.same hs hf hu (Step.returnHandler_presRet hty hwf hreg.2.1)

end Silmaril.Wasm.Execution.Core
