module

public import Silmaril.Wasm.Execution.Core.Soundness.PresBasic
public import Silmaril.Wasm.Execution.Core.Soundness.PresCall

@[expose] public section

/-! # Preservation wiring for the call rules

`PresConcl`-level wrappers for `Step.call`, `callRefNull`, `callRefHostDiv`,
`returnCall`, `callIndirect` and `returnCallIndirect`, in the shape used by the
cases of `Preservation.lean`.
-/

namespace Silmaril.Wasm.Execution.Core.PC

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- Function lookup in a context under a frame context. -/
theorem wireCall_func {s : Store H} {f : Frame} {Cf Ct : Context} (hfr : FrameOk s f Cf)
    (hu : CtxUnder Ct Cf) {x : FuncIdx} {d : DefType} (hx : Ct.funcs[x.toNat]? = some d) :
    ∃ a, f.module.funcs[x.toNat]? = some a ∧ ExternAddrOk s (.func a) (.func d) := by
  have hv : Ct.frameView = Cf.frameView := by rw [hu.eq]; rfl
  rw [Context.eq_of_frameView hv] at hx
  obtain ⟨C₀, lts, hm, -, rfl⟩ := hfr
  cases hm with
  | mk _ _ _ hfuncs =>
    obtain ⟨a, ha, hx⟩ := forall₂_getElem?_right hfuncs hx
    exact ⟨a, ha, hx⟩

/-- `pres_call` with the frame-context invariant. -/
theorem wireCall_pres_call {s : Store H} {f : Frame} {Cf C : Context} {it : InstrType} {x : FuncIdx}
    {a : Nat} {fi : FuncInst H} (hs : StoreOk s) (hfr : FrameOk s f Cf) (hu : CtxUnder C Cf)
    (hC : C.Wf)
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (h : AdminsOk s C [.plain (.call x)] it) :
    AdminsOk s C [.ref (.func a), .callRefType fi.type] it := by
  obtain ⟨it₀, h0, hrep⟩ := single_rep hC (fun C' it₀ h => by
    obtain ⟨_, _, _, _, _, rfl⟩ := inv_call h; rfl) h
  obtain ⟨d, ps, rs, hd, he, rfl⟩ := inv_call h0
  obtain ⟨a', ha', hxa⟩ := wireCall_func hfr hu hd
  rw [hx] at ha'; cases ha'
  have hdok : TyOk C.toTypeCtx d := hC.funcs d (List.mem_of_getElem? hd)
  have hpr := Expand.func_ok hdok he
  refine hrep hpr.1 hpr.2 s _ ?_
  have hfit := StoreOk.func_tyOk hs hf
  obtain ⟨ps', rs', he', hp, hr⟩ := func_sub_data (externAddr_func hxa rfl hf rfl) hfit he
  have hpr' := Expand.func_ok (TyOk.of_empty C.toTypeCtx hfit) he'
  have h1 : AdminsOk s C [.ref (.func a)] ⟨ps'.toList, [], ps'.toList ++
      [.refv (.ref false (Ty.defHeap fi.type))]⟩ := by
    simpa using AdminsOk.frame (AdminsOk.single (AdminOk.ref (C := C) (RefOk.func hf))) hpr'.1
  have h2 : AdminsOk s C [.callRefType fi.type]
      ⟨ps'.toList ++ [.refv (.ref false (Ty.defHeap fi.type))], [], rs'.toList⟩ :=
    subk (.single (.callRefType (TyOk.of_empty _ hfit) he'))
      (ResultSub.append (ResultSub.refl _ _) (.cons (.refv (.refNull .heapRefl)) .nil))
      (ResultSub.refl _ _)
      (ResultOk.append hpr'.1 (rok1 (refT_def_ok (TyOk.of_empty C.toTypeCtx hfit) false))) hpr'.2
  exact subk (seqk h1 h2) (resultSub_weaken hp) (resultSub_weaken hr) hpr.1 hpr.2

/-- `pres_returnCall` with the frame-context invariant. -/
theorem wireCall_pres_returnCall {s : Store H} {f : Frame} {Cf C : Context} {it : InstrType}
    {x : FuncIdx} {a : Nat} {fi : FuncInst H} (hs : StoreOk s) (hfr : FrameOk s f Cf)
    (hu : CtxUnder C Cf) (hC : C.Wf)
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (h : AdminsOk s C [.plain (.returnCall x)] it) :
    AdminsOk s C [.ref (.func a), .returnCallRefType fi.type] it := by
  obtain ⟨it₀, h0, hrep⟩ := single_rep hC (fun C' it₀ h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := inv_returnCall h; rfl) h
  obtain ⟨d, ps, rs, rs', t₃, t₄, hd, he, hret, hrs, hok, rfl⟩ := inv_returnCall h0
  obtain ⟨a', ha', hxa⟩ := wireCall_func hfr hu hd
  rw [hx] at ha'; cases ha'
  have hdok : TyOk C.toTypeCtx d := hC.funcs d (List.mem_of_getElem? hd)
  have hpr := Expand.func_ok hdok he
  refine hrep (ResultOk.append hok.1 hpr.1) hok.2.1 s _ ?_
  have hfit := StoreOk.func_tyOk hs hf
  obtain ⟨ps', rs'', he', hp, hr⟩ := func_sub_data (externAddr_func hxa rfl hf rfl) hfit he
  have hpr' := Expand.func_ok (TyOk.of_empty C.toTypeCtx hfit) he'
  have hrc : TyOk C.toTypeCtx (Ty.refT false (Ty.defHeap fi.type)) :=
    refT_def_ok (TyOk.of_empty C.toTypeCtx hfit) false
  have h1 : AdminsOk s C [.ref (.func a)] ⟨t₃ ++ ps'.toList, [], t₃ ++ ps'.toList ++
      [.refv (.ref false (Ty.defHeap fi.type))]⟩ := by
    simpa using AdminsOk.frame (AdminsOk.single (AdminOk.ref (C := C) (RefOk.func hf)))
      (ResultOk.append hok.1 hpr'.1)
  have h2 : AdminsOk s C [.returnCallRefType fi.type]
      ⟨t₃ ++ ps'.toList ++ [.refv (.ref false (Ty.defHeap fi.type))], [], t₄⟩ :=
    subk (.single (.returnCallRefType (TyOk.of_empty _ hfit) he' hret
        (ResultSub.trans hC.types hpr.2 (resultSub_weaken hr) hrs) hok))
      (ResultSub.append (ResultSub.refl _ _) (.cons (.refv (.refNull .heapRefl)) .nil))
      (ResultSub.refl _ _)
      (ResultOk.append (ResultOk.append hok.1 hpr'.1) (rok1 hrc)) hok.2.1
  exact subk (seqk h1 h2) (ResultSub.append (ResultSub.refl _ _) (resultSub_weaken hp))
    (ResultSub.refl _ _) (ResultOk.append hok.1 hpr.1) hok.2.1

end Silmaril.Wasm.Execution.Core.PC

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

theorem wireCall_call {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (hx : f.module.funcs[x.toNat]? = some a) (hfi : s.funcs[a]? = some fi) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [.plain (.call x)] it →
      PresConcl ⟨s, f, [.plain (.call x)]⟩ ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩
        Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _hts hty
  exact PresConcl.same hs hf hu (PC.wireCall_pres_call hs hf hu hwf hx hfi hty)

theorem wireCall_callRefNull {s : Store H} {f : Frame} {c : Admin} (hc : c.IsCallRef) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [.ref .null, c] it →
      PresConcl ⟨s, f, [.ref .null, c]⟩ ⟨s, f, [.trap]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _hts hty
  exact PresConcl.same hs hf hu (PC.pres_callRefNull hwf hc hty)

theorem wireCall_callRefHostDiv {s : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat} :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct (vals vs ++ [.ref (.func a), c]) it →
      PresConcl ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
        Cf Ct it := by
  intro Cf Ct it hs hf hu _hwf _hts hty
  exact PresConcl.same hs hf hu (PC.pres_callRefHostDiv hty)

theorem wireCall_returnCall {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (hx : f.module.funcs[x.toNat]? = some a) (hfi : s.funcs[a]? = some fi) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [.plain (.returnCall x)] it →
      PresConcl ⟨s, f, [.plain (.returnCall x)]⟩
        ⟨s, f, [.ref (.func a), .returnCallRefType fi.type]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _hts hty
  exact PresConcl.same hs hf hu (PC.wireCall_pres_returnCall hs hf hu hwf hx hfi hty)

theorem wireCall_callIndirect {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [.plain (.callIndirect x y)] it →
      PresConcl ⟨s, f, [.plain (.callIndirect x y)]⟩
        ⟨s, f, [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩),
          .plain (.callRef y)]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _hts hty
  exact PresConcl.same hs hf hu (PC.pres_callIndirect hwf hty)

theorem wireCall_returnCallIndirect {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [.plain (.returnCallIndirect x y)] it →
      PresConcl ⟨s, f, [.plain (.returnCallIndirect x y)]⟩
        ⟨s, f, [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩),
          .plain (.returnCallRef y)]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _hts hty
  exact PresConcl.same hs hf hu (PC.pres_returnCallIndirect hwf hty)

end Silmaril.Wasm.Execution.Core
