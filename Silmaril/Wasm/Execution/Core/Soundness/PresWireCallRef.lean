module

public import Silmaril.Wasm.Execution.Core.Soundness.PresBasic
public import Silmaril.Wasm.Execution.Core.Soundness.PresCall

@[expose] public section

/-! # Preservation wiring for the `call_ref` rules

`PresConcl`-level wrappers for `Step.callRefFunc`, `callRefHost`,
`returnCallRefLabel`, `returnCallRefHandler`, `returnCallRefFrameNull` and
`returnCallRefFrameAddr`, in the shape used by the cases of `Preservation.lean`,
on top of the `AdminsOk`-level lemmas of `PresCall.lean` (namespace `PC`).

The `PC` lemmas are stated for a context `C` with `CtxOk s f C`. The typing
context `Ct` of `preservation_gen` need not have all the frame's locals, so we
move to `wireCallRef_ctx Ct Cf` (`Ct` with the locals of the frame context `Cf`),
which satisfies `CtxOk`, is well formed, lies above `Ct` (`CtxLe`) and under `Cf`
(`CtxUnder`).

`returnCallRefFrameAddr` relies on two documented deviations: the reduct resolves an
index annotation against the exited frame's module (`Admin.retToCallIn`), and
`Moduleinst_ok` requires `RECS = []` (`FrameOk.recs_nil`).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## The bridge to `CtxOk` -/

/-- The typing context `Ct` with the locals of the frame context `Cf`. -/
abbrev wireCallRef_ctx (Ct Cf : Context) : Context := Ct.reshape Cf.locals Ct.labels Ct.return_

theorem wireCallRef_le {Ct Cf : Context} (hu : CtxUnder Ct Cf) :
    CtxLe Ct (wireCallRef_ctx Ct Cf) := ⟨rfl, hu.le⟩

theorem wireCallRef_eq {Ct Cf : Context} (hu : CtxUnder Ct Cf) :
    wireCallRef_ctx Ct Cf = Cf.reshape Cf.locals Ct.labels Ct.return_ :=
  hu.reshape_eq _ _ _

theorem wireCallRef_under {Ct Cf : Context} (hu : CtxUnder Ct Cf) :
    CtxUnder (wireCallRef_ctx Ct Cf) Cf :=
  ⟨wireCallRef_eq hu, LocalsLe.refl _⟩

theorem wireCallRef_wf {Ct Cf : Context} (hu : CtxUnder Ct Cf) (hwf : Ct.Wf) (hCf : Cf.Wf) :
    (wireCallRef_ctx Ct Cf).Wf := by
  refine ⟨hwf.types, hwf.tags, hwf.globals, hwf.tables, hwf.funcs, ?_, hwf.labels, hwf.return_, hwf.elems⟩
  intro lt hlt
  have h := hCf.locals lt hlt
  rw [← hu.toTypeCtx] at h
  exact h

theorem wireCallRef_ctxOk {s : Store H} {f : Frame} {Ct Cf : Context} (hf : FrameOk s f Cf)
    (hu : CtxUnder Ct Cf) : CtxOk s f (wireCallRef_ctx Ct Cf) := by
  refine ⟨⟨Cf, hf, ?_, rfl⟩, (FrameOk.ctx_fields hf).2.2, hf.set⟩
  rw [wireCallRef_eq hu]
  rfl

/-- Lift an `AdminsOk`-level step lemma (stated for a `CtxOk` context) to `PresConcl`. -/
theorem wireCallRef_lift {s s' : Store H} {f : Frame} {is is' : List Admin} {Cf Ct : Context}
    {it : InstrType} (hs : StoreOk s) (hf : FrameOk s f Cf) (hu : CtxUnder Ct Cf)
    (hwf : CtxWf Ct) (hts : StoreTypesOk s) (hty : AdminsOk s Ct is it)
    (k : ∀ C : Context, CtxOk s f C → C.Wf → AdminsOk s C is it →
      StoreOk s' ∧ Extend s s' ∧ AdminsOk s' C is' it) :
    PresConcl ⟨s, f, is⟩ ⟨s', f, is'⟩ Cf Ct it := by
  obtain ⟨hs', hext, h⟩ := k (wireCallRef_ctx Ct Cf) (wireCallRef_ctxOk hf hu)
    (wireCallRef_wf hu hwf (hf.ctxWf hs hts)) (AdminsOk.weaken (wireCallRef_le hu) hty)
  exact ⟨Cf, wireCallRef_ctx Ct Cf, hs', hext, FrameOk.extend_of_storeOk hs hext hf, rfl,
    wireCallRef_under hu, wireCallRef_le hu, h⟩

/-! ## Runtime `call_ref` annotations are valid in `{}` -/

/-- With `AdminOk.callRefType` requiring `TyOk {} d`, the `hcd` hypothesis of the
`PC` lemmas follows from the typing of the redex. -/
theorem wireCallRef_hcd {s : Store H} {C : Context} (hC : C.Wf) {vs : List Val} {a : Nat}
    {c : Admin} {it : InstrType} (hcr : c.IsCallRef)
    (h : AdminsOk s C (vals vs ++ [.ref (.func a), c]) it) :
    ∀ d, c = .callRefType d → TyOk {} d := by
  intro d hd
  have e : vals vs ++ [.ref (.func a), c] = vals (vs ++ [.ref (.func a)]) ++ [c] := by
    simp [vals, Val.toAdmin]
  rw [e] at h
  obtain ⟨_, _, _, _, hc0, _⟩ := PC.redex_rep hC (PC.callRef_inits hcr) h
  subst hd
  cases hc0 with
  | callRefType hok _ => exact hok

/-! ## The wrappers -/

theorem pres_wireCallRef_callRefFunc {s : Store H} {f : Frame} {c : Admin}
    {vs : List Val} {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)} {code : Func}
    (hc : c.IsCallRef) (hfa : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (hcode : fi.code = .wasm code) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct (vals vs ++ [.ref (.func a), c]) it →
      PresConcl ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
        ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
          [.label rs.length [] (expression code.body)]]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf hts hty
  refine wireCallRef_lift hs hf hu hwf hts hty fun C hcok hC h => ⟨hs, Extend.refl hs, ?_⟩
  exact PC.pres_callRefFunc hs hts hcok hC hc (wireCallRef_hcd hC hc h) hfa he hn hcode h

theorem pres_wireCallRef_callRefHost {host : HostSemantics H} (hhost : HostOk host)
    {s s' : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat} {fi : FuncInst H}
    {ps rs : Ty (.list .val)} {hh : H} {r : Result}
    (hc : c.IsCallRef) (hfa : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (hcode : fi.code = .host hh)
    (hres : host hh s vs (.returned s' r)) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct (vals vs ++ [.ref (.func a), c]) it →
      PresConcl ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ ⟨s', f, r.toAdmin⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf hts hty
  refine wireCallRef_lift hs hf hu hwf hts hty fun C hcok hC h => ?_
  exact PC.pres_callRefHost hhost hs hts hcok hC hc (wireCallRef_hcd hC hc h) hfa he hn hcode
    hres h

theorem pres_wireCallRef_returnCallRefLabel {s : Store H} {f : Frame} {k : Nat}
    {cont : List Instr} {vs : List Val} {c : Admin} {rest : List Admin}
    (hc : c.IsReturnCallRef) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [.label k cont (vals vs ++ [c] ++ rest)] it →
      PresConcl ⟨s, f, [.label k cont (vals vs ++ [c] ++ rest)]⟩ ⟨s, f, vals vs ++ [c]⟩
        Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _hts hty
  exact PresConcl.same hs hf hu (PC.pres_returnCallRefLabel hwf hc hty)

theorem pres_wireCallRef_returnCallRefHandler {s : Store H} {f : Frame} {k : Nat}
    {cs : List Catch} {vs : List Val} {c : Admin} {rest : List Admin}
    (hc : c.IsReturnCallRef) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [.handler k cs (vals vs ++ [c] ++ rest)] it →
      PresConcl ⟨s, f, [.handler k cs (vals vs ++ [c] ++ rest)]⟩ ⟨s, f, vals vs ++ [c]⟩
        Cf Ct it := by
  intro Cf Ct it hs hf hu hwf hts hty
  exact PresConcl.same hs hf hu (PC.pres_returnCallRefHandler hs hts hwf hc hty)

theorem pres_wireCallRef_returnCallRefFrameNull {s : Store H} {f fi : Frame} {k : Nat}
    {vs : List Val} {c : Admin} {rest : List Admin} (_hc : c.IsReturnCallRef) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s →
      AdminsOk s Ct [.frame k fi (vals vs ++ [.ref .null, c] ++ rest)] it →
      PresConcl ⟨s, f, [.frame k fi (vals vs ++ [.ref .null, c] ++ rest)]⟩ ⟨s, f, [.trap]⟩
        Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _hts hty
  exact PresConcl.same hs hf hu (PC.pres_returnCallRefFrameNull hwf hty)

/-! ## `return_call_ref` out of a frame -/

/-- Frame contexts have no `RECS` (`Moduleinst_ok` requires `RECS = []`). -/
theorem FrameOk.recs_nil {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C) :
    C.recs = [] := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := h
  exact hm.recs_nil

theorem wireCallRef_hcd_ret {s : Store H} {C : Context} (hC : C.Wf) {vs' vs : List Val} {a : Nat}
    {c : Admin} {rest : List Admin} {ts : List CValType} (hts : ResultOk C.toTypeCtx ts)
    (hcr : c.IsReturnCallRef)
    (h : AdminsOk s C (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest) (.plain [] ts)) :
    ∀ d, c = .returnCallRefType d → TyOk {} d := by
  intro d hd
  have e0 : vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest =
      (vals (vs' ++ vs ++ [.ref (.func a)]) ++ [c]) ++ rest := by
    simp [vals, Val.toAdmin]
  rw [e0] at h
  obtain ⟨m, ys₁, ys₂, hpre, -, -⟩ := AdminsOk.append_inv hC (.inr hts) h
  obtain ⟨_, _, _, _, hc1, _⟩ := PC.redex_rep hC (PC.returnCallRef_inits hcr) hpre
  subst hd
  cases hc1 with
  | returnCallRefType hok _ _ _ _ => exact hok

theorem pres_wireCallRef_returnCallRefFrameAddr {s : Store H} {f fi : Frame} {k : Nat}
    {vs' vs : List Val} {a : Nat} {c : Admin} {rest : List Admin} {fn : FuncInst H}
    {ps rs : Ty (.list .val)} (hc : c.IsReturnCallRef) (hfa : s.funcs[a]? = some fn)
    (he : Expand fn.type (.func ps rs)) (hn : vs.length = ps.length) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s →
      AdminsOk s Ct [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)] it →
      PresConcl ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩
        ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fi.module]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf hts hty
  refine wireCallRef_lift hs hf hu hwf hts hty fun C hcok hC h => ⟨hs, Extend.refl hs, ?_⟩
  obtain ⟨it₀, h0, hrep⟩ := PC.single_rep hC PC.frame_inits h
  cases h0 with
  | @frame _ C' _ _ _ ts hfr _ hb hok =>
    have hW := PC.frame_ctx_wf hs hts hfr hok
    exact hrep (by simp) (PC.resultOk_weaken hok) s _
      (PC.pres_returnCallRefFrameAddr hs hts hcok hC hc
        (wireCallRef_hcd_ret hW (PC.resultOk_weaken hok) hc hb) hfa he hn hfr hfr.recs_nil hok hb)

end Silmaril.Wasm.Execution.Core
