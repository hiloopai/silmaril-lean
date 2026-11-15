module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Tail

/-!
# Callee frames and the closure's returning behaviours (proofs)

By least-fixpoint induction every returning behaviour of `Shape.close wasmHOpenXP` is in `GoodCX`
(`close_le_goodCX`):

* a Wasm callee whose body ends in a flow: `evalLXPh_fwd` in its frame, the frame left with the
  values or the exception (`calleeRun_flow`);
* a Wasm callee whose body ends in a pending tail call: the body's logged run to Core's pending
  tail call, the frame left by `return_call_ref-label` and `return_call_ref-frame-addr`, then the
  tail callee's logged run in the caller's frame (`calleeRun_tail`); a host tail callee is its
  one event there;
* a host callee: its one event (`hEvStep_host_callRef`, any `call_ref` form).

Hence `close_ret_evRun`: a returning closed behaviour with a consistent log is a Core run of the
call with exactly that log, ending at the values or the thrown exception.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallX (tailFlow)
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP FrameP bodyCallXP)
open Silmaril.Wasm.Abstract.HostEvalP (hostCallXP hostCallXP_fixpoint)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Leaving a callee's frame -/

/-- A callee frame left with the values its body's flow hands back. -/
theorem exit_frame_vals {s' : Store H} {f F : Frame} {n : Nat} {c' : List Admin} {o : Outcome}
    {bfl : Binaryen.Flow} {w : List Val} {ob : Option Nat}
    (he : o.Ends c') (hm : FlowMatch bfl o) (hvs : bfl.retVals = some w)
    (hok : FlowOkE true [n] n ob bfl) (hob : ob = none ∨ ob = some n) :
    Steps P NH ⟨s', f, [.frame n F [.label n [] c']]⟩ ⟨s', f, vals (w.take n).reverse⟩ := by
  have hnorm : ∀ ws, bfl = .normal ws → ws.length = n := by
    rintro ws rfl
    exact length_of_ends hok hob
  obtain ⟨s'', res, hret, hK⟩ := frame_ends (P := P) (host := NH) (f := f) (n := n) (F := F) he
    (funcPost_of_match (s₂ := s') (F := F) hm hvs (retVals_length hok hob hvs) hnorm)
  obtain ⟨rfl, rfl⟩ := hK
  exact hret

/-- **A callee frame left with the values or the exception of its body's flow.** -/
theorem exit_frame_ans {s' : Store H} {f F : Frame} {n : Nat} {c' : List Admin} {o : Outcome}
    {bfl fl : Binaryen.Flow} {b : List Val ⊕ Nat} {ob : Option Nat}
    (he : o.Ends c') (hm : FlowMatch bfl o) (hx : exitFlow n bfl = some fl)
    (hend : endOfFlow fl s' = .ret b s') (hok : FlowOkE true [n] n ob bfl)
    (hob : ob = none ∨ ob = some n) :
    Steps P NH ⟨s', f, [.frame n F [.label n [] c']]⟩ ⟨s', f, ansCode b⟩ := by
  rcases bfl with w | ⟨_ | j, w⟩ | w | _ | t
  · simp only [exitFlow, Option.some.injEq] at hx
    subst hx
    simp only [endOfFlow, End.ret.injEq] at hend
    obtain ⟨rfl, -⟩ := hend
    exact exit_frame_vals he hm rfl hok hob
  · simp only [exitFlow, Option.some.injEq] at hx
    subst hx
    simp only [endOfFlow, End.ret.injEq] at hend
    obtain ⟨rfl, -⟩ := hend
    exact exit_frame_vals he hm rfl hok hob
  · simp [exitFlow] at hx
  · simp only [exitFlow, Option.some.injEq] at hx
    subst hx
    simp only [endOfFlow, End.ret.injEq] at hend
    obtain ⟨rfl, -⟩ := hend
    exact exit_frame_vals he hm rfl hok hob
  · simp only [exitFlow, Option.some.injEq] at hx
    subst hx
    cases hend
  · simp only [exitFlow, Option.some.injEq] at hx
    subst hx
    simp only [endOfFlow, End.ret.injEq] at hend
    obtain ⟨rfl, -⟩ := hend
    have hc : c' = throwing t := by
      rcases o with _ | _ | _ | _ | a' | _ | _ <;> simp only [FlowMatch] at hm
      subst hm
      exact he
    subst hc
    exact (Relation.ReflTransGen.single (Step.ctxtFrame Step.throwRefLabel)).tail Step.throwRefFrame

/-- The check of a callee body, in the callee's frame. -/
theorem body_chk {tags : List TagInst} {s : Store H} {a : Nat} {us : List Val} {fi : FuncInst H}
    {fn : Func} {ps rs : List Validation.CValType} (hS : StoreChkE (ehExt tags) s.funcs)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length) :
    ∃ ob, (ob = none ∨ ob = some rs.length) ∧
      chkE (ehExt tags) s.funcs (Frame.forCall fi.module us fn.locals).module
        (Frame.forCall fi.module us fn.locals).locals.length rs.length [rs.length]
        (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
  obtain ⟨ob, hb, hob⟩ := endsAt_eq (hS a fi fn ps rs hfi hcode hty)
  have hlen : (Frame.forCall fi.module us fn.locals).locals.length =
      ps.length + fn.locals.length := forCall_length _ _ hn
  exact ⟨ob, hob, by rw [hlen]; exact hb⟩

/-- Entering a Wasm callee from any `call_ref` form. -/
theorem steps_enter_callee {s : Store H} {f : Frame} {a : Nat} {us : List Val} {fi : FuncInst H}
    {fn : Func} {ps rs : List Validation.CValType} {c : Admin} (hcr : c.IsCallRef)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length) :
    Steps P NH ⟨s, f, vals us ++ [.ref (.func a), c]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module us fn.locals)
        [.label rs.length [] (expression fn.body)]]⟩ := by
  obtain ⟨ps', rs', hex, hpl, hrl⟩ := expand_of_funcType hty
  rw [← hrl]
  exact .single (Step.callRefFunc hcr hfi hex (hn.trans hpl.symm) hcode)

/-- **A Wasm callee whose body ends in a flow**: its logged body run, the frame left with the
values or the exception. -/
theorem calleeRun_flow {tags : List TagInst} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s' : Store H} {a : Nat} {us : List Val} {fi : FuncInst H}
    {fn : Func} {ps rs : List Validation.CValType} {f₂ : Frame} {bfl fl : Binaryen.Flow}
    {q : List (Call (wasmHostSig H))} {b : List Val ⊕ Nat}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (d : EvalOXP (hostCallXP host) s (Frame.forCall fi.module us fn.locals) []
      (Binaryen.liftInstrs fn.body) (s', f₂, .flow bfl))
    (cl : CoreLP tags P host s (Frame.forCall fi.module us fn.locals) []
      (Binaryen.liftInstrs fn.body) (s', f₂, .flow bfl) q)
    (hx : exitFlow rs.length bfl = some fl) (hend : endOfFlow fl s' = .ret b s')
    (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs) (hn : us.length = ps.length) :
    CalleeRun P host s a us q s' b := by
  intro f c hcr
  obtain ⟨-, hA, -⟩ := evalOXP_host_good (P := P) hH hE d hts
  obtain ⟨ob, hob, hb'⟩ := body_chk hS hfi hcode hty hn
  obtain ⟨hok, -, -⟩ := hA hS hb'
  have hwb := cl hS hb'
  rw [Binaryen.lowerList_liftInstrs] at hwb
  obtain ⟨s'', f'', c', o, hrun, he, hm⟩ := hwb
  have hne : bfl ≠ .trap := by
    rintro rfl
    simp only [exitFlow, Option.some.injEq] at hx
    subst hx
    cases hend
  obtain ⟨rfl, rfl, hfm⟩ := match_of_matchP hne hm
  have inner := evRun_wrap (Wfr rs.length f) (hW_fr rs.length f) hrun
  have ex := exit_frame_ans (P := P) (f := f) (F := f'') he hfm hx hend hok hob
  have := evRun_trans (evRun_of_free (steps_enter_callee hcr hfi hcode hty hn))
    (evRun_trans inner (evRun_of_free ex))
  simpa [vals] using this

/-- **A Wasm callee whose body ends in a pending tail call**: its logged body run to Core's
pending tail call, the frame left (`return_call_ref-label`, `return_call_ref-frame-addr`), then
the tail callee's logged run in the caller's frame. -/
theorem calleeRun_tail {tags : List TagInst} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₁ s₂ s' : Store H} {a a' n : Nat} {us args : List Val}
    {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType} {f₂ : Frame}
    {q qc : List (Call (wasmHostSig H))} {b b' : List Val ⊕ Nat}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (d : EvalOXP (hostCallXP host) s (Frame.forCall fi.module us fn.locals) []
      (Binaryen.liftInstrs fn.body) (s₁, f₂, .tail a' args n))
    (cl : CoreLP tags P host s (Frame.forCall fi.module us fn.locals) []
      (Binaryen.liftInstrs fn.body) (s₁, f₂, .tail a' args n) q)
    (hcallee : ∀ (fi₂ : FuncInst H) (ps₂ rs₂ : List Validation.CValType),
      s₁.funcs[a']? = some fi₂ → Validation.DefType.funcType? fi₂.type = some (ps₂, rs₂) →
      TagsOk tags s₁ → StoreChkE (ehExt tags) s₁.funcs → args.length = ps₂.length →
      CalleeRun P host s₁ a' args qc s₂ b)
    (hb : ∀ ws, b = .inl ws → ws.length ≤ n)
    (hend : tailAns rs.length n b s₂ = .ret b' s')
    (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs) (hn : us.length = ps.length) :
    CalleeRun P host s a us (q ++ qc) s' b' := by
  intro f c hcr
  obtain ⟨t₁, hA, -⟩ := evalOXP_host_good (P := P) hH hE d hts
  obtain ⟨ob, hob, hb'⟩ := body_chk hS hfi hcode hty hn
  obtain ⟨hok, hinv, hw⟩ := hA hS hb'
  have hnr : n = rs.length := hok
  obtain ⟨fi₂, ps₂, rs₂, hfi₂, hty₂, hargs, -⟩ := hw a' args n rfl
  obtain ⟨ps₂', rs₂', hex₂, hpl₂, -⟩ := expand_of_funcType hty₂
  have hS₁ : StoreChkE (ehExt tags) s₁.funcs := hinv.1.2.1 hS
  rw [hnr] at hend hb
  obtain ⟨rfl, rfl⟩ := tailAns_self hend hb
  have hwb := cl hS hb'
  rw [Binaryen.lowerList_liftInstrs] at hwb
  obtain ⟨s'', f'', c', o, hrun, he, hm⟩ := hwb
  obtain ⟨vs₁, c₀, rfl, hc₀, rfl, rfl⟩ := matchP_tail_iff.mp hm
  obtain ⟨-, rest, rfl⟩ := he
  have inner := evRun_wrap (Wfr rs.length f) (hW_fr rs.length f) hrun
  have ex := frame_tail_exit (P := P) (host := NH) (s := s'') (f := f) (k := rs.length)
    (F := f'') (vs₁ := vs₁) (rest := rest) hc₀ hfi₂ hex₂ (hargs.trans hpl₂.symm)
  have hcl := hcallee fi₂ ps₂ rs₂ hfi₂ hty₂ t₁ hS₁ hargs f _
    (isCallRef_retToCallIn hc₀ f''.module)
  have := evRun_trans (evRun_of_free (steps_enter_callee hcr hfi hcode hty hn))
    (evRun_trans inner (evRun_trans (evRun_of_free ex) hcl))
  simpa [vals] using this

/-- **An answered host call is its one event**, any `call_ref` form, any frame. -/
theorem hEvStep_host_callRef {s s' : Store H} {f : Frame} {a : Nat} {fi : FuncInst H} {hh : H}
    {ps rs : Validation.Ty (.list .val)} {us : List Val} {r : Result} {c : Admin}
    (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Validation.Expand fi.type (.func ps rs))
    (hn : us.length = ps.length) (hcode : fi.code = .host hh)
    (hans : host hh s us (.returned s' r)) :
    HEvStep P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩
      (some ⟨(hh, s, us), (s', r)⟩) ⟨s', f, r.toAdmin⟩ :=
  ⟨.top [] [], a, SingleThreaded.decompose?_redex hc hf he hn hcode, rfl, hans,
    by simp [SingleThreaded.Ctx.fill, vals]⟩

/-- A finished resolution ending in a return is a prefix resolution. -/
theorem subst_ret_pre {sh : Silmaril.Games.Abstract.Shape} {c : sh.ClosedMod} {R : Type}
    {x : List (Call (sh.E ⊕ₛ sh.self))} {e : End sh.S R} {y : CallBeh sh.E sh.S R}
    (h : Shape.Subst c x e y) {b : R} {s : sh.S} (hy : y.2 = .ret b s) :
    Shape.SubstPre c x y.1 ∧ y.2 = e := by
  induction h with
  | nil e => exact ⟨.nil, rfl⟩
  | ext _ ih =>
    obtain ⟨h₁, h₂⟩ := ih hy
    exact ⟨.ext h₁, h₂⟩
  | int hm _ ih =>
    obtain ⟨h₁, h₂⟩ := ih hy
    exact ⟨.int hm h₁, h₂⟩
  | intTrap _ => cases hy
  | intDiv _ => cases hy

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
