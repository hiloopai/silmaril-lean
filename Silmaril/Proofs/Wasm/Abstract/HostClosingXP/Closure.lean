module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Frame

/-!
# The returning behaviours of the canonical closure are logged Core runs (proofs)

* `close_le_goodCX`: every closed behaviour is in `GoodCX`, by least-fixpoint induction: a Wasm
  callee's body is `evalLXPh_fwd` in its frame (`calleeRun_flow`, `calleeRun_tail`), a host
  callee's one import call is one event (`hEvStep_host_callRef`);
* `close_ret_evRun`: a returning closed behaviour with a consistent log is a Core run of the call
  with exactly that log, to its values or its thrown exception;
* `wasmEvFunXP_ret_evRun`: the same for an invocation.
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

/-- **Every closed behaviour is in `GoodCX`**: least-fixpoint induction. -/
theorem close_le_goodCX {tags : List TagInst} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) : Shape.close (wasmHOpenXP (H := H)) ≤ GoodCX tags P host := by
  refine OrderHom.lfp_le _ ?_
  rintro a s us y ⟨x, hx, hS⟩ b s'' hy hq
  rcases hx with ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hfi, hc, hty, hE', hxf, rfl⟩ |
    ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, b₀, l, hfi, hc, hty, hE', rfl⟩ |
    ⟨fi, hh, ps, rs, s', r, fl, hfi, hc, hty, hxf, rfl⟩
  · -- a Wasm body ending in a flow
    obtain ⟨hpre, he⟩ := subst_ret_pre hS hy
    have hend : endOfFlow fl s' = .ret b s'' := he.symm.trans hy
    have hs'' : s'' = s' := by
      rcases fl <;> simp_all [endOfFlow]
    subst hs''
    obtain ⟨d, cl⟩ := evalLXPh_fwd (P := P) hH hE hE' y.1 hpre hq
    refine ⟨fi, ps, rs, bfl, fl, hfi, hty, ?_, hxf, hend,
      fun hts hSt hn => calleeRun_flow hH hE hfi hc hty d (cl hts) hxf hend hts hSt hn⟩
    rw [hostCallXP_fixpoint]
    exact .inl ⟨fi, fn, ps, rs, f₂, s'', .flow bfl, hfi, hc, hty, d, .flow⟩
  · -- a Wasm body ending in a pending tail call, made at the frame
    obtain ⟨hpre, he⟩ := subst_ret_pre hS hy
    have hend : tailAns rs.length n b₀ s₂ = .ret b s'' := he.symm.trans hy
    obtain ⟨q₁, c₁, hq₁, hpre₁, hm⟩ := substPre_last hpre
    rw [hq₁, cons_append] at hq
    obtain ⟨d, cl⟩ := evalLXPh_fwd (P := P) hH hE hE' q₁ hpre₁ hq.1
    obtain ⟨fi₂, ps₂, rs₂, hfi₂, hty₂, hn₂⟩ := evalLXPh_tail_wf hE' a' args n rfl
    obtain ⟨fi₂', ps₂', rs₂', bfl₂, fl₂, hfi₂', hty₂', hC₂, hx₂, hend₂, hrun₂⟩ := hm _ _ rfl hq.2
    obtain rfl : fi₂' = fi₂ := Option.some.inj (hfi₂'.symm.trans hfi₂)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty₂'.symm.trans hty₂))
    have htf : tailFlow n (ansFlow b₀) = tailFlow n bfl₂ := hn₂ ▸ tailFlow_ansFlow hx₂ hend₂
    have hb : ∀ ws, b₀ = .inl ws → ws.length ≤ n := by
      rintro ws rfl
      obtain ⟨-, -, -, -, -, hle, -⟩ := goodCX_inl (tags := tags) (P := P) hm hq.2 hfi₂ hty₂
      exact hn₂ ▸ hle
    have hend' := hend
    unfold tailAns at hend'
    rw [htf] at hend'
    split at hend'
    · rename_i flo hfo
      have hs'' : s'' = s₂ := by
        rcases flo <;> simp_all [endOfFlow]
      subst hs''
      refine ⟨fi, ps, rs, tailFlow n bfl₂, flo, hfi, hty, ?_, hfo, hend', ?_⟩
      · rw [hostCallXP_fixpoint]
        exact .inl ⟨fi, fn, ps, rs, f₂, s₁, .tail a' args n, hfi, hc, hty, d,
          .tail hC₂ (retVals_or_abrupt hx₂)⟩
      · intro hts hSt hn
        rw [hq₁]
        have hcallee : ∀ (fi₃ : FuncInst H) (ps₃ rs₃ : List Validation.CValType),
            s₁.funcs[a']? = some fi₃ → Validation.DefType.funcType? fi₃.type = some (ps₃, rs₃) →
            TagsOk tags s₁ → StoreChkE (ehExt tags) s₁.funcs → args.length = ps₃.length →
            CalleeRun P host s₁ a' args c₁ s'' b₀ := by
          intro fi₃ ps₃ rs₃ hfi₃ hty₃ ht hS₁ hargs
          have e₁ := Option.some.inj (hfi₃.symm.trans hfi₂)
          subst e₁
          have e₂ := (Prod.mk.inj (Option.some.inj (hty₃.symm.trans hty₂))).1
          subst e₂
          exact hrun₂ ht hS₁ hargs
        exact calleeRun_tail hH hE hfi hc hty d (cl hts) hcallee hb hend hts hSt hn
    · cases hend'
  · -- a host function: one import call
    cases hS with
    | ext h =>
      cases h
      have hm : host hh s us (.returned s' r) := hq _ List.mem_cons_self
      have hs'' : s'' = s' := by
        rcases fl <;> simp_all [endOfFlow]
      subst hs''
      refine ⟨fi, ps, rs, resFlow r, fl, hfi, hty, ?_, hxf, hy, ?_⟩
      · rw [hostCallXP_fixpoint]
        exact .inr ⟨fi, hh, r, hfi, hc, hm, rfl⟩
      · intro _ _ hn g c hcr
        obtain ⟨ps', rs', he', hpl, hrl⟩ := expand_of_funcType hty
        have hstep := hEvStep_host_callRef (P := P) (f := g) hcr hfi he' (hn.trans hpl.symm) hc hm
        rcases r with w | t | _
        · simp only [resFlow, exitFlow, Option.some.injEq] at hxf
          subst hxf
          simp only [endOfFlow, End.ret.injEq] at hy
          obtain ⟨rfl, -⟩ := hy
          have hw := hH.arity s a fi hh ps rs us w s'' hfi hc hty hm
          have hwr : (w.reverse.take rs.length).reverse = w := by
            rw [List.take_of_length_le (by simp [hw])]
            simp
          rw [ansCode, hwr]
          exact .event hstep (.refl _)
        · exact absurd hm (hH.noThrow _ _ _ _ _)
        · simp only [resFlow, exitFlow, Option.some.injEq] at hxf
          subst hxf
          cases hy

/-- **A returning closed behaviour with a consistent log is a Core run of the call** with
exactly that log, in any frame and any `call_ref` form, to its values or its thrown exception,
every profile. -/
theorem close_ret_evRun {tags : List TagInst} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {a : Nat} {s s₂ : Store H} {us : List Val}
    {b : List Val ⊕ Nat} {c₁ : List (Call (wasmHostSig H))} {fi : FuncInst H}
    {ps rs : List Validation.CValType}
    (hm : (c₁, .ret b s₂) ∈ Shape.close wasmHOpenXP a s us) (hc : Cons host c₁)
    (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs) (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length) :
    CalleeRun P host s a us c₁ s₂ b := by
  obtain ⟨fi', ps', rs', -, -, hfi', hty', -, -, -, hrun⟩ :=
    close_le_goodCX (P := P) hH hE a s us hm _ _ rfl hc
  obtain rfl : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty'.symm.trans hty))
  exact hrun hts hS hn

/-- The invoked function's type, from a returning behaviour. -/
theorem close_ret_fn {tags : List TagInst} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {a : Nat} {s s₂ : Store H} {us : List Val}
    {b : List Val ⊕ Nat} {c₁ : List (Call (wasmHostSig H))}
    (hm : (c₁, .ret b s₂) ∈ Shape.close wasmHOpenXP a s us) (hc : Cons host c₁) :
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), s.funcs[a]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) := by
  obtain ⟨fi, ps, rs, -, -, hfi, hty, -⟩ :=
    close_le_goodCX (tags := tags) (P := Silmaril.Wasm.Numerics.Profile.spec) hH hE a s us hm _ _ rfl hc
  exact ⟨fi, ps, rs, hfi, hty⟩

theorem invoke_eq {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    (hfi : s.funcs[a]? = some fi) :
    invoke s a vs = ⟨s, {}, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩ := by
  simp [invoke, hfi]

theorem invokeOk_length {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    {ps rs : List Validation.CValType} (hok : InvokeOk s a vs) (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) : vs.length = ps.length :=
  args_length hok hfi hty

/-- **A returning behaviour of an invocation with a consistent log is a Core run of the
invocation with exactly that log**, to its values or its thrown exception, every profile. -/
theorem wasmEvFunXP_ret_evRun {tags : List TagInst} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs : List Val} {b : List Val ⊕ Nat}
    (hts : TagsOk tags s) (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .ret b s₂) ∈ wasmEvFunXP s (a, vs))
    (hc : Cons host cs) : EvRun P host (invoke s a vs) cs ⟨s₂, {}, ansCode b⟩ := by
  obtain ⟨fi, ps, rs, hfi, hty⟩ := close_ret_fn (tags := tags) hH hE h hc
  rw [invoke_eq hfi]
  exact close_ret_evRun hH hE h hc hts hS hfi hty (invokeOk_length hok hfi hty) {} _ trivial

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
