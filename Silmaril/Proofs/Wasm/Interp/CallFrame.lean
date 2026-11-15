module

public import Silmaril.Proofs.Wasm.Interp.Invoke

/-!
# A native callee body is a Core 3.0 `call_ref` run in any caller frame (proofs)

`steps_callRef_of_eval`: if the body of the Wasm function at `a` evaluates
natively on the parameter-order arguments `vs`, then the Core code
`vals vs ++ [ref.func a, call_ref]` runs, in **any** caller frame `f`, to:

* the top `rs.length` returned values, in result order, when the body's flow
  hands back values (`retVals`);
* a trap, when it traps.

It never throws. The only assumptions are the arity check of the store
(`StoreChk`) and a typed invocation (`InvokeOk`), at every profile and host.
The proof is that of `invoke_body`/`fwd_invoke`, with the caller frame left
free.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H} {s s' : Store H} {a : Nat}
  {vs : List Val}

theorem steps_callRefAnn_of_good {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType}
    {F' : Frame} {flb : Binaryen.Flow} (hS : StoreChk s.funcs) (hlen : vs.length = ps.length)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (aga : ArityGood s (Frame.forCall fi.module vs fn.locals) [] (Binaryen.liftInstrs fn.body)
      (s', F', flb))
    (cga : CoreGood P host s (Frame.forCall fi.module vs fn.locals) [] (Binaryen.liftInstrs fn.body)
      (s', F', flb)) (f : Frame) {c : Admin} (hc : c.IsCallRef) :
    (∀ ws, flb.retVals = some ws → Steps P host
        ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
        ⟨s', f, vals (ws.take rs.length).reverse⟩) ∧
      (flb = .trap → Steps P host ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
        ⟨s', f, [.trap]⟩) ∧
      ∀ t, flb ≠ .throw t := by
  have hlocals : (Frame.forCall fi.module vs fn.locals).locals.length =
      ps.length + fn.locals.length := forCall_length _ _ hlen
  obtain ⟨ob, hb, hob⟩ := endsAt_eq (hS a fi fn ps rs hfi hcode hty)
  have hbc : chk s.funcs (Frame.forCall fi.module vs fn.locals).module
      (Frame.forCall fi.module vs fn.locals).locals.length rs.length [rs.length]
      (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
    rw [hlocals]
    exact hb
  obtain ⟨hok', -⟩ := aga hS hbc
  have hwp := cga hS hbc
  rw [Binaryen.lowerList_liftInstrs] at hwp
  obtain ⟨c', o, hbody, he, hm⟩ := run_of_wp hwp
  have enter : Steps P host ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs fn.locals)
        [.label rs.length [] (expression fn.body)]]⟩ := by
    obtain ⟨ps', rs', he', hpl, hrl⟩ := expand_of_funcType hty
    rw [← hrl]
    exact .single (Step.callRefFunc hc hfi he' (hlen.trans hpl.symm) hcode)
  have inner := Steps.frame (P := P) (host := host) (f := f) rs.length
    (Steps.label rs.length [] (by simpa [vals] using hbody))
  have hst := enter.trans inner
  refine ⟨fun ws hvs => ?_, fun htr => ?_, fun t ht => ?_⟩
  · have hnorm : ∀ w, flb = .normal w → w.length = rs.length := by
      rintro w rfl
      exact length_of_ends hok' hob
    obtain ⟨s'', res, hret, hK⟩ := frame_ends (P := P) (host := host) (f := f) he
      (funcPost_of_match (s₂ := s') (F := F') hm hvs (retVals_length hok' hob hvs) hnorm)
    obtain ⟨rfl, rfl⟩ := hK
    exact hst.trans hret
  · subst htr
    have hc : c' = [.trap] := by
      rcases o with _ | _ | _ | _ | _ | _ <;> simp only [FlowMatch] at hm
      exact he
    rw [hc] at hst
    exact hst.trans ((Relation.ReflTransGen.single (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame)
  · subst ht
    exact hok'

/-- `steps_callRefAnn_of_good` for the `call_ref` of the function's own type. -/
theorem steps_callRef_of_good {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType}
    {F' : Frame} {flb : Binaryen.Flow} (hS : StoreChk s.funcs) (hlen : vs.length = ps.length)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (aga : ArityGood s (Frame.forCall fi.module vs fn.locals) [] (Binaryen.liftInstrs fn.body)
      (s', F', flb))
    (cga : CoreGood P host s (Frame.forCall fi.module vs fn.locals) [] (Binaryen.liftInstrs fn.body)
      (s', F', flb)) (f : Frame) :
    (∀ ws, flb.retVals = some ws → Steps P host
        ⟨s, f, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩
        ⟨s', f, vals (ws.take rs.length).reverse⟩) ∧
      (flb = .trap → Steps P host ⟨s, f, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩
        ⟨s', f, [.trap]⟩) ∧
      ∀ t, flb ≠ .throw t :=
  steps_callRefAnn_of_good hS hlen hfi hcode hty aga cga f trivial

theorem steps_callRefAnn_of_eval {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType}
    {F' : Frame} {flb : Binaryen.Flow} (hS : StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hev : Binaryen.Eval s (Frame.forCall fi.module vs fn.locals) [] (Binaryen.liftInstrs fn.body)
      (s', F', flb)) (f : Frame) {c : Admin} (hc : c.IsCallRef) :
    (∀ ws, flb.retVals = some ws → Steps P host
        ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
        ⟨s', f, vals (ws.take rs.length).reverse⟩) ∧
      (flb = .trap → Steps P host ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
        ⟨s', f, [.trap]⟩) ∧
      ∀ t, flb ≠ .throw t :=
  steps_callRefAnn_of_good hS (args_length hok hfi hty) hfi hcode hty (flowOk_of_eval hev)
    (wp_of_eval hev) f hc

theorem steps_callRef_of_eval {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType}
    {F' : Frame} {flb : Binaryen.Flow} (hS : StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hev : Binaryen.Eval s (Frame.forCall fi.module vs fn.locals) [] (Binaryen.liftInstrs fn.body)
      (s', F', flb)) (f : Frame) :
    (∀ ws, flb.retVals = some ws → Steps P host
        ⟨s, f, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩
        ⟨s', f, vals (ws.take rs.length).reverse⟩) ∧
      (flb = .trap → Steps P host ⟨s, f, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩
        ⟨s', f, [.trap]⟩) ∧
      ∀ t, flb ≠ .throw t :=
  steps_callRef_of_good hS (args_length hok hfi hty) hfi hcode hty (flowOk_of_eval hev)
    (wp_of_eval hev) f

