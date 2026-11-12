module

public import Silmaril.Proofs.Wasm.Interp.Control
public import Silmaril.Wasm.Binaryen.AdequacyReduce

@[expose] public section

/-!
# Forward simulation of native invocations (proofs)

`fwd_invoke`, `fwdSim_of_storeChk`: a terminating native invocation (`Binaryen.invokeRun`) of a
function of a store whose functions all pass the arity check (`StoreChk`), on arguments of the
function's parameter types (`InvokeOk`), is matched by a Core 3.0 run of `$invoke` to the same
result, at every profile and host. This is silmaril-lean's `Binaryen.FwdSim` obligation
(`Silmaril/Wasm/Binaryen/AdequacyReduce.lean`) on arity-checked stores. New proofs. Summary in
`Silmaril.Wasm.Interp.Thms`.
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H} {s s' : Store H} {a : Nat}
  {vs : List Val}

/-- What a terminating native invocation did. -/
theorem invokeRun_inv {fuel : Nat} {fl : Binaryen.Flow}
    (h : Binaryen.invokeRun fuel s a vs = some (s', fl)) :
    ∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (F' : Frame)
      (flb : Binaryen.Flow), s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      Binaryen.run fuel s (Frame.forCall fi.module vs fn.locals) [] (Binaryen.liftInstrs fn.body) =
        some (s', F', flb) ∧
      ((∃ ws, flb.retVals = some ws ∧ fl = .normal (ws.take rs.length).reverse) ∨
        (flb = .trap ∧ fl = .trap) ∨ (∃ t, flb = .throw t ∧ fl = .throw t)) := by
  unfold Binaryen.invokeRun at h
  split at h
  · rename_i fi hfi
    split at h
    · rename_i fn ps rs hcode hty
      split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
      all_goals first
        | (obtain ⟨rfl, rfl⟩ := h
           exact ⟨fi, fn, ps, rs, _, _, hfi, hcode, hty, ‹_›, .inl ⟨_, rfl, rfl⟩⟩)
        | (obtain ⟨rfl, rfl⟩ := h
           exact ⟨fi, fn, ps, rs, _, _, hfi, hcode, hty, ‹_›, .inr (.inl ⟨rfl, rfl⟩)⟩)
        | (obtain ⟨rfl, rfl⟩ := h
           exact ⟨fi, fn, ps, rs, _, _, hfi, hcode, hty, ‹_›, .inr (.inr ⟨_, rfl, rfl⟩)⟩)
    · cases h
  · cases h

/-- The arguments of a valid invocation have the parameter arity of the function. -/
theorem args_length {fi : FuncInst H} {ps rs : List Validation.CValType} (hok : InvokeOk s a vs)
    (hfi : s.funcs[a]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    vs.length = ps.length := by
  obtain ⟨fi', ps', rs', hfi', he, hvs⟩ := hok
  rw [hfi] at hfi'
  cases hfi'
  have he' : fi.type.expand? = some (.func ps' rs') := Validation.Expand.iff.mp he
  unfold Validation.DefType.funcType? at hty
  rw [he'] at hty
  simp only [Option.some.injEq, Prod.mk.injEq] at hty
  rw [← hty.1]
  exact hvs.length_eq

/-- `$invoke` enters the callee body. -/
theorem steps_invoke_enter {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hlen : vs.length = ps.length) :
    Steps P host (invoke s a vs) ⟨s, {}, [.frame rs.length (Frame.forCall fi.module vs fn.locals)
      [.label rs.length [] (expression fn.body)]]⟩ := by
  obtain ⟨ps', rs', he, hpl, hrl⟩ := expand_of_funcType hty
  have hinv : invoke s a vs = ⟨s, {}, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩ := by
    simp [invoke, hfi]
  rw [hinv, ← hrl]
  exact .single (Step.callRefFunc trivial hfi he (hlen.trans hpl.symm) hcode)

/-- The Core run of an invocation whose native body ran, up to the body's final form. -/
theorem invoke_body {fuel : Nat} {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType}
    {F' : Frame} {flb : Binaryen.Flow} (hS : StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hrun : Binaryen.run fuel s (Frame.forCall fi.module vs fn.locals) []
      (Binaryen.liftInstrs fn.body) = some (s', F', flb)) :
    ∃ c' o ob, Steps P host (invoke s a vs)
        ⟨s', {}, [.frame rs.length F' [.label rs.length [] c']]⟩ ∧ o.Ends c' ∧
      FlowMatch flb o ∧ FlowOk [rs.length] rs.length ob flb ∧ (ob = none ∨ ob = some rs.length) := by
  have hlen : vs.length = ps.length := args_length hok hfi hty
  have hev := Binaryen.eval_of_run hrun
  have hlocals : (Frame.forCall fi.module vs fn.locals).locals.length =
      ps.length + fn.locals.length := forCall_length _ _ hlen
  obtain ⟨ob, hb, hob⟩ := endsAt_eq (hS a fi fn ps rs hfi hcode hty)
  have hbc : chk s.funcs (Frame.forCall fi.module vs fn.locals).module
      (Frame.forCall fi.module vs fn.locals).locals.length rs.length [rs.length]
      (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
    rw [hlocals]
    exact hb
  obtain ⟨hok', -⟩ := flowOk_of_eval hev hS hbc
  have hwp := wp_of_eval (P := P) (host := host) hev hS hbc
  rw [Binaryen.lowerList_liftInstrs] at hwp
  obtain ⟨c', o, hbody, he, hm⟩ := run_of_wp hwp
  have inner := Steps.frame (P := P) (host := host) (f := ({} : Frame)) rs.length
    (Steps.label rs.length [] (by simpa [vals] using hbody))
  exact ⟨c', o, ob, (steps_invoke_enter hfi hcode hty hlen).trans inner, he, hm, hok', hob⟩

/-- A trapped body leaves its label and frame as a trap. -/
theorem frame_trap {c' : List Admin} {o : Outcome} {n : Nat} {F' : Frame} (he : o.Ends c')
    (hm : FlowMatch .trap o) :
    Steps P host ⟨s', {}, [.frame n F' [.label n [] c']]⟩ ⟨s', {}, [.trap]⟩ := by
  have hc : c' = [.trap] := by
    rcases o with _ | _ | _ | _ | _ | _ <;> simp only [FlowMatch] at hm
    exact he
  rw [hc]
  exact (Relation.ReflTransGen.single (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame

/-- **Forward simulation of a native invocation**, every profile and host. -/
theorem fwd_invoke {fuel : Nat} {fl : Binaryen.Flow} (hS : StoreChk s.funcs)
    (hok : InvokeOk s a vs) (h : Binaryen.invokeRun fuel s a vs = some (s', fl)) :
    ∃ (c : Config H) (r : Result), Steps P host (invoke s a vs) c ∧ c.code = r.toAdmin ∧
      Binaryen.flowBeh fl = some r.toBehaviour := by
  obtain ⟨fi, fn, ps, rs, F', flb, hfi, hcode, hty, hrun, hfl⟩ := invokeRun_inv h
  obtain ⟨c', o, ob, hst, he, hm, hok', hob⟩ :=
    invoke_body (P := P) (host := host) hS hok hfi hcode hty hrun
  rcases hfl with ⟨ws, hvs, rfl⟩ | ⟨rfl, rfl⟩ | ⟨t, rfl, rfl⟩
  · have hnorm : ∀ w, flb = .normal w → w.length = rs.length := by
      rintro w rfl
      exact length_of_ends hok' hob
    obtain ⟨s'', res, hret, hK⟩ := frame_ends (P := P) (host := host) (f := ({} : Frame)) he
      (funcPost_of_match (s₂ := s') (F := F') hm hvs (retVals_length hok' hob hvs) hnorm)
    obtain ⟨rfl, rfl⟩ := hK
    exact ⟨_, .values _, hst.trans hret, rfl, rfl⟩
  · exact ⟨_, .trap, hst.trans (frame_trap he hm), rfl, rfl⟩
  · rcases o <;> simp only [FlowMatch] at hm

/-- **`FwdSim` on arity-checked stores**, every profile. -/
theorem fwdSim_of_storeChk (hS : StoreChk s.funcs) (hok : InvokeOk s a vs) :
    Binaryen.FwdSim P s a vs := by
  intro fuel s' fl b h hb
  obtain ⟨c, r, hst, hc, hbr⟩ := fwd_invoke (P := P) (host := Binaryen.closedHost) hS hok h
  rw [hb, Option.some.injEq] at hbr
  exact ⟨c, r, hst, hc, hbr.symm⟩

end Silmaril.Wasm.Interp
