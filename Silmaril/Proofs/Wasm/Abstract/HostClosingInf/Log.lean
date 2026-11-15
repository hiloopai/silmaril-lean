module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.Quiet

/-!
# Divergence after a nonempty log (proofs)

`evRun_div`: a Core run of a typed invocation with its exact host-event log `cs`, quiescent
from there by host-free divergence, is the behaviour `(cs, div)` of `wasmEvFunD`. It is
`HostEval.evRun_divL` at `Q y q := (q, div) ∈ wasmEvFunD y`, with its two hypotheses:

* `natDiv_wasmEvFunD`: host-free native divergence of trees is local divergence with host-free
  callees (`LogDiv.div`), or reaches a call whose body diverges host-free, which has the
  behaviour `([], div)` (`callDivO_closed`);
* `funDiv_wasmEvFunD`: a body diverging within its function after a resolved log is `LDLw`
  at the end of the empty descent path; a body reaching a call after a resolved prefix `q` is a
  descent with the import calls `q` (`descends_of_reachL`: the reached call answered by an
  exception ends the body), and `div` after a descent is `div` of the caller with the
  descent's import calls in front (`closeDLog_descends`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInf

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type}

/-! ## No divergence in the closure -/

/-- The closure has no divergent behaviour: an unbounded recursion has no behaviour at all. -/
theorem close_ne_div {s : Store H} {a : Nat} {vs : List Val}
    {q : List (Call (wasmHostSig H))} (h : (q, .div) ∈ Shape.close wasmHOpen a s vs) : False := by
  obtain ⟨fi, ps, rs, s₂, bfl, fl, h1, h2, h3, h4, he⟩ :=
    wasmEvFun_hostCall (host := (fun _ _ _ _ => True : HostSemantics H)) (s := s) (a := a)
      (vs := vs) h (fun c _ => by rcases c with ⟨_, _⟩; exact trivial)
  rcases fl <;> simp [endOfFlow] at he

/-- **`div` after a descent**: the caller diverges with the descent's import calls in front. -/
theorem closeDLog_descends {x y : (wasmOShape H).self.Op} {q q' : List (Call (wasmHostSig H))}
    (hxy : Shape.Descends wasmHOpen (Shape.close wasmHOpen) x q y)
    (h : (q', .div) ∈ wasmEvFunD y.2.2 (y.1, y.2.1)) :
    (q ++ q', .div) ∈ wasmEvFunD x.2.2 (x.1, x.2.1) := by
  rcases h with (hc | ⟨-, g, qq, N, hg, hD, hN, hqs⟩) | ⟨-, z, qs, u, q'', hp, hl, hsub, hq⟩
  · exact (close_ne_div hc).elim
  · refine .inl (.inr ⟨rfl, fun n => match n with | 0 => x | n + 1 => g n,
      fun n => match n with | 0 => q | n + 1 => qq n, N + 1, rfl, fun n => ?_, fun n hn => ?_, ?_⟩)
    · rcases n with _ | n
      · show Shape.Descends wasmHOpen (Shape.close wasmHOpen) x q (g 0)
        rw [hg]; exact hxy
      · exact hD n
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      exact hN k (by omega)
    · dsimp only at hqs ⊢
      rw [hqs, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  · exact .inr ⟨rfl, z, q ++ qs, u, q'', .step hxy hp, hl, hsub, by simp only at hq; simp [hq]⟩

/-! ## Descents from logged reaches -/

/-- **A logged reach, the reached call answered by an exception**, is a logged run ending in
that exception. -/
theorem reachL_throw {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {y : (wasmOShape H).self.Op} (h : ReachL s f stk es l y) :
    ∃ (s' : Store H) (f' : Frame) (t : Nat) (ans : List Val ⊕ Nat) (s'' : Store H),
      EvalL s f stk es (l ++ [⟨.inr y, (ans, s'')⟩]) (s', f', .throw t) := by
  induction h with
  | @here s s₁ f f₁ stk stk₁ x args es a fi ps rs l hargs hfi hty =>
    exact ⟨s₁, f₁, 0, .inr 0, s₁, EvalL.callThrow (t := 0) (s₂ := s₁) hargs hfi hty⟩
  | args _ ih =>
    obtain ⟨s', f', t, ans, s'', d⟩ := ih
    exact ⟨s', f', t, ans, s'', .argsAbort d Flow.notNormal_throw⟩
  | callK hargs hfi hty _ ih =>
    obtain ⟨s', f', t, ans, s'', d⟩ := ih
    exact ⟨s', f', t, ans, s'', by simpa using EvalL.callRet hargs hfi hty d⟩
  | opK hi hargs hflat _ ih =>
    obtain ⟨s', f', t, ans, s'', d⟩ := ih
    exact ⟨s', f', t, ans, s'', by simpa using EvalL.opOk hi hargs hflat d⟩
  | block har _ ih =>
    obtain ⟨s', f', t, ans, s'', d⟩ := ih
    exact ⟨s', f', t, ans, s'', .blockEsc har d trivial⟩
  | blockK har hbody hvs _ ih =>
    obtain ⟨s', f', t, ans, s'', d⟩ := ih
    exact ⟨s', f', t, ans, s'', by simpa using EvalL.blockOk har hbody hvs d⟩
  | loop har _ ih =>
    obtain ⟨s', f', t, ans, s'', d⟩ := ih
    exact ⟨s', f', t, ans, s'', .loopEsc har d trivial⟩
  | loopK har hbody _ ih =>
    obtain ⟨s', f', t, ans, s'', d⟩ := ih
    exact ⟨s', f', t, ans, s'', by simpa using EvalL.loopOk har hbody d⟩
  | loopBack har hbody _ ih =>
    obtain ⟨s', f', t, ans, s'', d⟩ := ih
    exact ⟨s', f', t, ans, s'', by simpa using EvalL.loopBack har hbody d⟩
  | cond _ ih =>
    obtain ⟨s', f', t, ans, s'', d⟩ := ih
    exact ⟨s', f', t, ans, s'', .ifAbort d Flow.notNormal_throw⟩
  | arm hc hb har _ ih =>
    obtain ⟨s', f', t, ans, s'', d⟩ := ih
    exact ⟨s', f', t, ans, s'', by simpa using EvalL.ifEsc hc hb har d trivial⟩
  | ifK hc hb har harm hvs _ ih =>
    obtain ⟨s', f', t, ans, s'', d⟩ := ih
    exact ⟨s', f', t, ans, s'', by simpa using EvalL.ifOk hc hb har harm hvs d⟩

/-- **A logged reach in a Wasm body is a descent**, with the import calls its completed calls
resolve to. -/
theorem descends_of_reachL {y z : (wasmOShape H).self.Op} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {l : List (OCall H)} {q : List (Call (wasmHostSig H))}
    (hf : y.2.2.funcs[y.1]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hr : ReachL y.2.2 (Frame.forCall fi.module y.2.1 fn.locals) [] (liftInstrs fn.body) l z)
    (hq : Shape.SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) q) :
    Shape.Descends wasmHOpen (Shape.close wasmHOpen) y q z := by
  obtain ⟨s', f', t, ans, s'', d⟩ := reachL_throw hr
  exact ⟨((l ++ [(⟨.inr z, (ans, s'')⟩ : OCall H)]).map OCall.lift, endOfFlow (.throw t) s'),
    .inl ⟨fi, fn, ps, rs, s', f', .throw t, .throw t, _, hf, hcode, hty, d, rfl, rfl⟩,
    l.map OCall.lift, (ans, s''), [], by rw [List.map_append]; rfl, hq⟩

/-! ## The two hypotheses -/

/-- The divergence of callees after a log, as behaviours of `wasmEvFunD`. -/
def QD (y : (wasmOShape H).self.Op) (q : List (Call (wasmHostSig H))) : Prop :=
  (q, .div) ∈ wasmEvFunD y.2.2 (y.1, y.2.1)

/-- **A call whose body diverges host-free** has the behaviour `([], div)`. -/
theorem callDivO_closed {y : (wasmOShape H).self.Op} (hy : Typed y)
    (h : CallDivO closedCall y) : QD y [] := by
  rcases callDivO_path_or_chain h with ⟨z, hz, hl⟩ | ⟨g, hg, hr⟩
  · obtain ⟨fi, fn, hf, hc, hl⟩ := hl
    have hp : Shape.DescPath wasmHOpen (Shape.close wasmHOpen) y [] z := by
      rcases hz with rfl | hz
      · exact .refl _
      · exact pendO_descPath hz hy
    exact .inr ⟨rfl, z, [], [], [], hp,
      ⟨fi, fn, [], hf, hc, .div (localDivO_closed_quiet _ _ _ _ hl), rfl⟩, .nil, rfl⟩
  · have ht : ∀ n, Typed (g n) := fun n => by
      rcases n with _ | n
      · exact hg ▸ hy
      · obtain ⟨_, _, _, _, hr'⟩ := hr n
        exact reachO_typed hr'
    exact .inl (.inr ⟨rfl, g, fun _ => [], 0, hg, fun n => bodyReachO_descends (ht n) (hr n),
      fun _ _ => rfl, rfl⟩)

/-- **Host-free native divergence** is `LogDivOut QD` with the empty log. -/
theorem natDiv_wasmEvFunD {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    (h : EvalDivO closedCall s f stk es) : LogDivOut QD s f stk es [] := by
  rcases evalDivO_decomp h with hl | ⟨y, hr, hy⟩
  · exact .inl ⟨[], .div (localDivO_closed_quiet _ _ _ _ hl), .nil⟩
  · have hr' : ReachO (hostCall (closedHost : HostSemantics H)) s f stk es y := by
      rw [hostCall_closedHost]; exact hr
    obtain ⟨l, q, hrl, hres, hc⟩ := reachL_of_reachO hr'
    obtain rfl := consistent_closedHost hc
    exact .inr ⟨l, y, [], [], hrl, hres, callDivO_closed (reachO_typed hr) hy, rfl⟩

/-- **The divergence of a Wasm callee's body after a log** is the call's behaviour `div`. -/
theorem funDiv_wasmEvFunD {y : (wasmOShape H).self.Op} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {cs : List (Call (wasmHostSig H))}
    (hf : y.2.2.funcs[y.1]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (h : LogDivOut QD y.2.2 (Frame.forCall fi.module y.2.1 fn.locals) [] (liftInstrs fn.body) cs) :
    QD y cs := by
  rcases h with ⟨l, hl, hres⟩ | ⟨l, z, q, q', hr, hres, hq, rfl⟩
  · exact .inr ⟨rfl, y, [], l.map OCall.lift, cs, .refl _, ⟨fi, fn, l, hf, hcode, hl, rfl⟩, hres,
      rfl⟩
  · exact closeDLog_descends (descends_of_reachL hf hcode hty hr hres) hq

/-! ## The adequacy -/

/-- **Divergence after a log** (deterministic profile, typed checked invocations): a Core run
with its exact host-event log `cs`, then host-free divergence, is `(cs, div)` in `wasmEvFunD`. -/
theorem evRun_div {o : SingleThreaded.GrowOracle} {host : HostSemantics H} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val} {c' : Config H}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs)
    (hrun : EvRun (SingleThreaded.profile o) host (invoke s a vs) cs c')
    (hd : Diverges (SingleThreaded.profile o) (fun _ _ _ _ => False) c') :
    (cs, .div) ∈ wasmEvFunD s (a, vs) :=
  evRun_divL hT hH QD (fun _ _ _ _ h => natDiv_wasmEvFunD h)
    (fun _ _ _ _ _ _ hf hcode hty h => funDiv_wasmEvFunD hf hcode hty h) hs hS hok hrun hd

end Silmaril.Proofs.Wasm.Abstract.HostClosingInf
