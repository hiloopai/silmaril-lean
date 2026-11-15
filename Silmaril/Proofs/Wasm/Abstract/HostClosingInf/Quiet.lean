module

public import Silmaril.Wasm.Abstract.HostClosingInf.Defs
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Wasm.Abstract.HostClosing.Thms
public import Silmaril.Wasm.Abstract.HostEval.Thms
public import Silmaril.Wasm.Abstract.DivO.Thms
public import Silmaril.Wasm.Abstract.Decomp.Thms
public import Silmaril.Wasm.Abstract.Closing.Thms
public import Silmaril.Wasm.Abstract.Recursion.Thms

/-!
# Host-free callees and logged local divergence (proofs)

* `quietCall` agrees with the closure `closedCall` on the answers it gives
  (`quietCall_closedCall`), and gives every answer of it that a run can consume
  (`closedCall_quietCall`); so `LocalDivO closedCall ≤ LocalDivO quietCall`, and local
  divergence (`wasmLocalDiv`) is logged local divergence with an empty log.
* Host-free descents (`ReachO closedCall`, `PendO closedCall`) are descents of `wasmHOpen`
  with no import calls.
* `invoke_div_closed`: a host-free divergent typed invocation diverges in `wasmEvFunD` with an
  empty log; `evRun_nil_div`: so does one quiescent after a run with no host event.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInf

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type}

/-! ## Answers -/

/-- The host with no outcome allows only the empty log. -/
theorem consistent_closedHost {cs : List (Call (wasmHostSig H))}
    (h : (coreHostRel (closedHost : HostSemantics H)).Consistent cs) : cs = [] := by
  cases cs with
  | nil => rfl
  | cons e _ => exact False.elim (h e List.mem_cons_self)

/-- A callee flow a run can consume: values, a trap or an exception. -/
def Consumed (fl : Flow) : Prop := (∃ vs, fl.retVals = some vs) ∨ fl = .trap ∨ ∃ t, fl = .throw t

theorem exitFlow_of_consumed {fl : Flow} (h : Consumed fl) (n : Nat) :
    ∃ fl', exitFlow n fl = some fl' := by
  rcases h with ⟨vs, hvs⟩ | rfl | ⟨t, rfl⟩
  · match fl, hvs with
    | .normal _, _ => exact ⟨_, rfl⟩
    | .ret _, _ => exact ⟨_, rfl⟩
    | .brk 0 _, _ => exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- A closed answer is a behaviour of the closure with an empty import log. -/
theorem hclose_of_closedCall {s s₂ : Store H} {a : Nat} {us : List Val} {bfl fl : Flow}
    {fi : FuncInst H} {ps rs : List Validation.CValType} (h : closedCall s a us (s₂, bfl))
    (hfi : s.funcs[a]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hx : exitFlow rs.length bfl = some fl) :
    ([], endOfFlow fl s₂) ∈ Shape.close wasmHOpen a s us := by
  rw [← hostCall_closedHost] at h
  obtain ⟨cs, hc, hm⟩ := hostCall_wasmEv hfi hty h hx
  obtain rfl := consistent_closedHost hc
  exact hm

/-- **Every consumable closed answer is a host-free answer.** -/
theorem closedCall_quietCall {s : Store H} {a : Nat} {us : List Val} {out : Store H × Flow}
    (h : closedCall s a us out) (hc : Consumed out.2) : quietCall s a us out := by
  have hb : bodyCall closedCall s a us out := by rw [← closedCall_fixpoint]; exact h
  obtain ⟨fi, -, ps, rs, -, hfi, -, hty, -⟩ := hb
  obtain ⟨fl, hx⟩ := exitFlow_of_consumed hc rs.length
  exact ⟨fi, ps, rs, fl, hfi, hty, hx, hclose_of_closedCall h hfi hty hx⟩

/-- **Every host-free answer is a closed answer**, up to the end it hands back. -/
theorem quietCall_closedCall {s s₂ : Store H} {a : Nat} {us : List Val} {bfl : Flow}
    (h : quietCall s a us (s₂, bfl)) :
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (fl fl' bfl' : Flow) (s₂' : Store H),
      s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      exitFlow rs.length bfl = some fl ∧ closedCall s a us (s₂', bfl') ∧
      exitFlow rs.length bfl' = some fl' ∧ endOfFlow fl' s₂' = endOfFlow fl s₂ := by
  obtain ⟨fi, ps, rs, fl, hfi, hty, hx, hm⟩ := h
  obtain ⟨fi', ps', rs', s₂', bfl', fl', hfi', hty', hcall, hx', he⟩ :=
    wasmEvFun_hostCall (host := (closedHost : HostSemantics H)) (s := s) (a := a) (vs := us)
      hm (fun _ h => nomatch h)
  obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
  rw [hostCall_closedHost] at hcall
  exact ⟨fi, ps, rs, fl, fl', bfl', s₂', hfi, hty, hx, hcall, hx', he.symm⟩

/-! ## Changing the oracle on consumed answers -/

theorem evalO_change {C C' : CallRel H}
    (hC : ∀ s a us out, C s a us out → Consumed out.2 → C' s a us out) {s : Store H} {f : Frame}
    {stk : List Val} {es : List BExpr} {r : Store H × Frame × Flow} (h : EvalO C s f stk es r) :
    EvalO C' s f stk es r := by
  induction h with
  | nil => exact .nil
  | argsAbort _ hfl ih => exact .argsAbort ih hfl
  | callOk _ hfi hty hcall hvs _ ih₁ ih₂ =>
    exact .callOk ih₁ hfi hty (hC _ _ _ _ hcall (.inl ⟨_, hvs⟩)) hvs ih₂
  | callTrap _ hfi hty hcall ih => exact .callTrap ih hfi hty (hC _ _ _ _ hcall (.inr (.inl rfl)))
  | callThrow _ hfi hty hcall ih =>
    exact .callThrow ih hfi hty (hC _ _ _ _ hcall (.inr (.inr ⟨_, rfl⟩)))
  | opOk hi _ hflat _ ih₁ ih₂ => exact .opOk hi ih₁ hflat ih₂
  | opStop hi _ hflat hfl ih => exact .opStop hi ih hflat hfl
  | blockOk har _ hvs _ ih₁ ih₂ => exact .blockOk har ih₁ hvs ih₂
  | blockBrk har _ ih => exact .blockBrk har ih
  | blockEsc har _ hfl ih => exact .blockEsc har ih hfl
  | loopOk har _ _ ih₁ ih₂ => exact .loopOk har ih₁ ih₂
  | loopBack har _ _ ih₁ ih₂ => exact .loopBack har ih₁ ih₂
  | loopBrk har _ ih => exact .loopBrk har ih
  | loopEsc har _ hfl ih => exact .loopEsc har ih hfl
  | ifOk _ hb har _ hvs _ ih₁ ih₂ ih₃ => exact .ifOk ih₁ hb har ih₂ hvs ih₃
  | ifBrk _ hb har _ ih₁ ih₂ => exact .ifBrk ih₁ hb har ih₂
  | ifEsc _ hb har _ hfl ih₁ ih₂ => exact .ifEsc ih₁ hb har ih₂ hfl
  | ifAbort _ hfl ih => exact .ifAbort ih hfl

theorem divStepO_change {C C' : CallRel H}
    (hC : ∀ s a us out, C s a us out → Consumed out.2 → C' s a us out)
    {X Y : Interp.Problem H} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    (h : DivStepO C X Y s f stk es) : DivStepO C' X Y s f stk es := by
  cases h with
  | args h => exact .args h
  | callee hargs hfi hcode hty h => exact .callee (evalO_change hC hargs) hfi hcode hty h
  | callRet hargs hfi hty hcall hvs h =>
    exact .callRet (evalO_change hC hargs) hfi hty (hC _ _ _ _ hcall (.inl ⟨_, hvs⟩)) hvs h
  | opK hi hargs hflat h => exact .opK hi (evalO_change hC hargs) hflat h
  | block har h => exact .block har h
  | blockK har hbody hvs h => exact .blockK har (evalO_change hC hbody) hvs h
  | loop har h => exact .loop har h
  | loopK har hbody h => exact .loopK har (evalO_change hC hbody) h
  | loopBack har hbody h => exact .loopBack har (evalO_change hC hbody) h
  | cond h => exact .cond h
  | arm hc hb har h => exact .arm (evalO_change hC hc) hb har h
  | ifK hc hb har harm hvs h =>
    exact .ifK (evalO_change hC hc) hb har (evalO_change hC harm) hvs h

theorem localDivO_change {C C' : CallRel H}
    (hC : ∀ s a us out, C s a us out → Consumed out.2 → C' s a us out) :
    LocalDivO C ≤ LocalDivO C' :=
  localDivO_of_coind fun _ _ _ _ h => divStepO_change hC (localDivO_iff_step.mp h)

/-- **Host-free local divergence is local divergence with host-free callees.** -/
theorem localDivO_closed_quiet : LocalDivO (closedCall : CallRel H) ≤ LocalDivO quietCall :=
  localDivO_change fun _ _ _ _ h hc => closedCall_quietCall h hc

/-- **Local divergence is logged local divergence with an empty log.** -/
theorem ldlw_of_wasmLocalDiv {z : (wasmOShape H).self.Op} (h : wasmLocalDiv z) : LDLw z [] := by
  obtain ⟨fi, fn, hf, hc, hl⟩ := h
  rw [← localDivO_closed] at hl
  exact ⟨fi, fn, [], hf, hc, .div (localDivO_closed_quiet _ _ _ _ hl), rfl⟩

/-! ## Host-free descents -/

/-- The call has a typed function. -/
def Typed (x : (wasmOShape H).self.Op) : Prop :=
  ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), x.2.2.funcs[x.1]? = some fi ∧
    Validation.DefType.funcType? fi.type = some (ps, rs)

theorem reachO_typed {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {y : (wasmOShape H).self.Op} (h : ReachO C s f stk es y) : Typed y := by
  induction h with
  | here _ hfi hty => exact ⟨_, _, _, funcs_of_func? hfi, hty⟩
  | args _ ih => exact ih
  | callK _ _ _ _ _ _ ih => exact ih
  | opK _ _ _ _ ih => exact ih
  | block _ _ ih => exact ih
  | blockK _ _ _ _ ih => exact ih
  | loop _ _ ih => exact ih
  | loopK _ _ _ ih => exact ih
  | loopBack _ _ _ ih => exact ih
  | cond _ ih => exact ih
  | arm _ _ _ _ ih => exact ih
  | ifK _ _ _ _ _ _ ih => exact ih

theorem typed_of_invokeOk {s : Store H} {a : Nat} {vs : List Val} (hok : InvokeOk s a vs) :
    Typed (⟨a, (vs, s)⟩ : (wasmOShape H).self.Op) := by
  obtain ⟨fi, ps, rs, hfi, he, -⟩ := hok
  refine ⟨fi, ps.toList, rs.toList, hfi, ?_⟩
  unfold Validation.DefType.funcType?
  rw [Validation.Expand.iff.mp he]

/-- Host-free reaching is native reaching. -/
theorem reach_of_reachO {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {y : (wasmOShape H).self.Op} (h : ReachO closedCall s f stk es y) : Reach s f stk es y := by
  induction h with
  | here hargs hfi hty => exact .here (evalO_closed_iff.mp hargs) hfi hty
  | args _ ih => exact .args ih
  | callK hargs hfi hty hcall hvs _ ih =>
    rw [closedCall_eq] at hcall
    obtain ⟨fi', fn, ps', rs', f₂, hfi', hcode, hty', hbody⟩ := hcall
    obtain rfl : _ = fi' := Option.some.inj ((funcs_of_func? hfi).symm.trans hfi')
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
    exact .callK (evalO_closed_iff.mp hargs) hfi hcode hty hbody hvs ih
  | opK hi hargs hflat _ ih => exact .opK hi (evalO_closed_iff.mp hargs) hflat ih
  | block har _ ih => exact .block har ih
  | blockK har hbody hvs _ ih => exact .blockK har (evalO_closed_iff.mp hbody) hvs ih
  | loop har _ ih => exact .loop har ih
  | loopK har hbody _ ih => exact .loopK har (evalO_closed_iff.mp hbody) ih
  | loopBack har hbody _ ih => exact .loopBack har (evalO_closed_iff.mp hbody) ih
  | cond _ ih => exact .cond ih
  | arm hc hb har _ ih => exact .arm (evalO_closed_iff.mp hc) hb har ih
  | ifK hc hb har harm hvs _ ih =>
    exact .ifK (evalO_closed_iff.mp hc) hb har (evalO_closed_iff.mp harm) hvs ih

/-- A behaviour of the import-free closure is one of the closure with host imports, with an
empty log. -/
theorem hclose_of_close {s : Store H} {a : Nat} {vs : List Val}
    {y : CallBeh Sig.empty (Store H) (List Val ⊕ Nat)} (h : y ∈ Shape.close wasmOpen a s vs) :
    ([], y.2) ∈ Shape.close wasmHOpen a s vs := by
  rw [close_wasmOpen] at h
  obtain ⟨s', fl, ⟨fi, fn, ps, rs, f₂, bfl, hfi, hcode, hty, hb, hx⟩, rfl⟩ := h
  have hc : closedCall s a vs (s', bfl) := by
    rw [closedCall_fixpoint]
    exact ⟨fi, fn, ps, rs, f₂, hfi, hcode, hty, hb⟩
  exact hclose_of_closedCall hc hfi hty hx

theorem substPre_lift {u : List (OCall H)} {q : List (Call Sig.empty)}
    (h : Shape.SubstPre (Shape.close wasmOpen) u q) :
    Shape.SubstPre (Shape.close wasmHOpen) (u.map OCall.lift) [] := by
  induction h with
  | nil => exact .nil
  | @ext m _ _ _ _ _ => exact nomatch m
  | int hc _ ih => exact .int (hclose_of_close hc) ih

theorem descends_lift {x y : (wasmOShape H).self.Op}
    (h : Shape.Descends wasmOpen (Shape.close wasmOpen) x [] y) :
    Shape.Descends wasmHOpen (Shape.close wasmHOpen) x [] y := by
  obtain ⟨z, ⟨fi, fn, ps, rs, s', f₂, bfl, fl, hfi, hcode, hty, hb, hx, he⟩, u, ans, rest, hz, hq⟩ := h
  refine ⟨(z.1.map OCall.lift, z.2),
    .inl ⟨fi, fn, ps, rs, s', f₂, bfl, fl, z.1, hfi, hcode, hty, hb, hx, Prod.ext rfl he⟩,
    u.map OCall.lift, ans, rest.map OCall.lift, ?_, substPre_lift hq⟩
  rw [hz, List.map_append, List.map_cons]
  rfl

/-- **A host-free descent is a descent of `wasmHOpen` with no import call.** -/
theorem bodyReachO_descends {x y : (wasmOShape H).self.Op} (hx : Typed x)
    (h : BodyReachO closedCall x y) : Shape.Descends wasmHOpen (Shape.close wasmHOpen) x [] y := by
  obtain ⟨fi, fn, hf, hc, hr⟩ := h
  exact descends_lift ((bodyReach_iff_descends hx).mp ⟨fi, fn, hf, hc, reach_of_reachO hr⟩)

theorem pendO_descPath {x z : (wasmOShape H).self.Op} (h : PendO closedCall x z) :
    Typed x → Shape.DescPath wasmHOpen (Shape.close wasmHOpen) x [] z := by
  induction h with
  | body hf hcode hr =>
    exact fun hx => Shape.DescPath.step (q := []) (bodyReachO_descends hx ⟨_, _, hf, hcode, hr⟩)
      (.refl _)
  | desc hf hcode hr _ ih =>
    exact fun hx => Shape.DescPath.step (q := []) (bodyReachO_descends hx ⟨_, _, hf, hcode, hr⟩)
      (ih (reachO_typed hr))

/-! ## Host-free divergence of an invocation -/

theorem hostTyped_closedHost : HostTyped (closedHost : HostSemantics H) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ h => False.elim h

theorem nativeHostSlice_closedHost : Interp.NativeHostSlice (closedHost : HostSemantics H) :=
  ⟨fun _ _ _ _ _ h => False.elim h, fun _ _ _ _ _ _ _ _ _ _ _ _ h => False.elim h,
    fun _ _ _ _ _ h => h⟩

/-- **A host-free divergent typed invocation diverges in `wasmEvFunD` with an empty log.** -/
theorem invoke_div_closed {o : SingleThreaded.GrowOracle} {s : Store H} {a : Nat}
    {vs : List Val} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hd : Diverges (SingleThreaded.profile o) closedHost (invoke s a vs)) :
    ([], .div) ∈ wasmEvFunD s (a, vs) := by
  rcases invoke_div_decomp hostTyped_closedHost nativeHostSlice_closedHost hs hS hok hd with
    ⟨_, _, _, -, -, -, hdiv⟩ | ⟨z, hz, hl⟩ | ⟨g, hg, hr⟩
  · exact False.elim hdiv
  · rw [hostCall_closedHost] at hz hl
    obtain ⟨fi, fn, hf, hc, hl⟩ := hl
    have hp : Shape.DescPath wasmHOpen (Shape.close wasmHOpen) ⟨a, (vs, s)⟩ [] z := by
      rcases hz with rfl | hz
      · exact .refl _
      · exact pendO_descPath hz (typed_of_invokeOk hok)
    exact .inr ⟨rfl, z, [], [], [], hp,
      ⟨fi, fn, [], hf, hc, .div (localDivO_closed_quiet _ _ _ _ hl), rfl⟩, .nil, rfl⟩
  · rw [hostCall_closedHost] at hr
    have ht : ∀ n, Typed (g n) := fun n => by
      rcases n with _ | n
      · exact hg ▸ typed_of_invokeOk hok
      · obtain ⟨_, _, _, _, hr'⟩ := hr n
        exact reachO_typed hr'
    exact .inl (.inr ⟨rfl, g, fun _ => [], 0, hg, fun n => bodyReachO_descends (ht n) (hr n),
      fun _ _ => rfl, rfl⟩)

theorem evRun_nil_steps {P : Numerics.Profile} {host : HostSemantics H} {c c' : Config H}
    {cs : List (Call (wasmHostSig H))} (h : EvRun P host c cs c') :
    cs = [] → Steps P closedHost c c' := by
  induction h with
  | refl => exact fun _ => .refl
  | silent hs _ ih =>
    intro hcs
    rcases hs with hs | ⟨rfl, -⟩
    · exact .head hs (ih hcs)
    · exact ih hcs
  | event _ _ _ => exact fun hcs => nomatch hcs

/-- **Quiescent host-free divergence after a run with no host event**: a divergent invocation
in `wasmEvFunD` with an empty log. -/
theorem evRun_nil_div {o : SingleThreaded.GrowOracle} {host : HostSemantics H} {s : Store H}
    {a : Nat} {vs : List Val} {c' : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs)
    (hrun : EvRun (SingleThreaded.profile o) host (invoke s a vs) [] c')
    (hd : Diverges (SingleThreaded.profile o) (fun _ _ _ _ => False) c') :
    ([], .div) ∈ wasmEvFunD s (a, vs) :=
  invoke_div_closed hs hS hok (Silmaril.InfiniteTrace.of_steps (evRun_nil_steps hrun rfl) hd)

end Silmaril.Proofs.Wasm.Abstract.HostClosingInf
