module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.FwdInf

/-!
# Trapping native behaviours are Core runs to a trap with exactly their host events (proofs)

The trapping half of the logged forward simulation, every profile. A trapping closed behaviour
`(q, trap)` of `Shape.close wasmHOpen` with a log the host allows is a Core run of the call, in
any caller frame, whose host events are **exactly** `q`, ending at `[trap]` (in some store:
a trap carries none).

* `TrapRun`, `trapRun_pre`, `trapRun_ctx`, `trapRun_label`: a logged Core run to a trap, and
  the host-free bubbling of a trap through values, code and labels (`steps_trap`,
  `Step.trapLabel`);
* `callRef_trap_of_body`: a callee body trapping in its frame traps the call, out of its frame
  (`Step.trapFrame`);
* `reachL_trap`: a logged reach (`ReachL`) whose resolved prefix makes the host calls `q`, the
  reached call trapping with the host calls `c₁`, is a Core run to a trap with the events
  `q ++ c₁`. By induction, as `reachL_fwd`: the completed parts are `prefix_glue`,
  `loopBack_glue`, `arm_glue`; the trap bubbles out of every enclosing context;
* `subst_trap_inv`: a trapping resolution either resolves every internal call (the open
  behaviour itself traps) or resolves a prefix and then meets a trapping callee
  (`Shape.Subst.intTrap`);
* `close_le_goodT`: by least-fixpoint induction, every trapping closed behaviour with a
  consistent log is such a Core run: a Wasm body trapping itself is `evalL_fwd` in its frame; a
  body reaching a trapping callee is a descent (`descends_unwrap`), then `reachL_trap`; a host
  callee answering a trap is its one event (`hEvStep_host_call`);
* `wasmEvFun_trap_evRun`: **a trapping behaviour of an invocation with a consistent log is a
  Core run of the invocation to a trap with exactly that log**.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInf

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Interp
open Shape (SubstPre)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Runs to a trap -/

/-- **A logged Core run to a trap**, with the host events `q`, in some store and frame. -/
def TrapRun (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (c : Config H)
    (q : List (Call (wasmHostSig H))) : Prop :=
  ∃ (s' : Store H) (f' : Frame), EvRun P host c q ⟨s', f', [.trap]⟩

theorem trapRun_pre {c c₁ : Config H} {q₁ q₂ : List (Call (wasmHostSig H))}
    (h : EvRun P host c q₁ c₁) (h₂ : TrapRun P host c₁ q₂) : TrapRun P host c (q₁ ++ q₂) := by
  obtain ⟨s', f', h'⟩ := h₂
  exact ⟨s', f', evRun_trans h h'⟩

/-- A trap bubbles out of values and code. -/
theorem trapRun_ctx (ws : List Val) (rest : List Admin) {s : Store H} {f : Frame}
    {code : List Admin} {q : List (Call (wasmHostSig H))} (h : TrapRun P host ⟨s, f, code⟩ q) :
    TrapRun P host ⟨s, f, vals ws ++ code ++ rest⟩ q := by
  obtain ⟨s', f', h⟩ := h
  have h₂ : Steps P NH ⟨s', f', vals ws ++ [.trap] ++ rest⟩ ⟨s', f', [.trap]⟩ := by
    simpa using Silmaril.Wasm.Logic.Core.steps_trap (P := P) (host := NH) s' f' ws rest
  exact ⟨s', f', by simpa using evRun_trans (evRun_ctx ws rest h) (evRun_of_free h₂)⟩

/-- A trap bubbles out of a label. -/
theorem trapRun_label (n : Nat) (cont : List Instr) {s : Store H} {f : Frame}
    {code : List Admin} {q : List (Call (wasmHostSig H))} (h : TrapRun P host ⟨s, f, code⟩ q) :
    TrapRun P host ⟨s, f, [.label n cont code]⟩ q := by
  obtain ⟨s', f', h⟩ := h
  have h₂ : Steps P NH ⟨s', f', [.label n cont [.trap]]⟩ ⟨s', f', [.trap]⟩ :=
    .single Step.trapLabel
  exact ⟨s', f', by simpa using evRun_trans (evRun_label n cont h) (evRun_of_free h₂)⟩

/-- A logged run matching a trap is a run to `[trap]`. -/
theorem trapRun_of_runL {s s' : Store H} {f f' : Frame} {code : List Admin}
    {q : List (Call (wasmHostSig H))} (h : RunL P host s f code q (s', f', .trap)) :
    EvRun P host ⟨s, f, code⟩ q ⟨s', f', [.trap]⟩ := by
  obtain ⟨c', o, h, he, hm⟩ := h
  rcases o with _ | _ | _ | _ | _ | _ | _ <;> simp only [FlowMatch] at hm
  have hc : c' = [.trap] := he
  subst hc
  exact h

/-- **A callee body trapping in its frame traps the call**, in any caller frame `g`. -/
theorem callRef_trap_of_body {s : Store H} {a : Nat} {us : List Val} {fi : FuncInst H}
    {fn : Func} {ps rs : List Validation.CValType} {q : List (Call (wasmHostSig H))}
    (hS : StoreChk s.funcs) (hn : us.length = ps.length) (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hb : ∀ {out : Option Nat}, chk s.funcs (Frame.forCall fi.module us fn.locals).module
      (Frame.forCall fi.module us fn.locals).locals.length rs.length [rs.length]
      (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some out →
      TrapRun P host ⟨s, Frame.forCall fi.module us fn.locals, vals ([] : List Val).reverse ++
        expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ q)
    (g : Frame) :
    ∃ s', EvRun P host ⟨s, g, vals us ++ [.ref (.func a), .callRefType fi.type]⟩ q
      ⟨s', g, [.trap]⟩ := by
  obtain ⟨ob, hbc⟩ := body_chk (y := ⟨a, (us, s)⟩) hS hfi hcode hty hn
  obtain ⟨s', f', run⟩ := hb hbc
  have enter := enter_body (P := P) (y := ⟨a, (us, s)⟩) hfi hcode hty hn g
  rw [callAt_code (y := ⟨a, (us, s)⟩) hfi] at enter
  have inner := evRun_frame (f := g) rs.length (evRun_label rs.length [] run)
  have hout : Steps P NH ⟨s', g, [.frame rs.length f' [.label rs.length [] [.trap]]]⟩
      ⟨s', g, [.trap]⟩ :=
    (Relation.ReflTransGen.single (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame
  exact ⟨s', by simpa using evRun_trans (evRun_of_free enter) (evRun_trans inner
    (evRun_of_free hout))⟩

/-! ## A reach into a trapping callee -/

/-- **A logged reach into a trapping callee is a Core run to a trap** with exactly the events
of the resolved prefix, then those of the callee. -/
theorem reachL_trap (hH : Interp.NativeHostSlice host) {s : Store H} {f : Frame}
    {stk : List Val} {es : List Binaryen.BExpr} {l : List (OCall H)}
    {y : (wasmOShape H).self.Op} (h : ReachL s f stk es l y) :
    ∀ q, SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) q → Cons host q →
      ∀ c₁ : List (Call (wasmHostSig H)),
      (∀ F : Frame, ∃ s', EvRun P host (callAt y F) c₁ ⟨s', F, [.trap]⟩) →
      ∀ {labels : List Nat} {ret : Nat} {out : Option Nat}, StoreChk s.funcs →
      chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
      TrapRun P host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩
        (q ++ c₁) := by
  induction h with
  | @here s s₁ f f₁ stk stk₁ x args es a fi ps rs l hargs hfi hty =>
    intro q hq hc c₁ hcal labels ret out hS hchk
    obtain ⟨d, cl⟩ := evalL_fwd (P := P) hH hargs q (substPre_mono (close_le_goodC hH) hq) hc
    obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨c', o', hrun, he, hm⟩ := cl hS ha
    have hc' : c' = vals stk₁.reverse := ends_normal hm he
    subst hc'
    have hfa := Silmaril.Wasm.Interp.funcs_of_func? hfi
    obtain ⟨s', hcr⟩ := hcal f₁
    rw [callAt_code (y := ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩) hfa] at hcr
    have hcall := evRun_oracle_call (rest := expression (Binaryen.BExpr.lowerList es)) hfi hcr
    have r1 := evRun_append (rest := .plain (.call x) :: expression (Binaryen.BExpr.lowerList es))
      hrun
    have hout : Steps P NH ⟨s', f₁, vals (stk₁.drop ps.length).reverse ++ [.trap] ++
        expression (Binaryen.BExpr.lowerList es)⟩ ⟨s', f₁, [.trap]⟩ := by
      simpa using Silmaril.Wasm.Logic.Core.steps_trap (P := P) (host := NH) s' f₁
        (stk₁.drop ps.length).reverse (expression (Binaryen.BExpr.lowerList es))
    rw [code_op]
    exact ⟨s', f₁, by simpa using evRun_trans r1 (evRun_trans hcall (evRun_of_free hout))⟩
  | @args s f stk i args es l y _ ih =>
    intro q hq hc c₁ hcal labels ret out hS hchk
    obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    rw [code_op]
    simpa [vals] using trapRun_ctx [] (.plain i :: expression (Binaryen.BExpr.lowerList es))
      (ih q hq hc c₁ hcal hS ha)
  | @callK s s₁ s₂ f f₁ stk stk₁ ws x args es a fi ps rs l₁ l₂ y hargs hfi hty _ ih =>
    intro q hq hc c₁ hcal labels ret out hS hchk
    have e : (l₁ ++ OCall.mk a (stk₁.take ps.length).reverse s₁ (.inl ws) s₂ :: l₂).map
        OCall.lift = (l₁ ++ [OCall.mk a (stk₁.take ps.length).reverse s₁ (.inl ws) s₂]).map
          OCall.lift ++ l₂.map OCall.lift := by simp
    rw [e] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH (.callRet hargs hfi hty .nil) h₁ hc.1 hS hchk
    simpa [List.append_assoc] using trapRun_pre run (ih q₂ h₂ hc.2 c₁ hcal hS' hchk')
  | opK hi hargs hflat _ ih =>
    intro q hq hc c₁ hcal labels ret out hS hchk
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    have hE := EvalL.opOk hi hargs hflat (es := []) .nil
    rw [List.append_nil] at hE
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH hE h₁ hc.1 hS hchk
    simpa [List.append_assoc] using trapRun_pre run (ih q₂ h₂ hc.2 c₁ hcal hS' hchk')
  | @block s f stk bt body es np nr l y har _ ih =>
    intro q hq hc c₁ hcal labels ret out hS hchk
    obtain ⟨⟨ob, hbc⟩, enter⟩ := block_enter (P := P) har hchk
    have := trapRun_ctx (stk.drop np).reverse (expression (Binaryen.BExpr.lowerList es))
      (trapRun_label nr [] (ih q hq hc c₁ hcal hS hbc))
    simpa using trapRun_pre (evRun_of_free enter) this
  | blockK har hbody hvs _ ih =>
    intro q hq hc c₁ hcal labels ret out hS hchk
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    have hE := EvalL.blockOk har hbody hvs (es := []) .nil
    rw [List.append_nil] at hE
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH hE h₁ hc.1 hS hchk
    simpa [List.append_assoc] using trapRun_pre run (ih q₂ h₂ hc.2 c₁ hcal hS' hchk')
  | @loop s f stk bt body es np nr l y har _ ih =>
    intro q hq hc c₁ hcal labels ret out hS hchk
    obtain ⟨⟨ob, hbc⟩, enter⟩ := loop_enter (P := P) har hchk
    have := trapRun_ctx (stk.drop np).reverse (expression (Binaryen.BExpr.lowerList es))
      (trapRun_label np [.loop bt (Binaryen.BExpr.lowerList body)] (ih q hq hc c₁ hcal hS hbc))
    simpa using trapRun_pre (evRun_of_free enter) this
  | loopK har hbody _ ih =>
    intro q hq hc c₁ hcal labels ret out hS hchk
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    have hE := EvalL.loopOk har hbody (es := []) .nil
    rw [List.append_nil] at hE
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH hE h₁ hc.1 hS hchk
    simpa [List.append_assoc] using trapRun_pre run (ih q₂ h₂ hc.2 c₁ hcal hS' hchk')
  | loopBack har hbody _ ih =>
    intro q hq hc c₁ hcal labels ret out hS hchk
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨run, hS', hchk'⟩ := loopBack_glue (P := P) hH har hbody h₁ hc.1 hS hchk
    simpa [List.append_assoc] using trapRun_pre run (ih q₂ h₂ hc.2 c₁ hcal hS' hchk')
  | @cond s f stk bt c t el es l y _ ih =>
    intro q hq hc c₁ hcal labels ret out hS hchk
    obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oc, hco, -⟩ := chk1_ifE h1
    rw [code_if]
    simpa [vals] using trapRun_ctx [] (.plain (.if_ bt (Binaryen.BExpr.lowerList t)
      (Binaryen.BExpr.lowerList el)) :: expression (Binaryen.BExpr.lowerList es))
      (ih q hq hc c₁ hcal hS hco)
  | @arm s s₁ f f₁ stk stk₁ cv b bt c t el es np nr l₁ l₂ y hcE hb har _ ih =>
    intro q hq hc c₁ hcal labels ret out hS hchk
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨hS', ⟨ob, hbc⟩, run⟩ := arm_glue (P := P) hH hcE hb har h₁ hc.1 hS hchk
    simpa [List.append_assoc] using trapRun_pre run (trapRun_ctx _ _
      (trapRun_label nr [] (ih q₂ h₂ hc.2 c₁ hcal hS' hbc)))
  | ifK hcE hb har harm hvs _ ih =>
    intro q hq hc c₁ hcal labels ret out hS hchk
    rw [List.map_append, List.map_append] at hq
    obtain ⟨q₁₂, q₃, rfl, h₁₂, h₃⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    have hE := EvalL.ifOk hcE hb har harm hvs (es := []) .nil
    rw [List.append_nil] at hE
    rw [← List.map_append] at h₁₂
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH hE h₁₂ hc.1 hS hchk
    simpa [List.append_assoc] using trapRun_pre run (ih q₃ h₃ hc.2 c₁ hcal hS' hchk')

/-! ## Trapping resolutions -/

/-- **A trapping resolution** resolves every internal call, the open behaviour itself trapping;
or resolves a prefix and then meets a callee that traps. -/
theorem subst_trap_inv {sh : Silmaril.Games.Abstract.Shape} {c : sh.ClosedMod} {R : Type}
    {x : List (Call (sh.E ⊕ₛ sh.self))} {e : End sh.S R} {y : CallBeh sh.E sh.S R}
    (h : Shape.Subst c x e y) (hy : y.2 = .trap) :
    (SubstPre c x y.1 ∧ e = .trap) ∨
      ∃ (u : List (Call (sh.E ⊕ₛ sh.self))) (z : sh.self.Op) (ans : sh.self.Ar z)
        (rest : List (Call (sh.E ⊕ₛ sh.self))) (q c₁ : List (Call sh.E)),
        x = u ++ ⟨.inr z, ans⟩ :: rest ∧ SubstPre c u q ∧ (c₁, .trap) ∈ c z.1 z.2.2 z.2.1 ∧
          y.1 = q ++ c₁ := by
  induction h with
  | nil e => exact .inl ⟨.nil, hy⟩
  | @ext m n rest e y _ ih =>
    rcases ih hy with ⟨h₁, h₂⟩ | ⟨u, z, ans, rest', q, c₁, rfl, hu, hm, hq⟩
    · exact .inl ⟨.ext h₁, h₂⟩
    · exact .inr ⟨⟨.inl m, n⟩ :: u, z, ans, rest', ⟨m, n⟩ :: q, c₁, rfl, .ext hu, hm,
        by simp [hq]⟩
  | @int g a s b s' rest e c₂ y hc _ ih =>
    rcases ih hy with ⟨h₁, h₂⟩ | ⟨u, z, ans, rest', q, c₁, rfl, hu, hm, hq⟩
    · exact .inl ⟨.int hc h₁, h₂⟩
    · exact .inr ⟨⟨.inr ⟨g, (a, s)⟩, (b, s')⟩ :: u, z, ans, rest', c₂ ++ q, c₁, rfl,
        .int hc hu, hm, by simp [hq]⟩
  | @intTrap g a s ans rest e c₁ hc =>
    exact .inr ⟨[], ⟨g, (a, s)⟩, ans, rest, [], c₁, rfl, .nil, hc, rfl⟩
  | intDiv _ => cases hy

/-! ## The trapping behaviours that are logged Core runs -/

/-- **Trapping closed behaviours that are logged Core runs**: closed behaviours which, when they
trap with a consistent log, are a Core run of the call to a trap, in any frame, with exactly that
log, for a checked store and typed arguments. -/
def GoodT (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) :
    (wasmHShape H).ClosedMod := fun a s us =>
  {y | y ∈ Shape.close wasmHOpen a s us ∧ (y.2 = .trap → Cons host y.1 →
    ∀ (fi : FuncInst H) (ps rs : List Validation.CValType), s.funcs[a]? = some fi →
      Validation.DefType.funcType? fi.type = some (ps, rs) → StoreChk s.funcs →
      us.length = ps.length → ∀ g : Frame,
        ∃ s', EvRun P host ⟨s, g, vals us ++ [.ref (.func a), .callRefType fi.type]⟩ y.1
          ⟨s', g, [.trap]⟩)}

theorem goodT_le_close : GoodT (H := H) P host ≤ Shape.close wasmHOpen :=
  fun _ _ _ _ h => h.1

/-- **Every closed behaviour is in `GoodT`**: least-fixpoint induction. -/
theorem close_le_goodT (hH : NativeHostSlice host) :
    Shape.close (wasmHOpen (H := H)) ≤ GoodT P host := by
  refine OrderHom.lfp_le _ ?_
  rintro a s us y ⟨x, hx, hS⟩
  refine ⟨?_, ?_⟩
  · rw [Shape.close, ← OrderHom.map_lfp]
    exact ⟨x, hx, hS.mono goodT_le_close⟩
  intro htr hq fi ps rs hfi hty hSt hn g
  rcases hx with ⟨fi', fn, ps', rs', s', f₂, bfl, fl, l, hfi', hc, hty', hE, hxf, rfl⟩ |
    ⟨fi', hh, ps', rs', s', r, fl, hfi', hc, hty', hxf, rfl⟩
  · obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
    rcases subst_trap_inv hS htr with ⟨hpre, he⟩ |
      ⟨u, z, ans, rest, q, c₁, hsplit, hu, hm, hy⟩
    · -- the body traps itself
      have hfl : fl = .trap := by rcases fl <;> simp_all [endOfFlow]
      subst hfl
      have hbfl : bfl = .trap := by
        rcases bfl with w | ⟨_ | k, w⟩ | w | _ | t <;> simp_all [exitFlow]
      subst hbfl
      obtain ⟨-, cl⟩ := evalL_fwd (P := P) hH hE y.1
        (substPre_mono (le_trans goodT_le_close (close_le_goodC hH)) hpre) hq
      exact callRef_trap_of_body hSt hn hfi hc hty
        (fun hbc => ⟨s', f₂, trapRun_of_runL (cl hSt hbc)⟩) g
    · -- the body reaches a trapping callee
      have hD : Shape.Descends wasmHOpen (GoodT P host) ⟨a, (us, s)⟩ q z :=
        ⟨_, .inl ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hfi, hc, hty, hE, hxf, rfl⟩, u, ans, rest,
          hsplit, hu⟩
      obtain ⟨fi'', fn', ps'', rs'', l₁, hfi'', hc', hty'', hr, hq₁⟩ := descends_unwrap hD
      obtain rfl : fi = fi'' := Option.some.inj (hfi.symm.trans hfi'')
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty''))
      obtain rfl : fn = fn' := by rw [hc] at hc'; exact FuncCode.wasm.inj hc'
      rw [hy] at hq
      obtain ⟨hcq, hcc⟩ := cons_append.1 hq
      have hq₁' := substPre_mono goodT_le_close hq₁
      obtain ⟨ob, hbc⟩ := body_chk (y := ⟨a, (us, s)⟩) hSt hfi hc hty hn
      obtain ⟨⟨fz, psz, rsz, hfz, htz, hnz, hSz⟩, -⟩ :=
        reachL_fwd (P := P) hH hr q hq₁' hcq hSt hbc
      have hcal : ∀ F : Frame, ∃ s'', EvRun P host (callAt z F) c₁ ⟨s'', F, [.trap]⟩ := by
        intro F
        rw [callAt_code hfz]
        exact hm.2 rfl hcc fz psz rsz hfz htz hSz hnz F
      rw [hy]
      exact callRef_trap_of_body hSt hn hfi hc hty
        (fun hbc' => reachL_trap (P := P) hH hr q hq₁' hcq c₁ hcal hSt hbc') g
  · obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
    cases hS with
    | ext h =>
      cases h
      have hm : host hh s us (.returned s' r) := hq _ List.mem_cons_self
      have hfl : fl = .trap := by rcases fl <;> simp_all [endOfFlow]
      subst hfl
      have hr : r = .trap := by
        rcases r with w | t | _ <;> simp_all [resFlow, exitFlow]
      subst hr
      obtain ⟨ps₀, rs₀, he', hpl, -⟩ := expand_of_funcType hty
      exact ⟨s', .event (hEvStep_host_call hfi he' (hn.trans hpl.symm) hc hm) (.refl _)⟩

/-- **A trapping closed behaviour with a consistent log is a Core run of the call to a trap**
with exactly that log, in any frame, every profile. -/
theorem close_trap_evRun (hH : NativeHostSlice host) {a : Nat} {s : Store H} {us : List Val}
    {c₁ : List (Call (wasmHostSig H))} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (hm : (c₁, .trap) ∈ Shape.close wasmHOpen a s us) (hc : Cons host c₁)
    (hS : StoreChk s.funcs) (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length)
    (f : Frame) :
    ∃ s', EvRun P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩ c₁
      ⟨s', f, [.trap]⟩ :=
  (close_le_goodT (P := P) hH a s us hm).2 rfl hc fi ps rs hfi hty hS hn f

/-- **A trapping behaviour of an invocation with a consistent log is a Core run of the
invocation to a trap with exactly that log**, every profile. -/
theorem wasmEvFun_trap_evRun (hH : NativeHostSlice host) {s : Store H} {a : Nat}
    {vs : List Val} (hS : StoreChk s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .trap) ∈ wasmEvFun s (a, vs))
    (hc : Cons host cs) : ∃ s₂, EvRun P host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ := by
  obtain ⟨fi, ps, rs, hfi, he, -⟩ := id hok
  have hty := funcType_of_expand he
  have hinv : invoke s a vs = ⟨s, {}, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩ := by
    simp [invoke, hfi]
  rw [hinv]
  exact close_trap_evRun hH h hc hS hfi hty (args_length hok hfi hty) {}

end Silmaril.Proofs.Wasm.Abstract.HostClosingInf
