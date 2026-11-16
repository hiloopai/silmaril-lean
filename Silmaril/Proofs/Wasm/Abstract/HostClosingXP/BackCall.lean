module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackGoal

/-!
# The logged backward simulation of a call (proofs)

`callG_step`: `CallG n` from `BackG m` and `CallG m` for `m < n`. A host callee is one event
(`evRunN_host_callRef`); its answer is a closed behaviour (`close_hostX`), a trap ending the run.
A Wasm callee's only step enters its frame (`callRef_wasm_unique`); the body runs alone
(`evRunN_frame_seq_split`) and is a resolved logged run (`BackG`). Its end leaves the frame:

* values or an exception: `exit_frame_ans`, the run going on from the answer;
* a trap, or Core's pending null tail call: the frame traps, with no further event;
* a pending tail call: `return_call_ref-label` and `return_call_ref-frame-addr`
  (`frame_tail_exit`), then the tail callee in the caller's frame, by `CallG` on the strictly
  shorter rest of the run, so a host tail callee is its one event there.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- **A `call_ref` of Wasm code on exactly its arguments has one step**: it enters the callee's
frame. -/
theorem callRef_wasm_unique {s : Store H} {f : Frame} {pre us : List Val} {a : Nat} {cr : Admin}
    {rest : List Admin} {fi : FuncInst H} {fn : Func} {ps rs : Validation.Ty (.list .val)}
    {c₁ : Config H} (hcr : cr.IsCallRef) (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hex : Validation.Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (h : Step P host ⟨s, f, Interp.callCode pre us a cr rest⟩ c₁) :
    c₁ = ⟨s, f, vals pre ++ [.frame rs.length (Frame.forCall fi.module us fn.locals)
      [.label rs.length [] (expression fn.body)]] ++ rest⟩ := by
  have e : Interp.callCode pre us a cr rest = vals (pre ++ us) ++ .ref (.func a) :: cr :: rest := by
    simp [Interp.callCode]
  rw [e] at h
  obtain ⟨vs₁, vs₂, ps', rs', hsplit, he, hn', rfl⟩ := Step.callRef_wasm_inv_seq hcr hf hcode h
  have := (Validation.Expand.iff.1 hex).symm.trans (Validation.Expand.iff.1 he)
  simp only [Option.some.injEq, Validation.Ty.func.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  obtain ⟨rfl, rfl⟩ := List.append_inj' hsplit (hn.trans hn'.symm)
  simp

/-- The code a callee frame traps from: a trap, or Core's pending null tail call. -/
def TrapCode (code : List Admin) : Prop :=
  code = [.trap] ∨ ∃ (vs : List Val) (c₀ : Admin) (rest₀ : List Admin), c₀.IsReturnCallRef ∧
    code = vals vs ++ .ref .null :: c₀ :: rest₀

theorem trapCode_of_endOK {s' : Store H} {f₂ : Frame} {cb : Config H}
    (h : EndOK (s', f₂, .flow .trap) cb) : TrapCode cb.code := by
  rcases h with ⟨oc, he, hm⟩ | ⟨-, hc⟩
  · rcases matchP_flow_iff.mp hm with ⟨-, -, hfm⟩ | ⟨-, vs, c₀, rfl, hc₀, -, -⟩
    · rcases oc with _ | _ | _ | _ | _ | _ | _ <;> simp only [FlowMatch] at hfm
      exact .inl he
    · obtain ⟨-, rest₀, hc⟩ := he
      exact .inr ⟨vs, c₀, rest₀, hc₀, hc⟩
  · exact .inl hc

/-- A callee frame around trapping code traps. -/
theorem frame_trap_steps {s : Store H} {f F : Frame} {k : Nat} {code : List Admin}
    (hc : TrapCode code) :
    Steps P NH ⟨s, f, [.frame k F [.label k [] code]]⟩ ⟨s, f, [.trap]⟩ := by
  rcases hc with rfl | ⟨vs, c₀, rest₀, hc₀, rfl⟩
  · exact (Relation.ReflTransGen.single (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame
  · refine (Relation.ReflTransGen.single (Step.ctxtFrame (label_step_tailNull hc₀))).tail ?_
    have e : vals vs ++ .ref .null :: c₀ :: [] = vals vs ++ [.ref .null, c₀] ++ [] := by simp
    rw [e]
    exact Step.returnCallRefFrameNull hc₀

/-- After a callee frame around trapping code, a labelled run makes no event. -/
theorem trapCode_nil {o : GrowOracle} {s : Store H} {f F : Frame} {k : Nat} {code : List Admin}
    {pre : List Val} {rest : List Admin} {n : Nat} {cs : List (Call (wasmHostSig H))} {c : Config H}
    (hc : TrapCode code)
    (h : EvRunN (profile o) host n ⟨s, f, vals pre ++ [.frame k F [.label k [] code]] ++ rest⟩ cs c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c') : cs = [] := by
  have hw : WP (profile o) NH s f (vals pre ++ [.frame k F [.label k [] code]] ++ rest)
      (fun _ _ oc => oc = .trap) := by
    refine WP.steps (Steps.ctx pre rest (frame_trap_steps hc)) ?_
    have := wp_trap (P := profile o) (host := NH) (s := s) (f := f) (vs := pre) (rest := rest)
      (Q := fun _ _ oc => oc = .trap) rfl
    simpa using this
  exact (wp_end hw h hend).1

/-- The closure behaviour of a call answered by a host function. -/
theorem host_ans_close (hH : NativeHostSlice host) {s s' : Store H} {a : Nat} {us : List Val}
    {fi : FuncInst H} {hh : H} {ps rs : List Validation.CValType} {ws : List Val}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hans : host hh s us (.returned s' (.values ws))) :
    ([⟨(hh, s, us), (s', .values ws)⟩], .ret (.inl ws) s') ∈ Cl a s us := by
  have hw := hH.arity s a fi hh _ _ us ws s' hf hcode hty hans
  have hx : exitFlow rs.length (resFlow (.values ws)) = some (.normal ws) := by
    simp only [resFlow, exitFlow, Option.some.injEq, Binaryen.Flow.normal.injEq]
    rw [List.take_of_length_le (by simp [hw])]
    simp
  exact close_hostX hf hcode hty hx

section Step

variable {tags : List TagInst} {o : GrowOracle}

/-- **The logged backward simulation of a call**, from the statements for strictly shorter
runs. -/
theorem callG_step (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {n : Nat} (ihB : ∀ m < n, ∀ es, BackG tags o host m es) (ihC : ∀ m < n, CallG tags o host m) :
    CallG tags o host n := by
  intro s₁ f₁ pre us a cr rest c cs hcr hcc hct hrun hend hnd
  obtain ⟨hS, hts, fi, ps, rs, hfi, hty, hn⟩ := id hcc
  obtain ⟨ps', rs', hex, hpl, hrl⟩ := expand_of_funcType hty
  have hn' : us.length = ps'.length := hn.trans hpl.symm
  cases hcode : fi.code with
  | host hh =>
    have hrun' : EvRunN (profile o) host n
        ⟨s₁, f₁, vals pre ++ vals us ++ .ref (.func a) :: cr :: rest⟩ cs c := by
      simpa [Interp.callCode] using hrun
    rcases evRunN_host_callRef hcr hfi hcode hex hn' hrun' with ⟨rfl, -⟩ |
      ⟨s', r, m, cs', hm, rfl, hans, hk⟩
    · exfalso
      have hd := decompose?_wrap (s := s₁) pre rest (decompose?_redex hcr hfi hex hn' hcode)
      simp only [List.append_assoc, List.cons_append, List.nil_append]
        at hnd hd
      rw [hd] at hnd
      cases hnd
    · rcases r with ws | t | _
      · exact .inl ⟨_, .inl ws, s', m, cs', host_ans_close hH hfi hcode hty hans, rfl, hm,
          by simpa [ansCode, Result.toAdmin] using hk⟩
      · exact (hH.noThrow _ _ _ _ _ hans).elim
      · have hk' : EvRunN (profile o) host m ⟨s', f₁, vals pre ++ .trap :: rest⟩ cs' c := by
          simpa [Result.toAdmin] using hk
        obtain ⟨-, rfl⟩ := evRunN_trap_head hk' hend
        exact .inr (close_hostX (r := .trap) (fl := .trap) hfi hcode hty rfl)
  | wasm fn =>
    let F := Frame.forCall fi.module us fn.locals
    have hstep : Step (profile o) Det.noHost ⟨s₁, f₁, Interp.callCode pre us a cr rest⟩
        ⟨s₁, f₁, vals pre ++ [.frame rs'.length F [.label rs'.length [] (expression fn.body)]] ++
          rest⟩ :=
      Silmaril.Wasm.Logic.Core.Step.ctx pre rest (Step.callRefFunc hcr hfi hex hn' hcode)
    obtain ⟨m, rfl, hrun₁⟩ := evRunN_unique (fun c₁ h => callRef_wasm_unique hcr hfi hcode hex hn' h)
      hstep hrun hend
    rw [hrl] at hrun₁
    obtain ⟨cb, N₁, cs₁, cs₂, rfl, hN₁, h₁, hend₁, hk, hx⟩ := evRunN_frame_seq_split hrun₁ hend
    -- the body's end is not at a host call
    have hnd₁ : decompose? cb.store cb.code = none := by
      cases hdc : decompose? cb.store cb.code with
      | none => rfl
      | some x =>
        exfalso
        obtain ⟨-, rfl⟩ := hx (by simp [hdc])
        have hl : (decompose? cb.store [.label rs.length [] cb.code]).isSome := by
          obtain ⟨E, a', hh, us'⟩ := x
          rw [decompose?_label_some hdc]
          rfl
        have := decompose?_wrap_frame (ws := pre) (n := rs.length) (F := cb.frame) (rest := rest) hl
        rw [hnd] at this
        cases this
    -- the body is typed
    have hctB : TypedP tags s₁ F [] (Binaryen.liftInstrs fn.body) :=
      callee_typedP ⟨hcc, f₁, cr, pre, rest, hcr, hct⟩ hfi hcode
    have hcodeB : tcode [] (Binaryen.liftInstrs fn.body) = expression fn.body := by
      simp [tcode, Binaryen.lowerList_liftInstrs, vals]
    have h₁' : EvRunN (profile o) host N₁ ⟨s₁, F, tcode [] (Binaryen.liftInstrs fn.body)⟩ cs₁ cb := by
      rw [hcodeB]; exact h₁
    obtain ⟨l, ⟨s', f₂, ob⟩, hd, hres, hok⟩ :=
      ihB N₁ (by omega) _ s₁ F [] cb cs₁ hctB h₁' hend₁ hnd₁
    have hcons₁ : Cons host cs₁ := evRun_consistent (evRunN_evRun h₁)
    -- typing of the configurations after the body
    have hstB : Steps (profile o) host ⟨s₁, f₁, Interp.callCode pre us a cr rest⟩
        ⟨cb.store, f₁, vals pre ++ [.frame rs.length cb.frame [.label rs.length [] cb.code]] ++
          rest⟩ := by
      refine (Relation.ReflTransGen.single (Step.of_noHost host hstep)).trans ?_
      rw [hrl]
      exact Steps.ctx pre rest (Steps.frame rs.length (Steps.label rs.length [] (evRunN_steps h₁)))
    have hctX := ContextTyped.steps_typed hT hct hstB
    obtain ⟨obc, hobc, hbc⟩ := body_chk (tags := tags) hS hfi hcode hty hn
    rcases hres with hq | ⟨htr, hq⟩
    swap
    · -- cut at a trapping callee
      simp only at htr
      subst htr
      have hcs₂ := trapCode_nil (trapCode_of_endOK hok) hk hend
      subst hcs₂
      rw [List.append_nil]
      exact .inr (close_wasm_trap hfi hcode hty hd hq rfl)
    obtain ⟨-, t₁, a₁, -⟩ := full_run (P := profile o) hH hE hd
      (substPre_mono (close_le_goodCX hH hE) hq) hcons₁ hts
    obtain ⟨hpo, hinv, htw⟩ := a₁ hS hbc
    cases ob with
    | flow bfl =>
      have hfo : FlowOkE true [rs.length] rs.length obc bfl := hpo
      by_cases hbt : bfl = .trap
      · subst hbt
        have hcs₂ := trapCode_nil (trapCode_of_endOK hok) hk hend
        subst hcs₂
        rw [List.append_nil]
        exact .inr (close_wasm_flow (fl := .trap) hfi hcode hty hd hq rfl)
      obtain ⟨fl, hxf⟩ : ∃ fl, exitFlow rs.length bfl = some fl := by
        rcases bfl with w | ⟨_ | k, w⟩ | w | _ | t
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
        · obtain ⟨k', hk', -⟩ := hfo
          simp at hk'
        · exact ⟨_, rfl⟩
        · exact absurd rfl hbt
        · exact ⟨_, rfl⟩
      obtain ⟨b, hbend⟩ : ∃ b, endOfFlow fl s' = .ret b s' := by
        rcases bfl with w | ⟨_ | k, w⟩ | w | _ | t <;>
          simp only [exitFlow, Option.some.injEq, reduceCtorEq] at hxf
        all_goals (try exact absurd rfl hbt)
        all_goals (subst hxf; exact ⟨_, rfl⟩)
      rcases hok with ⟨oc, he, hm⟩ | ⟨h, -⟩
      swap
      · cases h; exact absurd rfl hbt
      obtain ⟨hs', hf', hfm⟩ := match_of_matchP hbt hm
      have hex' := exit_frame_ans (P := profile o) (f := f₁) (F := cb.frame) (n := rs.length)
        he hfm hxf hbend hfo hobc
      rw [← hs'] at hex'
      obtain ⟨m', hm', hk'⟩ := through (Steps.ctx pre rest hex') hk hend
      refine .inl ⟨cs₁, b, s', m', cs₂, ?_, rfl, by omega, by rw [← hs']; exact hk'⟩
      have := close_wasm_flow hfi hcode hty hd hq hxf
      rwa [hbend] at this
    | tail a' args k =>
      have hkr : k = rs.length := hpo
      subst hkr
      obtain ⟨fi₂, ps₂, rs₂, hfi₂, hty₂, hargs, hrs₂⟩ := htw a' args rs.length rfl
      obtain ⟨ps₂', rs₂', hex₂, hpl₂, -⟩ := expand_of_funcType hty₂
      rcases hok with ⟨oc, he, hm⟩ | ⟨h, -⟩
      swap
      · cases h
      obtain ⟨vs₁, c₀, rfl, hc₀, hs', hf'⟩ := matchP_tail_iff.mp hm
      obtain ⟨-, rest₀, hcb⟩ := he
      have hex' := frame_tail_exit (P := profile o) (host := NH) (s := cb.store) (f := f₁)
        (k := rs.length) (F := cb.frame) (vs₁ := vs₁) (rest := rest₀) hc₀ (hs' ▸ hfi₂) hex₂
        (hargs.trans hpl₂.symm)
      rw [← hcb] at hex'
      have hst := Steps.ctx pre rest hex'
      obtain ⟨m', hm', hk'⟩ := through hst hk hend
      have hcc₂ : CallChkP tags s' a' args :=
        ⟨hinv.1.2.1 hS, t₁, fi₂, ps₂, rs₂, hfi₂, hty₂, hargs⟩
      have hct₂ : Sim.ContextTyped ⟨s', f₁,
          Interp.callCode pre args a' (c₀.retToCallIn cb.frame.module) rest⟩ := by
        have := ContextTyped.steps_typed hT hctX (steps_host hst)
        rw [hs'] at this
        simpa [Interp.callCode] using this
      have hk'' : EvRunN (profile o) host m' ⟨s', f₁,
          Interp.callCode pre args a' (c₀.retToCallIn cb.frame.module) rest⟩ cs₂ c := by
        rw [← hs']
        simpa [Interp.callCode] using hk'
      rcases ihC m' (by omega) s' f₁ pre args a' _ rest c cs₂
          (isCallRef_retToCallIn hc₀ _) hcc₂ hct₂ hk'' hend hnd with
        ⟨q', b', s₃, m'', cs₃, hz, rfl, hm'', hk₃⟩ | hz
      · obtain ⟨fi₃, ps₃, rs₃, hfi₃, hty₃⟩ := close_fn hz
        have hb : ∀ ws, b' = .inl ws → ws.length ≤ rs.length := by
          rintro ws rfl
          obtain ⟨fi₄, ps₄, rs₄, hfi₄, hty₄, hl⟩ := close_ret_len hz
          rw [hfi₂] at hfi₄
          obtain rfl := Option.some.inj hfi₄
          rw [hty₂] at hty₄
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hty₄)
          omega
        refine .inl ⟨cs₁ ++ q', b', s₃, m'', cs₃, ?_, by simp, by omega, hk₃⟩
        have := close_wasm_tail hfi hcode hty hd hq hz
        rwa [tailAns_eq hb] at this
      · exact .inr (close_wasm_tailTrap hfi hcode hty hd hq hz)

end Step

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
