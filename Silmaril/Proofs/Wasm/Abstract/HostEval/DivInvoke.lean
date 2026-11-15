module

public import Silmaril.Proofs.Wasm.Abstract.HostEval.DivWhole
public import Silmaril.Proofs.Wasm.Abstract.HostEval.Invoke

/-!
# Divergent invocations with host calls (proofs)

`invoke_div`: in the deterministic profile `SingleThreaded.profile o`, for a host with typed
answers in the native host slice, a divergent Core run of a typed invocation `invoke s a vs`
of a store whose functions pass the arity check diverges at a host call the host may diverge
on (the invoked host function itself, or a pending call `PendO` of the invoked Wasm function),
or the body of the invoked Wasm function diverges in the open native semantics with host calls
(`CallDivO (hostCall host)`). The invocation-level form of `div_whole`: a host function is read
off `HostCall.diverges_host_call`; a Wasm function's body is split off its frame
(`HostCall.diverges_frame_seq_split`) and given by `div_whole`, and a body that ends cannot
make the empty outer frame diverge.

`invoke_div_decomp` combines it with `callDivO_path_or_chain`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {host : HostSemantics H}

/-- **Divergent invocations with host calls** (deterministic profile). -/
theorem invoke_div {o : GrowOracle} (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (hd : Diverges (profile o) host (invoke s a vs)) :
    (∃ (y : (wasmOShape H).self.Op) (fi : FuncInst H) (hh : H),
        (y = ⟨a, (vs, s)⟩ ∨ PendO (hostCall host) ⟨a, (vs, s)⟩ y) ∧
        y.2.2.funcs[y.1]? = some fi ∧ fi.code = .host hh ∧ host hh y.2.2 y.2.1 .diverged) ∨
      CallDivO (hostCall host) ⟨a, (vs, s)⟩ := by
  obtain ⟨-, -, rts, -, -, hcok⟩ := invoke_ok hs hok
  obtain ⟨fi, ps', rs', hfi, hex, hvt⟩ := hok
  have hty := Interp.funcType_of_expand hex
  have hlen : vs.length = ps'.toList.length :=
    Interp.args_length ⟨fi, ps', rs', hfi, hex, hvt⟩ hfi hty
  have hinv : invoke s a vs = ⟨s, {}, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩ := by
    simp [invoke, hfi]
  rw [hinv] at hd
  have hlen' : vs.length = ps'.length := by simpa [Validation.Ty.length] using hlen
  -- the argument split of a call at the invocation is trivial
  have hsplit : ∀ {vs₁ vs₂ : List Val}, vs = vs₁ ++ vs₂ → vs₂.length = vs.length → vs₁ = [] := by
    intro vs₁ vs₂ hv hn
    have h₁ := congrArg List.length hv
    simp only [List.length_append] at h₁
    rw [← List.length_eq_zero_iff]
    omega
  cases hcd : fi.code with
  | host hh =>
    obtain ⟨vs₁, vs₂, ps, rs, hv, he, hn, hdiv | ⟨s', res, hhost, hd₁⟩⟩ :=
      diverges_host_call (rest := []) (r := .callRefType fi.type) trivial hfi hcd hd
    all_goals
      have heq := (Validation.Expand.iff.1 he).symm.trans (Validation.Expand.iff.1 hex)
      simp only [Option.some.injEq, Validation.Ty.func.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain rfl := hsplit hv (hn.trans hlen'.symm)
      simp only [List.nil_append] at hv
      subst hv
    · exact .inl ⟨⟨a, (vs, s)⟩, fi, hh, .inl rfl, hfi, hcd, hdiv⟩
    · exfalso
      rcases res with ws | t | _
      · have hd₂ : Diverges (profile o) host ⟨s', {}, vals ws⟩ := by
          simpa [Result.toAdmin] using hd₁
        exact not_div_stuck (fun c' h => Sim.Step.not_vals h) hd₂
      · exact hH.noThrow hh s vs s' t hhost
      · exact trap_not_diverges (ws := []) (r := []) (by simpa [Result.toAdmin] using hd₁)
  | wasm fn =>
    obtain ⟨vs₁, vs₂, ps, rs, hv, he, hn, hd₁⟩ :=
      diverges_wasm_call (r := .callRefType fi.type) trivial hfi hcd hd
    have heq := (Validation.Expand.iff.1 he).symm.trans (Validation.Expand.iff.1 hex)
    simp only [Option.some.injEq, Validation.Ty.func.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain rfl := hsplit hv (hn.trans hlen'.symm)
    simp only [List.nil_append] at hv
    subst hv
    set F := Frame.forCall fi.module vs fn.locals with hF
    -- the callee body: checked and typed
    obtain ⟨ob, hb, hob⟩ := Interp.endsAt_eq (hS a fi fn _ _ hfi hcd hty)
    have hbc : Interp.chk s.funcs F.module F.locals.length rs.toList.length [rs.toList.length]
        (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
      rw [hF, Interp.forCall_length _ _ hlen]; exact hb
    have enter : Steps (profile o) Det.noHost
        ⟨s, {}, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩
        ⟨s, {}, [.frame rs.length F [.label rs.length [] (expression fn.body)]]⟩ :=
      .single (Step.callRefFunc trivial hfi he hn hcd)
    have htF : Sim.ContextTyped
        ⟨s, {}, vals [] ++ [.frame rs.length F [.label rs.length [] (expression fn.body)]] ++ []⟩ := by
      have := Sim.ContextTyped.steps (Sim.ContextTyped.of_configOk (hinv ▸ hcok)) enter
      simpa [vals] using this
    have hct : Sim.ContextTyped ⟨s, F, vals ([] : List Val).reverse ++
        expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ := by
      have h₁ := Sim.ContextTyped.frame htF
      have h₂ := Sim.ContextTyped.label (vs := []) (rest := []) (by simpa [vals] using h₁)
      simpa [Binaryen.lowerList_liftInstrs, vals] using h₂
    have hd₂ : Diverges (profile o) host
        ⟨s, {}, vals [] ++ [.frame rs.length F [.label rs.length [] (expression fn.body)]] ++ []⟩ := by
      simpa [vals] using hd₁
    rcases diverges_frame_seq_split hd₂ with hdb | ⟨⟨rcs, rcf, rcc⟩, hrb, hsb, hd₃⟩
    · rcases div_whole (o := o) hT hH s F [] (Binaryen.liftInstrs fn.body) _ _ _ hS hbc hct
          (by simpa [Binaryen.lowerList_liftInstrs, vals] using hdb) with
        ⟨y, fi', hh', hr, h1, h2, h3⟩ | hev
      · exact .inl ⟨y, fi', hh', .inr (pendO_of_body (x := ⟨a, (vs, s)⟩) hfi hcd hr), h1, h2, h3⟩
      · exact .inr ⟨fi, fn, hfi, hcd, hev⟩
    · exfalso
      dsimp only at hsb hd₃
      have hb' : Steps (profile o) host
          ⟨s, F, vals ([] : List Val).reverse ++
            expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ ⟨rcs, rcf, rcc⟩ := by
        simpa [Binaryen.lowerList_liftInstrs, vals] using hrb
      obtain ⟨fl, oc, hevb, hen, hm⟩ := body_end_frame hT hH hS hbc hct hb' hsb hd₃
      dsimp only at hevb hen
      have htyF := typed_frame_steps hT htF hrb
      dsimp only at htyF
      obtain ⟨hok', -⟩ := (Interp.evalH_good (P := profile o) hH hevb).1 hS hbc
      cases hvs : fl.retVals with
      | some ws =>
        have hrs := Interp.retVals_length hok' hob hvs
        have hnorm : ∀ ws, fl = .normal ws → ws.length = rs.toList.length := by
          intro ws hws; rw [hws] at hok'; exact Interp.length_of_ends hok' hob
        obtain ⟨s', res, hret', -⟩ := Silmaril.Wasm.Logic.Core.frame_ends
          (P := profile o) (host := Det.noHost) (f := {}) hen
          (Interp.funcPost_of_match (s₂ := rcs) (F := rcf) hm hvs hrs hnorm)
        have hx := Silmaril.Wasm.Logic.Core.Steps.ctx (P := profile o)
          (host := Det.noHost) [] [] hret'
        have hx' : Steps (profile o) Det.noHost
            ⟨rcs, {}, vals [] ++ [.frame rs.length rcf [.label rs.length [] rcc]] ++ []⟩
            ⟨s', {}, vals res⟩ := by
          simpa [vals, Validation.Ty.length] using hx
        have hd₄ : Diverges (profile o) host ⟨s', {}, vals res⟩ :=
          diverges_through_steps hx' htyF hd₃
        exact not_div_stuck (fun c' h => Sim.Step.not_vals h) hd₄
      | none =>
        have hfl : fl = .trap := by
          rcases hfl : fl with ws | ⟨_ | k, ws⟩ | ws | _ | t <;> rw [hfl] at hok' hvs <;>
            simp_all [Binaryen.Flow.retVals, Interp.FlowOk]
        subst hfl
        have hc' : rcc = [.trap] := by
          rcases oc with _ | _ | _ | _ | _ | _ | _ <;> simp only [Interp.FlowMatch] at hm
          exact hen
        subst hc'
        have hout : Steps (profile o) Det.noHost
            ⟨rcs, {}, vals [] ++ [.frame rs.length rcf [.label rs.length [] [.trap]]] ++ []⟩
            ⟨rcs, {}, vals [] ++ [.trap] ++ []⟩ :=
          Silmaril.Wasm.Logic.Core.Steps.ctx _ []
            ((Relation.ReflTransGen.single (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame)
        exact trap_not_diverges (ws := []) (r := [])
          (by simpa using diverges_through_steps hout htyF hd₃)

/-- **A divergent invocation, decomposed** (deterministic profile): it diverges at a host call
the host may diverge on, or reaches (as the invoked function or a pending call of it) a call
whose body diverges within its own function, or starts an infinite chain of descents into
callee bodies. -/
theorem invoke_div_decomp {o : GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hd : Diverges (profile o) host (invoke s a vs)) :
    (∃ (y : (wasmOShape H).self.Op) (fi : FuncInst H) (hh : H),
        (y = ⟨a, (vs, s)⟩ ∨ PendO (hostCall host) ⟨a, (vs, s)⟩ y) ∧
        y.2.2.funcs[y.1]? = some fi ∧ fi.code = .host hh ∧ host hh y.2.2 y.2.1 .diverged) ∨
      (∃ z, (z = ⟨a, (vs, s)⟩ ∨ PendO (hostCall host) ⟨a, (vs, s)⟩ z) ∧
        LocalCallDivO (hostCall host) z) ∨
      ∃ g : Nat → (wasmOShape H).self.Op, g 0 = ⟨a, (vs, s)⟩ ∧
        ∀ n, BodyReachO (hostCall host) (g n) (g (n + 1)) :=
  (invoke_div hT hH hs hS hok hd).imp_right callDivO_path_or_chain

end Silmaril.Proofs.Wasm.Abstract.HostEval
