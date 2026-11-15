module

public import Silmaril.Proofs.Wasm.Abstract.HostEval.LoggedBlock

/-!
# The logged backward simulation: calls of Wasm functions (proofs)

`back_callRef_wasm` and `back_call_wasm` for labelled runs. The callee body runs in its frame
on a strictly shorter run, with its own part of the log (`evRunN_frame_seq_split`). A body
ending at a host call is a pending host call of the callee (`PendL.desc`), the body's
completed calls resolved; a body that returns is the callee's behaviour in the closure
(`close_wasm`), whose host calls are exactly the body's part of the log; a body that traps is
the callee's trapping behaviour (`close_of_trapT`, a trapping callee read by
`Shape.Subst.intTrap`). `back_op_callL`: a
direct call as a tree, its completed call recorded with the callee's behaviour.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core (Outcome)
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {host : HostSemantics H}

/-- A resolved prefix, then an internal call whose callee traps, is a trapping resolution. -/
theorem subst_trap_of_pre {c : (wasmHShape H).ClosedMod} {u : List (HCall H)}
    {q q' : List (Call (wasmHostSig H))} (hu : Shape.SubstPre c u q)
    {g : Nat} {args : List Val} {s₀ s'' : Store H} {ans : List Val ⊕ Nat}
    (hm : (q', .trap) ∈ c g s₀ args) (rest : List (HCall H))
    (e : End (Store H) (List Val ⊕ Nat)) :
    Shape.Subst c (u ++ ⟨.inr ⟨g, (args, s₀)⟩, (ans, s'')⟩ :: rest) e (q ++ q', .trap) := by
  induction hu with
  | nil =>
    have := Shape.Subst.intTrap (sh := wasmHShape H) (c := c) (g := g) (a := args) (s := s₀)
      (ans := (ans, s'')) (rest := rest) (e := e) hm
    simpa using this
  | ext _ ih => exact .ext ih
  | int hc _ ih =>
    rw [List.append_assoc]
    exact Shape.Subst.int hc ih

/-- **A trapping body is a trapping behaviour of its function in the closure**, with exactly
its host calls. -/
theorem close_of_trapT {s : Store H} {a : Nat} {us : List Val} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {q : List (Call (wasmHostSig H))}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (h : TrapT s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body) q) :
    (q, .trap) ∈ Shape.close wasmHOpen a s us := by
  rcases h with ⟨l, s', f', d, hl⟩ | ⟨l, y, ans, s'', s', f', t, q₁, q', d, hq, hm, rfl⟩
  · exact close_wasm (fl := .trap) hf hcode hty d hl rfl
  · rw [← Shape.resolve_close]
    refine ⟨_, .inl ⟨fi, fn, ps, rs, s', f', .throw t, .throw t, _, hf, hcode, hty, d, rfl, rfl⟩, ?_⟩
    obtain ⟨g, args, s₀⟩ := y
    have e : (l ++ [(⟨.inr ⟨g, (args, s₀)⟩, (ans, s'')⟩ : OCall H)]).map OCall.lift =
        l.map OCall.lift ++ [⟨.inr ⟨g, (args, s₀)⟩, (ans, s'')⟩] := by
      rw [List.map_append]; rfl
    rw [e]
    exact subst_trap_of_pre hq hm [] _

/-- **The backward case of `call_ref` of a Wasm function**, logged (deterministic profile). -/
theorem back_callRef_wasmL {o : GrowOracle} {n : Nat} {s₁ : Store H} {f₁ : Frame}
    {stk₁ : List Val} {a : Nat} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {rest : List Admin} {c : Config H}
    {cs : List (Call (wasmHostSig H))}
    (hf : s₁.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hp : ps.length ≤ stk₁.length)
    (hrun₁ : EvRunN (profile o) host n
      ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ rest)⟩ cs c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c')
    (ihbody : ∀ m < n, ∀ cb cs₁, EvRunN (profile o) host m
        ⟨s₁, Interp.calleeFrame fi fn stk₁ ps.length,
          vals ([] : List Val).reverse ++
            expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ cs₁ cb →
      (∀ c', ¬ Step (profile o) Det.noHost cb c') →
      BackOutL host s₁ (Interp.calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body)
        cs₁ cb)
    (hret : ∀ r, EvalH host s₁ (Interp.calleeFrame fi fn stk₁ ps.length) []
        (Binaryen.liftInstrs fn.body) r →
      (∀ vs, r.2.2.retVals = some vs →
        rs.length ≤ vs.length ∧ ∀ ws, r.2.2 = .normal ws → ws.length = rs.length) ∧
      (r.2.2.retVals = none → r.2.2 = .trap)) :
    CallOutL o host n s₁ f₁ stk₁ a ps rs rest cs c := by
  obtain ⟨ps', rs', hex, hpl, hrl⟩ := Interp.expand_of_funcType hty
  -- `call_ref`, the only step, enters the frame
  have hp' : ps'.length ≤ stk₁.length := by omega
  have hs₂ : Step (profile o) Det.noHost
      ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ rest)⟩
      ⟨s₁, f₁, vals (stk₁.drop ps'.length).reverse ++
        [.frame rs'.length (Frame.forCall fi.module (stk₁.take ps'.length).reverse fn.locals)
          [.label rs'.length [] (expression fn.body)]] ++ rest⟩ := by
    rw [code_call_split stk₁ ps'.length]
    have hn : (stk₁.take ps'.length).reverse.length = ps'.length := by
      simp only [List.length_reverse, List.length_take]; omega
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := profile o) (host := Det.noHost)
      (stk₁.drop ps'.length).reverse rest
      (Step.callRefFunc (c := .callRefType fi.type) trivial hf hex hn hcode)
  obtain ⟨n₂, rfl, hrun₂⟩ :=
    evRunN_unique (fun c₁ h => callRef_wasm_step_unique hf hcode hex hp' h) hs₂ hrun₁ hend
  rw [hpl, hrl] at hrun₂
  -- the body in its frame
  obtain ⟨cb, N₁, cs₁, cs₂, rfl, hN₁, hb, hsb, hk, hx⟩ := evRunN_frame_seq_split hrun₂ hend
  have hb' : EvRunN (profile o) host N₁
      ⟨s₁, Interp.calleeFrame fi fn stk₁ ps.length,
        vals ([] : List Val).reverse ++
          expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ cs₁ cb := by
    simpa [Binaryen.lowerList_liftInstrs, vals] using hb
  rcases ihbody N₁ (by omega) cb cs₁ hb' hsb with
      ⟨⟨s₂, f₂, fl⟩, hev, ⟨oc, he, hst, hfr, hm⟩, hlog, htl⟩ | ⟨mm, hat, hpt⟩
  · right
    dsimp only at hst hfr hm hlog htl
    obtain ⟨rcs, rcf, rcc⟩ := cb
    dsimp only at hst hfr he hk
    subst hst hfr
    have hcall : hostCall host s₁ a (stk₁.take ps.length).reverse (rcs, fl) := by
      rw [hostCall_fixpoint]
      exact .inl ⟨fi, fn, ps, rs, rcf, hf, hcode, hty, hev⟩
    have hmem : ∀ vs, fl.retVals = some vs → (cs₁, .ret (.inl (vs.take rs.length).reverse) rcs) ∈
        Shape.close wasmHOpen a s₁ (stk₁.take ps.length).reverse := by
      intro vs hvs
      have hnt : fl ≠ .trap := by rintro rfl; simp [Binaryen.Flow.retVals] at hvs
      obtain ⟨l, d, hl⟩ := hlog hnt
      exact close_wasm hf hcode hty d hl (exitFlow_of_retVals hvs)
    refine ⟨rcs, fl, cs₁, cs₂, rfl, hcall, hmem, fun htr => close_of_trapT hf hcode hty (htl htr),
      ?_⟩
    obtain ⟨hvals, htrap⟩ := hret _ hev
    cases hvs : fl.retVals with
    | some vs =>
      obtain ⟨hrs, hnorm⟩ := hvals vs hvs
      obtain ⟨s', res, hret', hK⟩ := Silmaril.Wasm.Logic.Core.frame_ends (P := profile o)
        (host := Det.noHost) (f := f₁) he
        (Interp.funcPost_of_match (s₂ := rcs) (F := rcf) hm hvs hrs hnorm)
      obtain ⟨rfl, rfl⟩ := hK
      have hx := Silmaril.Wasm.Logic.Core.Steps.ctx (P := profile o)
        (host := Det.noHost) (stk₁.drop ps.length).reverse rest hret'
      obtain ⟨m, hm', h⟩ := evRunN_through_steps hx hk hend
      refine .inl ⟨vs, m, by omega, rfl, ?_⟩
      simpa [Interp.stack_after] using h
    | none =>
      have hfl := htrap hvs
      subst hfl
      have hc' : rcc = [.trap] := by
        rcases oc with _ | _ | _ | _ | _ | _ | _ <;> simp only [Interp.FlowMatch] at hm
        exact he
      subst hc'
      have hout : Steps (profile o) Det.noHost
          ⟨rcs, f₁, vals (stk₁.drop ps.length).reverse ++
            [.frame rs.length rcf [.label rs.length [] [.trap]]] ++ rest⟩
          ⟨rcs, f₁, vals (stk₁.drop ps.length).reverse ++ [.trap] ++ rest⟩ :=
        Silmaril.Wasm.Logic.Core.Steps.ctx _ rest
          ((Relation.ReflTransGen.single (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame)
      obtain ⟨m, -, h⟩ := evRunN_through_steps hout hk hend
      obtain ⟨hc, rfl⟩ := evRunN_trap_head (by simpa using h) hend
      subst hc
      exact .inr ⟨rfl, ⟨.trap, rfl, rfl, rfl, trivial⟩, rfl⟩
  · left
    obtain ⟨rfl, rfl⟩ := hx (atHost_isSome hat)
    obtain ⟨rcs, rcf, rcc⟩ := cb
    obtain ⟨l, y, q, q', hr, hq, hpl', rfl⟩ := hpt
    exact ⟨mm, atHost_frame hat, by simpa using PendL.desc hf hcode hr hq hpl'⟩

/-- **The backward case of a direct call of a Wasm function**, logged (deterministic
profile): `call x` is the only step, then `back_callRef_wasmL`. -/
theorem back_call_wasmL {o : GrowOracle} {n : Nat} {s₁ : Store H} {f₁ : Frame}
    {stk₁ : List Val} {x : FuncIdx} {a : Nat} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {rest : List Admin} {c : Config H}
    {cs : List (Call (wasmHostSig H))}
    (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hp : ps.length ≤ stk₁.length)
    (hrun : EvRunN (profile o) host n
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩ cs c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c')
    (ihbody : ∀ m < n, ∀ cb cs₁, EvRunN (profile o) host m
        ⟨s₁, Interp.calleeFrame fi fn stk₁ ps.length,
          vals ([] : List Val).reverse ++
            expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ cs₁ cb →
      (∀ c', ¬ Step (profile o) Det.noHost cb c') →
      BackOutL host s₁ (Interp.calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body)
        cs₁ cb)
    (hret : ∀ r, EvalH host s₁ (Interp.calleeFrame fi fn stk₁ ps.length) []
        (Binaryen.liftInstrs fn.body) r →
      (∀ vs, r.2.2.retVals = some vs →
        rs.length ≤ vs.length ∧ ∀ ws, r.2.2 = .normal ws → ws.length = rs.length) ∧
      (r.2.2.retVals = none → r.2.2 = .trap)) :
    CallOutL o host n s₁ f₁ stk₁ a ps rs rest cs c := by
  obtain ⟨hx, hf⟩ := Interp.func?_inv hfi
  have hs₁ : Step (profile o) Det.noHost
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩
      ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ rest)⟩ := by
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := profile o) (host := Det.noHost)
      stk₁.reverse rest (Step.call hx hf)
  obtain ⟨n₁, rfl, hrun₁⟩ :=
    evRunN_unique (fun c₁ h => call_step_unique hfi h) hs₁ hrun hend
  rcases back_callRef_wasmL hf hcode hty hp hrun₁ hend
      (fun m hm cb cs₁ h hs => ihbody m (by omega) cb cs₁ h hs) hret with hp' |
    ⟨s₂, fl, q, cs', hcs, hcall, hmem, hmt, ⟨vs, m, hm, hvs, hk⟩ | htr⟩
  · exact .inl hp'
  · exact .inr ⟨s₂, fl, q, cs', hcs, hcall, hmem, hmt, .inl ⟨vs, m, by omega, hvs, hk⟩⟩
  · exact .inr ⟨s₂, fl, q, cs', hcs, hcall, hmem, hmt, .inr htr⟩

/-- **A direct call as a tree**, for any callee, logged. -/
theorem back_op_callL {o : GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {x : FuncIdx} {args es : List Binaryen.BExpr} {c : Config H}
    {cs : List (Call (wasmHostSig H))}
    (hrun : EvRunN (profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.op (.call x) args :: es))⟩
        cs c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c')
    (ihargs : ∀ m ≤ n, ∀ c₁ cs₁, EvRunN (profile o) host m
        ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)⟩ cs₁ c₁ →
      (∀ c', ¬ Step (profile o) Det.noHost c₁ c') → BackOutL host s f stk args cs₁ c₁)
    (hcase : ∀ s₁ f₁ stk₁ m cs', m ≤ n → EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      EvRunN (profile o) host m
        ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) ::
          expression (Binaryen.BExpr.lowerList es)⟩ cs' c →
      ∃ (a : Nat) (fi : FuncInst H) (ps rs : List Validation.CValType),
        s₁.func? f₁ x = some (a, fi) ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        CallOutL o host m s₁ f₁ stk₁ a ps rs (expression (Binaryen.BExpr.lowerList es)) cs' c)
    (ihes : ∀ (s₁ : Store H) (f₁ : Frame) (stk₁ : List Val) (a : Nat) (fi : FuncInst H)
      (ps rs : List Validation.CValType) (s₂ : Store H) (fl : Binaryen.Flow) (vs : List Val)
      (m : Nat) cs', m ≤ n → EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      s₁.func? f₁ x = some (a, fi) → Validation.DefType.funcType? fi.type = some (ps, rs) →
      hostCall host s₁ a (stk₁.take ps.length).reverse (s₂, fl) → fl.retVals = some vs →
      EvRunN (profile o) host m
        ⟨s₂, f₁, vals (vs.take rs.length ++ stk₁.drop ps.length).reverse ++
          expression (Binaryen.BExpr.lowerList es)⟩ cs' c →
      BackOutL host s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es cs' c) :
    BackOutL host s f stk (.op (.call x) args :: es) cs c := by
  refine back_op_argsL hrun hend ihargs
    fun s₁ f₁ stk₁ m l₁ cs₁ cs₂ hm hev d₁ hl₁ hcs hrun₁ => ?_
  subst hcs
  obtain ⟨a, fi, ps, rs, hfi, hty, hco⟩ := hcase s₁ f₁ stk₁ m cs₂ hm hev hrun₁
  rcases hco with ⟨mm, hat, hpl⟩ |
      ⟨s₂, fl, q, cs', rfl, hcall, hmem, hmt, ⟨vs, m', hm', hvs, hk⟩ | ⟨rfl, hends, rfl⟩⟩
  · exact .inr ⟨mm, hat, pendT_call d₁ hl₁ hfi hty hpl⟩
  · have hz := res_single (hmem vs hvs)
    have d₁' : EvalL s f stk args l₁ (s₁, f₁, .normal stk₁) := d₁
    rcases ihes s₁ f₁ stk₁ a fi ps rs s₂ fl vs m' cs' (by omega) hev hfi hty hcall hvs hk with
        ⟨r, hev', hr, hlog', htl'⟩ | ⟨mm, hat, hpt⟩
    · refine .inl ⟨r, .callOk hev hfi hty hcall hvs hev', hr, fun hnt => ?_, fun htr => ?_⟩
      · obtain ⟨l₂, d₂, hl₂⟩ := hlog' hnt
        refine ⟨_, EvalL.callRet (ws := (vs.take rs.length).reverse) (s₂ := s₂) d₁' hfi hty
          (by rw [List.reverse_reverse]; exact d₂), ?_⟩
        have := res_append hl₁ (res_append hz hl₂)
        simpa [List.append_assoc] using this
      · have := trapT_lift (l₀ := l₁ ++ [OCall.mk a (stk₁.take ps.length).reverse s₁
            (.inl (vs.take rs.length).reverse) s₂])
          (fun l r d _ => by
            have := EvalL.callRet (ws := (vs.take rs.length).reverse) (s₂ := s₂) d₁' hfi hty
              (by rw [List.reverse_reverse]; exact d)
            simpa [List.append_assoc] using this)
          (res_append hl₁ hz) (htl' htr)
        simpa [List.append_assoc] using this
    · have := pendT_lift (l₀ := l₁ ++ [OCall.mk a (stk₁.take ps.length).reverse s₁
          (.inl (vs.take rs.length).reverse) s₂])
        (fun l y h => by
          have := ReachL.callK (ws := (vs.take rs.length).reverse) (s₂ := s₂) d₁' hfi hty
            (by rw [List.reverse_reverse]; exact h)
          simpa [List.append_assoc] using this)
        (res_append hl₁ hz) hpt
      exact .inr ⟨mm, hat, by simpa [List.append_assoc] using this⟩
  · exact .inl ⟨_, .callTrap hev hfi hty hcall, hends, fun h => (h rfl).elim,
      fun _ => by simpa using trapT_call d₁ hl₁ hfi hty (hmt rfl)⟩

end Silmaril.Proofs.Wasm.Abstract.HostEval
