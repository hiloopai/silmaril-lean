module

public import Silmaril.Proofs.Wasm.Interp.TailX
public import Silmaril.Proofs.Wasm.Interp.OracleCloseX

/-!
# The closure as a sound oracle with direct tail calls (proofs)

`OracleCloseX.oracleSoundX_closedX` closes the oracle for `irExt`. This module does the same for
the tail checker `tExt` (`return_call x` admitted): on good stores, `XRecursion.closedCallX` is a
sound oracle for `tExt` (`oracleSoundT_closedX`), by the same least-fixpoint induction. A callee
body now runs under the tail-aware postcondition (`evalOXT_goodT`): it ends matched, or at a
pending tail call; the frame is left by `frame_ends` with `funcPost_of_tailRun` (a returning
tail callee) or by `frame_tail_exit` (a trapping one), as in `wp_call_okT`/`wp_call_trapT`.

**Scope.** As `TailX`: `return_call_indirect`/`return_call_ref` are rejected by `tExt` (null
tails), and callee bodies have no `call_ref` (`GoodStoreX`).
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.XRecursion

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- The soundness of one answer, as `OracleSoundT` states it. -/
def SoundAnsT (P : Numerics.Profile) (host : HostSemantics H) (s : Store H) (a : Nat)
    (us : List Val) (out : Store H × Binaryen.Flow) : Prop :=
  ∀ (f : Frame) (fi : FuncInst H) (ps rs : List Validation.CValType) (c : Admin),
    StoreChkE tExt s.funcs → s.funcs[a]? = some fi →
    Validation.DefType.funcType? fi.type = some (ps, rs) →
    us.length = ps.length → c.IsCallRef →
    (∃ ob, (ob = none ∨ ob = some rs.length) ∧ FlowOk [rs.length] rs.length ob out.2 ∧
        FuncsGoodE tExt s.funcs out.1.funcs) ∧
      (∀ vs, out.2.retVals = some vs → Steps P host
        ⟨s, f, vals us ++ [.ref (.func a), c]⟩ ⟨out.1, f, vals (vs.take rs.length).reverse⟩) ∧
      (out.2 = .trap → Steps P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩ ⟨out.1, f, [.trap]⟩)

/-- **A callee whose body has a sound `EvalOXT` run answers soundly**, the body possibly
ending in a direct tail call. -/
theorem soundAnsT_of_bodyT {C : Abstract.CallRel H} (hC : OracleSoundT P host C)
    {s s₂ : Store H} {a : Nat} {us : List Val} {fi : FuncInst H} {fn : Func}
    {f₂ : Frame} {fl : Binaryen.Flow} (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm fn)
    (dT : EvalOXT C s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body)
      (s₂, f₂, fl)) :
    SoundAnsT P host s a us (s₂, fl) := by
  intro f fi' ps rs c hS hfi' hty hn hcr
  rw [hfi] at hfi'; cases hfi'
  obtain ⟨hA, hCore⟩ := evalOXT_goodT (P := P) (host := host) hC dT
  have hend := hS a fi fn ps rs hfi hcode hty
  obtain ⟨ob, hb, hob⟩ := endsAt_eq hend
  have hlen : (Frame.forCall fi.module us fn.locals).locals.length = ps.length + fn.locals.length :=
    forCall_length _ _ hn
  have hb' : chkE tExt s.funcs (Frame.forCall fi.module us fn.locals).module
      (Frame.forCall fi.module us fn.locals).locals.length rs.length [rs.length]
      (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
    rw [hlen]; exact hb
  obtain ⟨hok, hinv⟩ := hA hS hb'
  have hwb := hCore hS hb'
  rw [Binaryen.lowerList_liftInstrs] at hwb
  obtain ⟨ps', rs', hex, hpl, hrl⟩ := expand_of_funcType hty
  have hn' : us.length = ps'.length := by rw [hn, ← hpl]
  have hrl' : rs'.length = rs.length := by rw [← hrl]
  have enter : Steps P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module us fn.locals)
        [.label rs.length [] (expression fn.body)]]⟩ := by
    rw [← hrl']
    exact .single (Step.callRefFunc hcr hfi hex hn' hcode)
  refine ⟨⟨ob, hob, hok, hinv.1⟩, ?_, ?_⟩ <;>
  rcases run_of_wpT hwb with ⟨c', o, hrun, he, hm⟩ | ⟨s', f', vs', a', c', rest₀, hrun, hT⟩ |
      ⟨vs', c', rest₀, hrun, hnc, hntr⟩
  · -- matched, returning
    intro vs hvs
    have inner := Steps.frame (P := P) (host := host) (f := f) rs.length
      (Steps.label rs.length [] (by simpa [vals] using hrun))
    have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
    have hnorm : ∀ ws, fl = .normal ws → ws.length = rs.length := by
      rintro ws rfl
      exact length_of_ends hok hob
    obtain ⟨s', res, hret, hK⟩ := frame_ends (P := P) (host := host) (f := f) he
      (funcPost_of_match (s₂ := s₂) (F := f₂) hm hvs hrs hnorm)
    obtain ⟨rfl, rfl⟩ := hK
    exact enter.trans (inner.trans hret)
  · -- a pending tail, returning
    intro vs hvs
    rcases tailRun_flow hT with ⟨ws, hw⟩ | hw <;> dsimp only at hw <;> subst hw
    · simp only [Binaryen.Flow.retVals, Option.some.injEq] at hvs
      subst hvs
      have inner := Steps.frame (P := P) (host := host) (f := f) rs.length
        (Steps.label rs.length [] (show Steps P host
          ⟨s, Frame.forCall fi.module us fn.locals, expression fn.body⟩
          ⟨s', f', vals vs' ++ .ref (.func a') :: c' :: rest₀⟩ from by simpa [vals] using hrun))
      have hf' : f' = f₂ := hT.2.1
      subst hf'
      have he : Outcome.Ends (.tail vs' a' c') (vals vs' ++ .ref (.func a') :: c' :: rest₀) :=
        ⟨hT.1, rest₀, rfl⟩
      obtain ⟨s'', res, hret, hK⟩ := frame_ends (P := P) (host := host) (f := f) (n := rs.length)
        he (funcPost_of_tailRun hT)
      obtain ⟨rfl, rfl⟩ := hK
      exact enter.trans (inner.trans hret)
    · simp [Binaryen.Flow.retVals] at hvs
  · -- a pending null tail traps, so does not return
    intro vs hvs
    dsimp only at hntr
    subst hntr
    simp [Binaryen.Flow.retVals] at hvs
  · -- matched, trapping
    intro htr
    subst htr
    have inner := Steps.frame (P := P) (host := host) (f := f) rs.length
      (Steps.label rs.length [] (by simpa [vals] using hrun))
    have hc : c' = [.trap] := by
      rcases o with _ | _ | _ | _ | _ | _ <;> simp only [FlowMatch] at hm
      exact he
    subst hc
    have out : Steps P host ⟨s₂, f, [.frame rs.length f₂ [.label rs.length [] [.trap]]]⟩
        ⟨s₂, f, [.trap]⟩ :=
      (Relation.ReflTransGen.single (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame
    exact enter.trans (inner.trans out)
  · -- a pending tail, trapping
    intro htr
    subst htr
    obtain ⟨hc, hf', vs₁, args, fn', ps'', rs'', rfl, hfn, hex', hlen', hg⟩ := hT
    dsimp only at hf'
    subst hf'
    rcases hg f with ⟨ws, hw, -⟩ | ⟨-, htrs⟩
    · cases hw
    have inner := Steps.frame (P := P) (host := host) (f := f) rs.length
      (Steps.label rs.length [] (show Steps P host
        ⟨s, Frame.forCall fi.module us fn.locals, expression fn.body⟩
        ⟨s', f', vals (vs₁ ++ args) ++ .ref (.func a') :: c' :: rest₀⟩ from by simpa [vals] using hrun))
    exact enter.trans (inner.trans ((frame_tail_exit (f := f) (k := rs.length) (F := f')
      (vs₁ := vs₁) (rest := rest₀) hc hfn hex' hlen').trans htrs))
  · -- a pending null tail traps at the frame
    intro _
    have inner := Steps.frame (P := P) (host := host) (f := f) rs.length
      (Steps.label rs.length [] (show Steps P host
        ⟨s, Frame.forCall fi.module us fn.locals, expression fn.body⟩
        ⟨s₂, f₂, vals vs' ++ .ref .null :: c' :: rest₀⟩ from by simpa [vals] using hrun))
    exact enter.trans (inner.trans (frame_tailNull (P := P) (host := host) (s := s₂) (f := f)
      (n := rs.length) (F := f₂) (vs := vs') (rest := rest₀) hnc))

/-- **The closure on good stores is a sound oracle for `tExt`**, callee bodies possibly ending
in direct tail calls. -/
theorem oracleSoundT_closedX : OracleSoundT P host (closedX (H := H)) := by
  let Q : Abstract.CallRel H := fun s a us out =>
    closedCallX s a us out ∧ (GoodStoreX s → SoundAnsT P host s a us out)
  have hQ : (closedCallX : Abstract.CallRel H) ≤ Q := by
    refine OrderHom.lfp_le _ ?_
    rintro s a us ⟨s₂, fl⟩ ⟨fi, fn, ps, rs, f₂, hfi, hcode, hty, d⟩
    refine ⟨?_, fun hG => ?_⟩
    · rw [closedCallX_fixpoint]
      exact ⟨fi, fn, ps, rs, f₂, hfi, hcode, hty, d.mono fun _ _ _ _ h => h.1⟩
    · let C' : Abstract.CallRel H := fun s a us out => GoodStoreX s ∧ Q s a us out
      have hC' : OracleSoundT P host C' :=
        fun s s₂ f a fi ps rs us fl c hS hfi hty hn hcr hcall =>
          hcall.2.2 hcall.1 f fi ps rs c hS hfi hty hn hcr
      have hkf : ∀ s a us out, Q s a us out → out.1.funcs = s.funcs :=
        fun _ _ _ _ h => closedCallX_funcs h.1
      have hCk : KeepsTy C' := fun _ _ _ _ h hs a fi hfi =>
        hs a fi (closedCallX_funcs h.2.1 ▸ hfi)
      have d' : EvalOX C' s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body)
          (s₂, f₂, fl) :=
        EvalOX.restrict (I := GoodStoreX) (fun he hs => goodStoreX_of_funcs he hs) hkf d hG
      obtain ⟨hTm, hind⟩ := hG.2 a fi fn hfi hcode
      exact soundAnsT_of_bodyT hC' hfi hcode (evalOXT_of_evalOX_ind hCk d' hG.1 hTm hind)
  intro s s₂ f a fi ps rs us fl c hS hfi hty hn hcr ⟨hG, hcl⟩
  exact (hQ _ _ _ _ hcl).2 hG f fi ps rs c hS hfi hty hn hcr

/-- **Closed extended runs with direct tail calls are Core 3.0 runs** (good stores,
`tExt`-checked code, tail-aware postcondition). -/
theorem evalOX_closed_goodT {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow} (h : EvalOX closedCallX s f stk es r) (hG : GoodStoreX s)
    (hm : TyTypes f.module) (hx : indOkL f.module es = true) :
    ArityGoodE tExt s f stk es r ∧ CoreGoodT tExt P host s f stk es r :=
  evalOXT_goodT oracleSoundT_closedX
    (evalOXT_of_evalOX_ind keepsTy_closedX (evalOX_closedX h hG) hG.1 hm hx)

end Silmaril.Wasm.Interp
