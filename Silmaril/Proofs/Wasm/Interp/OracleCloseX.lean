module

public import Silmaril.Proofs.Wasm.Interp.OracleSimX
public import Silmaril.Wasm.Abstract.CallXT.Thms
public import Silmaril.Wasm.Abstract.XRecursion.Thms

/-!
# The closed extended call relation is a sound oracle (proofs)

`XRecursion.closedCallX` answers every call form by running its callee. On
stores whose functions are typed and whose bodies make their indirect calls
typed (`GoodStoreX`), it is a sound oracle for every `call_ref` form
(`oracleSoundX_closedX`): each answer is the end of the Core 3.0 run of its
callee from `[ref.func a, c]`, at the callee's result arity.

The proof is a least-fixpoint induction. A callee body runs under the closure
restricted to good stores and to sound answers (`EvalOX.restrict`), its
indirect calls carry their typed arities (`CallXT.evalOXT_of_evalOX_ind`), so
the forward simulation `evalOXT_goodE` applies; the callee's frame is entered by
`call_ref-func` and left by `frame_ends`.

**Scope.** As `evalOXT_goodE`: the extended store check `StoreChkE irExt` is assumed,
and code with `call_ref` is excluded (`indOkL`), pending its typed discharge.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.XRecursion

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- Stores whose functions have valid types, and whose bodies have valid instance types
and only indirect calls naming instance types (no `call_ref`). Depends only on the
store's functions. -/
def GoodStoreX (s : Store H) : Prop :=
  TyFuncs s ∧ ∀ (a : Nat) (fi : FuncInst H) (fn : Func), s.funcs[a]? = some fi →
    fi.code = .wasm fn → TyTypes fi.module ∧ indOkL fi.module (Binaryen.liftInstrs fn.body) = true

theorem goodStoreX_of_funcs {s s' : Store H} (h : s'.funcs = s.funcs) (hs : GoodStoreX s) :
    GoodStoreX s' :=
  ⟨fun a fi hfi => hs.1 a fi (h ▸ hfi), fun a fi fn hfi hc => hs.2 a fi fn (h ▸ hfi) hc⟩

/-- The closed extended call relation on good stores. -/
def closedX : Abstract.CallRel H := fun s a us out => GoodStoreX s ∧ closedCallX s a us out

/-- Restricting an oracle that keeps functions to stores satisfying an invariant of the
functions. -/
theorem EvalOX.restrict {C : Abstract.CallRel H} {I : Store H → Prop}
    (hI : ∀ {s s' : Store H}, s'.funcs = s.funcs → I s → I s')
    (hC : ∀ s a us out, C s a us out → out.1.funcs = s.funcs) {s : Store H} {f : Frame}
    {stk : List Val} {es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (h : EvalOX C s f stk es r) :
    I s → EvalOX (fun s a us out => I s ∧ C s a us out) s f stk es r := by
  have fx := fun {s f stk es r} (d : EvalOX C s f stk es r) =>
    Silmaril.Wasm.Abstract.XRecursion.evalOX_funcs hC d
  induction h with
  | nil => intro _; exact .nil
  | argsAbort _ hfl ih => exact fun hs => .argsAbort (ih hs) hfl
  | callOk hargs hfi hty hcall hvs _ ih₁ ih₂ =>
    intro hs
    have hs₁ := hI (fx hargs) hs
    exact .callOk (ih₁ hs) hfi hty ⟨hs₁, hcall⟩ hvs (ih₂ (hI (hC _ _ _ _ hcall) hs₁))
  | callTrap hargs hfi hty hcall ih => exact fun hs => .callTrap (ih hs) hfi hty ⟨hI (fx hargs) hs, hcall⟩
  | callThrow hargs hfi hty hcall ih =>
    exact fun hs => .callThrow (ih hs) hfi hty ⟨hI (fx hargs) hs, hcall⟩
  | opOk hi hargs hflat _ ih₁ ih₂ =>
    exact fun hs => .opOk hi (ih₁ hs) hflat (ih₂ (hI (Silmaril.Wasm.Abstract.XRecursion.evalFlat_funcs (H := H) hflat)
      (hI (fx hargs) hs)))
  | opStop hi _ hflat hfl ih => exact fun hs => .opStop hi (ih hs) hflat hfl
  | blockOk har hbody hvs _ ih₁ ih₂ => exact fun hs => .blockOk har (ih₁ hs) hvs (ih₂ (hI (fx hbody) hs))
  | blockBrk har _ ih => exact fun hs => .blockBrk har (ih hs)
  | blockEsc har _ hfl ih => exact fun hs => .blockEsc har (ih hs) hfl
  | loopOk har hbody _ ih₁ ih₂ => exact fun hs => .loopOk har (ih₁ hs) (ih₂ (hI (fx hbody) hs))
  | loopBack har hbody _ ih₁ ih₂ => exact fun hs => .loopBack har (ih₁ hs) (ih₂ (hI (fx hbody) hs))
  | loopBrk har _ ih => exact fun hs => .loopBrk har (ih hs)
  | loopEsc har _ hfl ih => exact fun hs => .loopEsc har (ih hs) hfl
  | ifOk hc hb har harm hvs _ ih₁ ih₂ ih₃ =>
    intro hs
    have hs₁ := hI (fx hc) hs
    exact .ifOk (ih₁ hs) hb har (ih₂ hs₁) hvs (ih₃ (hI (fx harm) hs₁))
  | ifBrk hc hb har _ ih₁ ih₂ => exact fun hs => .ifBrk (ih₁ hs) hb har (ih₂ (hI (fx hc) hs))
  | ifEsc hc hb har _ hfl ih₁ ih₂ => exact fun hs => .ifEsc (ih₁ hs) hb har (ih₂ (hI (fx hc) hs)) hfl
  | ifAbort _ hfl ih => exact fun hs => .ifAbort (ih hs) hfl
  | callIndOk hargs hres hfi hty hcall hvs _ ih₁ ih₂ =>
    intro hs
    have hs₁ := hI (fx hargs) hs
    exact .callIndOk (ih₁ hs) hres hfi hty ⟨hs₁, hcall⟩ hvs (ih₂ (hI (hC _ _ _ _ hcall) hs₁))
  | callIndRes _ hres ih => exact fun hs => .callIndRes (ih hs) hres
  | callIndStop hargs hres hfi hty hcall hfl ih =>
    exact fun hs => .callIndStop (ih hs) hres hfi hty ⟨hI (fx hargs) hs, hcall⟩ hfl
  | callRefOk hargs hfi hty hcall hvs _ ih₁ ih₂ =>
    intro hs
    have hs₁ := hI (fx hargs) hs
    exact .callRefOk (ih₁ hs) hfi hty ⟨hs₁, hcall⟩ hvs (ih₂ (hI (hC _ _ _ _ hcall) hs₁))
  | callRefNull _ ih => exact fun hs => .callRefNull (ih hs)
  | callRefStop hargs hfi hty hcall hfl ih =>
    exact fun hs => .callRefStop (ih hs) hfi hty ⟨hI (fx hargs) hs, hcall⟩ hfl
  | tail hargs hres hfi hty hcall hfl ih =>
    exact fun hs => .tail (ih hs) hres hfi hty ⟨hI (fx hargs) hs, hcall⟩ hfl
  | tailRes _ hres ih => exact fun hs => .tailRes (ih hs) hres

/-- The soundness of one answer, as `OracleSoundX` states it. -/
def SoundAns (P : Numerics.Profile) (host : HostSemantics H) (s : Store H) (a : Nat)
    (us : List Val) (out : Store H × Binaryen.Flow) : Prop :=
  ∀ (f : Frame) (fi : FuncInst H) (ps rs : List Validation.CValType) (c : Admin),
    StoreChkE irExt s.funcs → s.funcs[a]? = some fi →
    Validation.DefType.funcType? fi.type = some (ps, rs) →
    us.length = ps.length → c.IsCallRef →
    (∃ ob, (ob = none ∨ ob = some rs.length) ∧ FlowOk [rs.length] rs.length ob out.2 ∧
        FuncsGoodE irExt s.funcs out.1.funcs) ∧
      (∀ vs, out.2.retVals = some vs → Steps P host
        ⟨s, f, vals us ++ [.ref (.func a), c]⟩ ⟨out.1, f, vals (vs.take rs.length).reverse⟩) ∧
      (out.2 = .trap → Steps P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩ ⟨out.1, f, [.trap]⟩)

/-- **A callee whose body runs soundly answers soundly.** -/
theorem soundAns_of_body {C : Abstract.CallRel H} (hC : OracleSoundX P host C)
    (hCk : KeepsTy C) {s s₂ : Store H} {a : Nat} {us : List Val} {fi : FuncInst H} {fn : Func}
    {f₂ : Frame} {fl : Binaryen.Flow} (hG : GoodStoreX s) (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm fn)
    (d : EvalOX C s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body)
      (s₂, f₂, fl)) :
    SoundAns P host s a us (s₂, fl) := by
  intro f fi' ps rs c hS hfi' hty hn hcr
  rw [hfi] at hfi'; cases hfi'
  obtain ⟨hTm, hind⟩ := hG.2 a fi fn hfi hcode
  have dT := evalOXT_of_evalOX_ind hCk d hG.1 hTm hind
  obtain ⟨hA, hCore⟩ := evalOXT_goodE (P := P) (host := host) hC dT
  -- the body's check
  have hend := hS a fi fn ps rs hfi hcode hty
  obtain ⟨ob, hb, hob⟩ := endsAt_eq hend
  have hlen : (Frame.forCall fi.module us fn.locals).locals.length = ps.length + fn.locals.length :=
    forCall_length _ _ hn
  have hb' : chkE irExt s.funcs (Frame.forCall fi.module us fn.locals).module
      (Frame.forCall fi.module us fn.locals).locals.length rs.length [rs.length]
      (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
    rw [hlen]; exact hb
  obtain ⟨hok, hinv⟩ := hA hS hb'
  have hwb := hCore hS hb'
  rw [Binaryen.lowerList_liftInstrs] at hwb
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp hwb
  obtain ⟨ps', rs', hex, hpl, hrl⟩ := expand_of_funcType hty
  have hn' : us.length = ps'.length := by rw [hn, ← hpl]
  have hrl' : rs'.length = rs.length := by rw [← hrl]
  have enter : Steps P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module us fn.locals)
        [.label rs.length [] (expression fn.body)]]⟩ := by
    rw [← hrl']
    exact .single (Step.callRefFunc hcr hfi hex hn' hcode)
  have inner := Steps.frame (P := P) (host := host) (f := f) rs.length
    (Steps.label rs.length [] (by simpa [vals] using hrun))
  refine ⟨⟨ob, hob, hok, hinv.1⟩, fun vs hvs => ?_, fun htr => ?_⟩
  · have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
    have hnorm : ∀ ws, fl = .normal ws → ws.length = rs.length := by
      rintro ws rfl
      exact length_of_ends hok hob
    obtain ⟨s', res, hret, hK⟩ := frame_ends (P := P) (host := host) (f := f) he
      (funcPost_of_match (s₂ := s₂) (F := f₂) hm hvs hrs hnorm)
    obtain ⟨rfl, rfl⟩ := hK
    exact enter.trans (inner.trans hret)
  · subst htr
    have hc : c' = [.trap] := by
      rcases o with _ | _ | _ | _ | _ | _ <;> simp only [FlowMatch] at hm
      exact he
    subst hc
    have out : Steps P host ⟨s₂, f, [.frame rs.length f₂ [.label rs.length [] [.trap]]]⟩
        ⟨s₂, f, [.trap]⟩ :=
      (Relation.ReflTransGen.single (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame
    exact enter.trans (inner.trans out)

/-- **The closure on good stores is a sound oracle**, for every `call_ref` form. -/
theorem oracleSoundX_closedX : OracleSoundX P host (closedX (H := H)) := by
  let Q : Abstract.CallRel H := fun s a us out =>
    closedCallX s a us out ∧ (GoodStoreX s → SoundAns P host s a us out)
  have hQ : (closedCallX : Abstract.CallRel H) ≤ Q := by
    refine OrderHom.lfp_le _ ?_
    rintro s a us ⟨s₂, fl⟩ ⟨fi, fn, ps, rs, f₂, hfi, hcode, hty, d⟩
    refine ⟨?_, fun hG => ?_⟩
    · rw [closedCallX_fixpoint]
      exact ⟨fi, fn, ps, rs, f₂, hfi, hcode, hty, d.mono fun _ _ _ _ h => h.1⟩
    · let C' : Abstract.CallRel H := fun s a us out => GoodStoreX s ∧ Q s a us out
      have hC' : OracleSoundX P host C' :=
        fun s s₂ f a fi ps rs us fl c hS hfi hty hn hcr hcall =>
          hcall.2.2 hcall.1 f fi ps rs c hS hfi hty hn hcr
      have hkf : ∀ s a us out, Q s a us out → out.1.funcs = s.funcs :=
        fun _ _ _ _ h => closedCallX_funcs h.1
      have hCk : KeepsTy C' := fun _ _ _ _ h hs a fi hfi =>
        hs a fi (closedCallX_funcs h.2.1 ▸ hfi)
      have d' : EvalOX C' s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body)
          (s₂, f₂, fl) :=
        EvalOX.restrict (I := GoodStoreX) (fun he hs => goodStoreX_of_funcs he hs) hkf d hG
      exact soundAns_of_body hC' hCk hG hfi hcode d'
  intro s s₂ f a fi ps rs us fl c hS hfi hty hn hcr ⟨hG, hcl⟩
  exact (hQ _ _ _ _ hcl).2 hG f fi ps rs c hS hfi hty hn hcr

/-- **Closed runs on good stores are runs answered by the sound closure.** -/
theorem evalOX_closedX {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow} (h : EvalOX closedCallX s f stk es r) (hG : GoodStoreX s) :
    EvalOX (closedX (H := H)) s f stk es r :=
  EvalOX.restrict (I := GoodStoreX) (fun he hs => goodStoreX_of_funcs he hs)
    (fun _ _ _ _ h => closedCallX_funcs h) h hG

theorem keepsTy_closedX : KeepsTy (closedX (H := H)) :=
  fun _ _ _ _ h hs a fi hfi => hs a fi (closedCallX_funcs h.2 ▸ hfi)

/-- **The closed extended semantics is Core 3.0 adequate** (indirect calls, good stores):
a run of `irExt`-checked code in `EvalOX closedCallX` on a good store, in an instance with
valid types, whose indirect calls name instance types, is a Core 3.0 run. -/
theorem evalOX_closed_goodE {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow} (h : EvalOX closedCallX s f stk es r) (hG : GoodStoreX s)
    (hm : TyTypes f.module) (hx : indOkL f.module es = true) :
    ArityGoodE irExt s f stk es r ∧ CoreGoodE irExt P host s f stk es r :=
  evalOXT_goodE oracleSoundX_closedX
    (evalOXT_of_evalOX_ind keepsTy_closedX (evalOX_closedX h hG) hG.1 hm hx)

end Silmaril.Wasm.Interp
