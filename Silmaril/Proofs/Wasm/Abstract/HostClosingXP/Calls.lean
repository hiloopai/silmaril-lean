module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Cases

/-!
# The call cases of the logged canonical simulation (proofs)

A call (`call`, `call_indirect`, `call_ref`) answered by a logged run of its callee in the
caller's frame (`CalleeRun`: from the callee reference and a `call_ref` form on top of the
arguments, to the answer's code, `ansCode`), with the arity facts of the answer from the
canonical host oracle (`hostP`), as in `PendSim`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallXT (typeArity)
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- The code of an answer: returned values, or a thrown exception. -/
def ansCode : List Val ⊕ Nat → List Admin
  | .inl ws => vals ws
  | .inr t => throwing t

/-- **A logged run of a callee in any caller frame**, from any `call_ref` form on the callee
reference above the arguments, to the code of its answer `b`, at the store `s'`, with the host
events `qc`. -/
def CalleeRun (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (s : Store H)
    (a : Nat) (us : List Val) (qc : List (Call (wasmHostSig H))) (s' : Store H)
    (b : List Val ⊕ Nat) : Prop :=
  ∀ (f : Frame) (c : Admin), c.IsCallRef →
    EvRun P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩ qc ⟨s', f, ansCode b⟩

section Calls

variable {tags : List TagInst} {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ : List Val}
  {es args : List Binaryen.BExpr} {i : Instr} {r : Store H × Frame × POut}
  {q₁ q₂ qc : List (Call (wasmHostSig H))} {x : FuncIdx} {a fa : Nat} {fi : FuncInst H}
  {ps rs : List Validation.CValType} {y : TypeIdx} {Q : Post H}

/-- **The Core run of a direct call answered by a logged callee run**, in context. -/
theorem evRun_call {rest fin : List Admin} (hfi : s₁.func? f₁ x = some (a, fi))
    (hst : EvRun P host
      ⟨s₁, f₁, vals (stk₁.take ps.length).reverse ++ [.ref (.func a), .callRefType fi.type]⟩ qc
      ⟨s₂, f₁, fin⟩) :
    EvRun P host ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩ qc
      ⟨s₂, f₁, vals (stk₁.drop ps.length).reverse ++ fin ++ rest⟩ := by
  have hsplit : vals stk₁.reverse =
      vals (stk₁.drop ps.length).reverse ++ vals (stk₁.take ps.length).reverse := by
    conv_lhs => rw [← List.take_append_drop ps.length stk₁]
    simp [vals]
  have h₁ := Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := NH)
    ((stk₁.drop ps.length).reverse ++ (stk₁.take ps.length).reverse) rest
    (Step.call (s := s₁) (f := f₁) (module_of_func? hfi) (funcs_of_func? hfi))
  have h₂ := evRun_ctx (stk₁.drop ps.length).reverse rest hst
  rw [hsplit]
  simp only [vals_append, List.append_assoc, List.singleton_append] at h₁ h₂ ⊢
  exact .silent (.inl h₁) h₂

/-- **The Core run of a `call_ref` form answered by a logged callee run**, in context. -/
theorem evRun_callRef {rest fin : List Admin} {c : Admin}
    (hst : EvRun P host ⟨s₁, f₁, vals (stk₁.take ps.length).reverse ++ [.ref (.func fa), c]⟩ qc
      ⟨s₂, f₁, fin⟩) :
    EvRun P host ⟨s₁, f₁, vals stk₁.reverse ++ [.ref (.func fa), c] ++ rest⟩ qc
      ⟨s₂, f₁, vals (stk₁.drop ps.length).reverse ++ fin ++ rest⟩ := by
  have hsplit : vals stk₁.reverse =
      vals (stk₁.drop ps.length).reverse ++ vals (stk₁.take ps.length).reverse := by
    conv_lhs => rw [← List.take_append_drop ps.length stk₁]
    simp [vals]
  have h₂ := evRun_ctx (stk₁.drop ps.length).reverse rest hst
  rw [hsplit]
  simpa only [List.append_assoc] using h₂

/-- An answer's code, in context, as a final form or the continuation's stack. -/
theorem wpl_ans_throw {t : Nat} {rest : List Admin} {pre : List Val} :
    WPL P host ⟨s₂, f₁, vals pre ++ ansCode (.inr t) ++ rest⟩ []
      (MatchP (s₂, f₁, .flow (.throw t))) :=
  wpl_matchP (wpl_of_wp (wp_throwing ⟨rfl, rfl, rfl⟩))

/-- **A call answered by returned values.** -/
theorem coreLP_callRet (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    (aha : ArityGoodE (ehExt tags) s f stk args (s₁, f₁, .normal stk₁) true)
    (iha : CoreLP tags P host s f stk args (s₁, f₁, .flow (.normal stk₁)) q₁)
    (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    {bfl : Binaryen.Flow} {w ws : List Val}
    (hcall : hostP tags host s₁ a (stk₁.take ps.length).reverse (s₂, bfl))
    (hvs : bfl.retVals = some w) (hws : ws.reverse = w.take rs.length)
    (hrun : StoreChkE (ehExt tags) s₁.funcs → ((stk₁.take ps.length).reverse).length = ps.length →
      CalleeRun P host s₁ a (stk₁.take ps.length).reverse qc s₂ (.inl ws))
    (ihk : CoreLQ tags P host s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es Q q₂) :
    CoreLQ tags P host s f stk (.op (.call x) args :: es) Q (q₁ ++ (qc ++ q₂)) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, h2⟩ := arity_call_pre hS aha hfi hty hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  obtain ⟨⟨ob, hob, hok, hfuncs⟩, -, -⟩ :=
    oracle_at (oracleSoundTE_hostP (P := P) hH hE).soundE hS inv1 hfi hty hp hcall f₁
  have hrs : rs.length ≤ w.length := retVals_length hok hob hvs
  have inv2 : EvalInvE (ehExt tags) s f (s₂, f₁, .normal (ws.reverse ++ stk₁.drop ps.length)) :=
    ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  have hlen : (ws.reverse ++ stk₁.drop ps.length).length =
      stk₁.length - ps.length + rs.length := by
    rw [hws]
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have h2' : chkE (ehExt tags) s₂.funcs f₁.module f₁.locals.length ret labels
      (some (ws.reverse ++ stk₁.drop ps.length).length) es = some out := by
    rw [hlen]
    exact chk_inv inv2 h2
  have hk := ihk (storeChk_inv inv2 hS) h2'
  have st := evRun_call (rest := expression (Binaryen.BExpr.lowerList es)) hfi
    (hrun (storeChk_inv inv1 hS) (take_rev_length hp) f₁ (.callRefType fi.type) trivial)
  rw [code_op]
  refine wpl_append_normal (iha hS ha) (wpl_evRun st ?_)
  simpa [ansCode, vals, List.reverse_append, List.append_assoc] using hk

/-- **A call answered by an exception**, raised at the call. -/
theorem coreLP_callThrow {t : Nat}
    (aha : ArityGoodE (ehExt tags) s f stk args (s₁, f₁, .normal stk₁) true)
    (iha : CoreLP tags P host s f stk args (s₁, f₁, .flow (.normal stk₁)) q₁)
    (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hrun : StoreChkE (ehExt tags) s₁.funcs → ((stk₁.take ps.length).reverse).length = ps.length →
      CalleeRun P host s₁ a (stk₁.take ps.length).reverse qc s₂ (.inr t)) :
    CoreLP tags P host s f stk (.op (.call x) args :: es) (s₂, f₁, .flow (.throw t)) (q₁ ++ qc) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, -⟩ := arity_call_pre hS aha hfi hty hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  have st := evRun_call (rest := expression (Binaryen.BExpr.lowerList es)) hfi
    (hrun (storeChk_inv inv1 hS) (take_rev_length hp) f₁ (.callRefType fi.type) trivial)
  rw [code_op, show q₁ ++ qc = q₁ ++ (qc ++ []) by simp]
  exact wpl_append_normal (iha hS ha) (wpl_evRun st wpl_ans_throw)

/-- **An indirect or reference call answered by returned values.** -/
theorem coreLP_irRet {top : Val} (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (aha : ArityGoodE (ehExt tags) s f stk args (s₁, f₁, .normal (top :: stk₁)) true)
    (iha : CoreLP tags P host s f stk args (s₁, f₁, .flow (.normal (top :: stk₁))) q₁)
    (hpre : Steps P NH ⟨s₁, f₁, vals [top] ++ [.plain i]⟩
      ⟨s₁, f₁, [.ref (.func fa), .plain (.callRef y)]⟩)
    (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    {bfl : Binaryen.Flow} {w ws : List Val}
    (hcall : hostP tags host s₁ fa (stk₁.take ps.length).reverse (s₂, bfl))
    (hvs : bfl.retVals = some w) (hws : ws.reverse = w.take rs.length)
    (hrun : StoreChkE (ehExt tags) s₁.funcs → ((stk₁.take ps.length).reverse).length = ps.length →
      CalleeRun P host s₁ fa (stk₁.take ps.length).reverse qc s₂ (.inl ws))
    (ihk : CoreLQ tags P host s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es Q q₂) :
    CoreLQ tags P host s f stk (.op i args :: es) Q (q₁ ++ (qc ++ q₂)) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, h2⟩ := arity_ir_preP hS aha hi hy hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  obtain ⟨⟨ob, hob, hok, hfuncs⟩, -, -⟩ := (oracleSoundTE_hostP (P := P) hH hE) s₁ s₂ f₁ fa fi
    ps rs _ bfl (.plain (.callRef y)) (storeChk_inv inv1 hS) hfi hty (take_rev_length hp) trivial
    hcall
  have hrs : rs.length ≤ w.length := retVals_length hok hob hvs
  have inv2 : EvalInvE (ehExt tags) s f
      (s₂, f₁, .normal (ws.reverse ++ stk₁.drop ps.length)) :=
    ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  have hlen : (ws.reverse ++ stk₁.drop ps.length).length =
      stk₁.length - ps.length + rs.length := by
    rw [hws]
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have h2' : chkE (ehExt tags) s₂.funcs f₁.module f₁.locals.length ret labels
      (some (ws.reverse ++ stk₁.drop ps.length).length) es = some out := by
    rw [hlen]
    exact chk_inv inv2 h2
  have hk := ihk (storeChk_inv inv2 hS) h2'
  let E := expression (Binaryen.BExpr.lowerList es)
  have st₁ := Steps.ctx (P := P) (host := NH) stk₁.reverse E hpre
  have st₂ := evRun_callRef (rest := E)
    (hrun (storeChk_inv inv1 hS) (take_rev_length hp) f₁ (.plain (.callRef y)) trivial)
  have e : vals (top :: stk₁).reverse ++ .plain i :: E =
      vals stk₁.reverse ++ (vals [top] ++ [.plain i]) ++ E := by simp [vals]
  rw [code_op]
  refine wpl_append_normal (iha hS ha) ?_
  rw [e]
  refine wpl_free st₁ (wpl_evRun st₂ ?_)
  simpa [ansCode, vals, List.reverse_append, List.append_assoc] using hk

/-- **An indirect or reference call answered by an exception.** -/
theorem coreLP_irThrow {top : Val} {t : Nat}
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (aha : ArityGoodE (ehExt tags) s f stk args (s₁, f₁, .normal (top :: stk₁)) true)
    (iha : CoreLP tags P host s f stk args (s₁, f₁, .flow (.normal (top :: stk₁))) q₁)
    (hpre : Steps P NH ⟨s₁, f₁, vals [top] ++ [.plain i]⟩
      ⟨s₁, f₁, [.ref (.func fa), .plain (.callRef y)]⟩)
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (hrun : StoreChkE (ehExt tags) s₁.funcs → ((stk₁.take ps.length).reverse).length = ps.length →
      CalleeRun P host s₁ fa (stk₁.take ps.length).reverse qc s₂ (.inr t)) :
    CoreLP tags P host s f stk (.op i args :: es) (s₂, f₁, .flow (.throw t)) (q₁ ++ qc) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, -⟩ := arity_ir_preP hS aha hi hy hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  let E := expression (Binaryen.BExpr.lowerList es)
  have st₁ := Steps.ctx (P := P) (host := NH) stk₁.reverse E hpre
  have st₂ := evRun_callRef (rest := E)
    (hrun (storeChk_inv inv1 hS) (take_rev_length hp) f₁ (.plain (.callRef y)) trivial)
  have e : vals (top :: stk₁).reverse ++ .plain i :: E =
      vals stk₁.reverse ++ (vals [top] ++ [.plain i]) ++ E := by simp [vals]
  rw [code_op, show q₁ ++ qc = q₁ ++ (qc ++ []) by simp]
  refine wpl_append_normal (iha hS ha) ?_
  rw [e]
  exact wpl_free st₁ (wpl_evRun st₂ wpl_ans_throw)

end Calls

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
