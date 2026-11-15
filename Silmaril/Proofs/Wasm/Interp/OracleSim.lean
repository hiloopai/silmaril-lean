module

public import Silmaril.Proofs.Wasm.Interp.Control
public import Silmaril.Wasm.Abstract.Recursion.Defs

/-!
# Forward simulation of the native semantics with a call oracle (proofs)

`Abstract.EvalO C` runs native code with every call answered by an oracle `C`.
If the oracle is sound (`OracleSound`), then every `EvalO C` run of
arity-checked code is a Core 3.0 run, at every profile and host
(`evalO_good`). The proof is the induction of `wp_of_eval` and
`flowOk_of_eval`: the non-call cases reuse their case lemmas, and the call
cases use the oracle in place of the callee's derivation.

An oracle is sound when each of its answers, for a call of a function with
type `(ps, rs)` on `ps.length` arguments in an arity-checked store:

* extends the store's functions (Core `Extend`), keeping the store check and the native
  profile (`FuncsGood`);
* returns at the callee's result arity (`FlowOk [rs.length] rs.length`), so it
  never branches out and never throws;
* is matched by a Core run of `vals us ++ [ref.func a, call_ref]`, in any frame,
  to the top `rs.length` values (or to a trap).
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- **A sound call oracle**, for the store check with the extension `ext`. -/
def OracleSoundE (ext : ExtArity H) (P : Numerics.Profile) (host : HostSemantics H) (C : Abstract.CallRel H) : Prop :=
  ∀ (s s₂ : Store H) (f : Frame) (a : Nat) (fi : FuncInst H) (ps rs : List Validation.CValType)
    (us : List Val) (fl : Binaryen.Flow),
    StoreChkE ext s.funcs → s.funcs[a]? = some fi → Validation.DefType.funcType? fi.type = some (ps, rs) →
    us.length = ps.length → C s a us (s₂, fl) →
    (∃ ob, (ob = none ∨ ob = some rs.length) ∧ FlowOk [rs.length] rs.length ob fl ∧
        FuncsGoodE ext s.funcs s₂.funcs) ∧
      (∀ vs, fl.retVals = some vs → Steps P host
        ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩
        ⟨s₂, f, vals (vs.take rs.length).reverse⟩) ∧
      (fl = .trap → Steps P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩
        ⟨s₂, f, [.trap]⟩)

/-- A sound call oracle, for the native store check. -/
abbrev OracleSound (P : Numerics.Profile) (host : HostSemantics H) (C : Abstract.CallRel H) : Prop :=
  OracleSoundE noExt P host C

section OCases

set_option linter.unusedSectionVars false

variable {ext : ExtArity H} [ExtStable ext]

variable {C : Abstract.CallRel H} {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val}
  {es args : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow} {fl : Binaryen.Flow}
  {x : FuncIdx} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}

theorem module_of_func? (h : s.func? f x = some (a, fi)) : f.module.funcs[x.toNat]? = some a := by
  unfold Store.func? at h
  rcases ha : f.module.funcs[x.toNat]? with _ | a'
  · simp [ha] at h
  · rcases hb : s.funcs[a']? with _ | fi'
    · simp [ha, hb] at h
    · simp only [ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      rw [h.1]

theorem take_rev_length (hp : ps.length ≤ stk₁.length) :
    ((stk₁.take ps.length).reverse).length = ps.length := by
  simp only [List.length_reverse, List.length_take]
  omega

/-- The oracle's facts at a call. -/
theorem oracle_at (hC : OracleSoundE ext P host C) (hS : StoreChkE ext s.funcs)
    (inv1 : EvalInvE ext s f (s₁, f₁, .normal stk₁)) (hfi : s₁.func? f₁ x = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hp : ps.length ≤ stk₁.length)
    (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, fl)) (f' : Frame) :
    (∃ ob, (ob = none ∨ ob = some rs.length) ∧ FlowOk [rs.length] rs.length ob fl ∧
        FuncsGoodE ext s₁.funcs s₂.funcs) ∧
      (∀ vs, fl.retVals = some vs → Steps P host
        ⟨s₁, f', vals (stk₁.take ps.length).reverse ++ [.ref (.func a), .callRefType fi.type]⟩
        ⟨s₂, f', vals (vs.take rs.length).reverse⟩) ∧
      (fl = .trap → Steps P host
        ⟨s₁, f', vals (stk₁.take ps.length).reverse ++ [.ref (.func a), .callRefType fi.type]⟩
        ⟨s₂, f', [.trap]⟩) :=
  hC s₁ s₂ f' a fi ps rs _ fl (storeChk_inv inv1 hS) (funcs_of_func? hfi) hty
    (take_rev_length hp) hcall

theorem arityO_callOk (hC : OracleSoundE ext P host C)
    (iha : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁)) (hfi : s₁.func? f₁ x = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
    (ihk : ArityGoodE ext s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
    ArityGoodE ext s f stk (.op (.call x) args :: es) r := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, h2⟩ := arity_call_pre hS iha hfi hty hc
  obtain ⟨⟨ob, hob, hok, hfuncs⟩, -, -⟩ := oracle_at hC hS inv1 hfi hty hp hcall f₁
  have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
  have inv2 : EvalInvE ext s f (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
    ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  have hlen : (vs.take rs.length ++ stk₁.drop ps.length).length =
      stk₁.length - ps.length + rs.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have h2' : chkE ext s₂.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out := by
    rw [hlen]
    exact chk_inv inv2 h2
  obtain ⟨hok', inv3⟩ := ihk (storeChk_inv inv2 hS) h2'
  exact ⟨hok', inv2.trans inv3⟩

theorem arityO_callTrap (hC : OracleSoundE ext P host C)
    (iha : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁)) (hfi : s₁.func? f₁ x = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, .trap)) :
    ArityGoodE ext s f stk (.op (.call x) args :: es) (s₂, f₁, .trap) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, -⟩ := arity_call_pre hS iha hfi hty hc
  obtain ⟨⟨_, _, _, hfuncs⟩, -, -⟩ := oracle_at hC hS inv1 hfi hty hp hcall f₁
  exact ⟨trivial, inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩

theorem arityO_callThrow {t : Nat} (hC : OracleSoundE ext P host C)
    (iha : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁)) (hfi : s₁.func? f₁ x = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, .throw t)) :
    ArityGoodE ext s f stk (.op (.call x) args :: es) (s₂, f₁, .throw t) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, -⟩ := arity_call_pre hS iha hfi hty hc
  obtain ⟨⟨_, _, hok, _⟩, -, -⟩ := oracle_at hC hS inv1 hfi hty hp hcall f₁
  exact absurd hok id

/-- The Core run of a call answered by the oracle, in context. -/
theorem steps_oracle_call {rest : List Admin} {fin : List Admin}
    (hfi : s₁.func? f₁ x = some (a, fi))
    (hst : Steps P host
      ⟨s₁, f₁, vals (stk₁.take ps.length).reverse ++ [.ref (.func a), .callRefType fi.type]⟩
      ⟨s₂, f₁, fin⟩) :
    Steps P host ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩
      ⟨s₂, f₁, vals (stk₁.drop ps.length).reverse ++ fin ++ rest⟩ := by
  have hsplit : vals stk₁.reverse =
      vals (stk₁.drop ps.length).reverse ++ vals (stk₁.take ps.length).reverse := by
    conv_lhs => rw [← List.take_append_drop ps.length stk₁]
    simp [vals]
  have h₁ := Step.ctx (P := P) (host := host)
    ((stk₁.drop ps.length).reverse ++ (stk₁.take ps.length).reverse) rest
    (Step.call (s := s₁) (f := f₁) (module_of_func? hfi) (funcs_of_func? hfi))
  have h₂ := Steps.ctx (P := P) (host := host) (stk₁.drop ps.length).reverse rest hst
  rw [hsplit]
  simp only [vals_append, List.append_assoc, List.singleton_append] at h₁ h₂ ⊢
  exact Relation.ReflTransGen.head h₁ h₂

theorem coreO_callOk (hC : OracleSoundE ext P host C)
    (aha : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁))
    (iha : CoreGoodE ext P host s f stk args (s₁, f₁, .normal stk₁))
    (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
    (ihk : CoreGoodE ext P host s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
    CoreGoodE ext P host s f stk (.op (.call x) args :: es) r := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, h2⟩ := arity_call_pre hS aha hfi hty hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  obtain ⟨⟨ob, hob, hok, hfuncs⟩, hret, -⟩ := oracle_at hC hS inv1 hfi hty hp hcall f₁
  have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
  have inv2 : EvalInvE ext s f (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
    ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  have hlen : (vs.take rs.length ++ stk₁.drop ps.length).length =
      stk₁.length - ps.length + rs.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have h2' : chkE ext s₂.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out := by
    rw [hlen]
    exact chk_inv inv2 h2
  have hk := ihk (storeChk_inv inv2 hS) h2'
  have st := steps_oracle_call (rest := expression (Binaryen.BExpr.lowerList es)) hfi (hret vs hvs)
  rw [code_op]
  refine wp_append_normal (iha hS ha) (WP.steps st ?_)
  simpa [vals, List.reverse_append, List.append_assoc] using hk

theorem coreO_callTrap (hC : OracleSoundE ext P host C)
    (aha : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁))
    (iha : CoreGoodE ext P host s f stk args (s₁, f₁, .normal stk₁))
    (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, .trap)) :
    CoreGoodE ext P host s f stk (.op (.call x) args :: es) (s₂, f₁, .trap) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, -⟩ := arity_call_pre hS aha hfi hty hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  obtain ⟨-, -, htr⟩ := oracle_at hC hS inv1 hfi hty hp hcall f₁
  have st := steps_oracle_call (rest := expression (Binaryen.BExpr.lowerList es)) hfi (htr rfl)
  rw [code_op]
  refine wp_append_normal (iha hS ha) ⟨s₂, f₁, [.trap], .trap, st.trans ?_, rfl, rfl, rfl, trivial⟩
  simpa using steps_trap (P := P) (host := host) s₂ f₁ _ _

theorem coreO_callThrow {t : Nat} (hC : OracleSoundE ext P host C)
    (aha : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁))
    (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, .throw t)) :
    CoreGoodE ext P host s f stk (.op (.call x) args :: es) (s₂, f₁, .throw t) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, -⟩ := arity_call_pre hS aha hfi hty hc
  obtain ⟨⟨_, _, hok, _⟩, -, -⟩ := oracle_at hC hS inv1 hfi hty hp hcall f₁
  exact absurd hok id

end OCases

/-- **Forward simulation with a sound oracle**: every `EvalO C` run of
arity-checked code is a Core 3.0 run, with the arity invariants. -/
theorem evalO_goodE {ext : ExtArity H} [ExtStable ext] {C : Abstract.CallRel H}
    (hC : OracleSoundE ext P host C) {s : Store H} {f : Frame}
    {stk : List Val} {es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (h : Abstract.EvalO C s f stk es r) :
    ArityGoodE ext s f stk es r ∧ CoreGoodE ext P host s f stk es r := by
  induction h with
  | nil => exact ⟨arity_nil, core_nil⟩
  | argsAbort _ hfl iha => exact ⟨arity_argsAbort iha.1 hfl, core_argsAbort iha.2 hfl⟩
  | callOk _ hfi hty hcall hvs _ iha ihk =>
    exact ⟨arityO_callOk hC iha.1 hfi hty hcall hvs ihk.1,
      coreO_callOk hC iha.1 iha.2 hfi hty hcall hvs ihk.2⟩
  | callTrap _ hfi hty hcall iha =>
    exact ⟨arityO_callTrap hC iha.1 hfi hty hcall, coreO_callTrap hC iha.1 iha.2 hfi hty hcall⟩
  | callThrow _ hfi hty hcall iha =>
    exact ⟨arityO_callThrow hC iha.1 hfi hty hcall, coreO_callThrow hC iha.1 hfi hty hcall⟩
  | opOk hi _ hflat _ iha ihk =>
    exact ⟨arity_opOk iha.1 hflat ihk.1, core_opOk iha.1 iha.2 hi hflat ihk.2⟩
  | opStop _ _ hflat hfl iha =>
    exact ⟨arity_opStop iha.1 hflat hfl, core_opStop iha.1 iha.2 hflat hfl⟩
  | blockOk har _ hvs _ ihb ihk =>
    exact ⟨arity_blockOk har ihb.1 hvs ihk.1, core_blockOk har ihb.1 ihb.2 hvs ihk.2⟩
  | blockBrk har _ ihb =>
    exact ⟨arity_blockBrk har ihb.1, core_blockAbrupt har ihb.1 ihb.2 (.inl ⟨_, _, rfl, rfl⟩)⟩
  | blockEsc har _ hfl ihb =>
    exact ⟨arity_blockEsc har ihb.1 hfl, core_blockAbrupt har ihb.1 ihb.2 (.inr ⟨hfl, rfl⟩)⟩
  | loopOk har _ _ ihb ihk =>
    exact ⟨arity_loopOk har ihb.1 ihk.1, core_loopOk har ihb.1 ihb.2 ihk.2⟩
  | loopBack har _ _ ihb ihk =>
    exact ⟨arity_loopBack har ihb.1 ihk.1, core_loopBack har ihb.1 ihb.2 ihk.2⟩
  | loopBrk har _ ihb =>
    exact ⟨arity_loopBrk har ihb.1, core_loopAbrupt har ihb.1 ihb.2 (.inl ⟨_, _, rfl, rfl⟩)⟩
  | loopEsc har _ hfl ihb =>
    exact ⟨arity_loopEsc har ihb.1 hfl, core_loopAbrupt har ihb.1 ihb.2 (.inr ⟨hfl, rfl⟩)⟩
  | ifOk _ hb har _ hvs _ ihc iharm ihk =>
    exact ⟨arity_ifOk ihc.1 har iharm.1 hvs ihk.1,
      core_ifOk ihc.1 ihc.2 hb har iharm.1 iharm.2 hvs ihk.2⟩
  | ifBrk _ hb har _ ihc iharm =>
    exact ⟨arity_ifBrk ihc.1 har iharm.1,
      core_ifAbrupt ihc.1 ihc.2 hb har iharm.1 iharm.2 (.inl ⟨_, _, rfl, rfl⟩)⟩
  | ifEsc _ hb har _ hfl ihc iharm =>
    exact ⟨arity_ifEsc ihc.1 har iharm.1 hfl,
      core_ifAbrupt ihc.1 ihc.2 hb har iharm.1 iharm.2 (.inr ⟨hfl, rfl⟩)⟩
  | ifAbort _ hfl ihc => exact ⟨arity_ifAbort ihc.1 hfl, core_ifAbort ihc.2 hfl⟩

/-- `evalO_goodE` for the native check. -/
theorem evalO_good {C : Abstract.CallRel H} (hC : OracleSound P host C) {s : Store H} {f : Frame}
    {stk : List Val} {es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (h : Abstract.EvalO C s f stk es r) : ArityGood s f stk es r ∧ CoreGood P host s f stk es r :=
  evalO_goodE (ext := noExt) hC h

end Silmaril.Wasm.Interp
