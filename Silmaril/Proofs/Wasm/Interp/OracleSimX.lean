module

public import Silmaril.Proofs.Wasm.Interp.OracleSim
public import Silmaril.Wasm.Abstract.CallXT.Defs
public import Silmaril.Wasm.Abstract.CallRes.Thms

/-!
# Forward simulation of the indirect and reference calls (proofs)

`Abstract.CallXT.EvalOXT C` is `EvalOX C` with each indirect or reference
call's callee arity recorded as the annotated type's. This module proves that
its runs of code checked by the extension `irExt` are Core 3.0 runs
(`evalOXT_goodE`), with the arity invariants, at every profile and host, given
a sound oracle (`OracleSoundX`).

**Scope.** The invariants assume the extended store check
`StoreChkE irExt s.funcs`: the store's functions pass `chkE irExt`, so they may
contain `call_indirect`/`call_ref` too (a natively checked store qualifies,
`storeChkE_of_storeChk`).
`irExt` describes `call_indirect x y` and `call_ref y` by the type
`y` (`.fall (p + 1) q`). It does not describe the tail calls, so `chkE irExt`
rejects them: for code with a tail call nothing is claimed here. A tail call
replaces the caller's frame (`return_call_ref-frame-addr`), so its adequacy is
a frame-level statement, not a body-level `Match`.

`OracleSoundX` is `OracleSound` with the Core run of the callee stated for
every call form `c` of `call_ref` (`Admin.IsCallRef`): `call_ref y` and the
`call_ref` of a defined type reach the same callee configuration.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- The arity checker extension for `call_indirect x y` and `call_ref y`: they pop
the index or reference and the parameters of `y`, and push its results. The
tail calls are not described. -/
def irExt : ExtArity H := fun _ mi i =>
  match i with
  | .callIndirect _ y | .callRef y => (typeArity mi y).map fun p => .fall (p.1 + 1) p.2
  | _ => none

instance : ExtStable (irExt (H := H)) := ⟨fun _ h => h⟩

/-- **A sound call oracle, for every `call_ref` form.** -/
def OracleSoundX (P : Numerics.Profile) (host : HostSemantics H) (C : Abstract.CallRel H) : Prop :=
  ∀ (s s₂ : Store H) (f : Frame) (a : Nat) (fi : FuncInst H) (ps rs : List Validation.CValType)
    (us : List Val) (fl : Binaryen.Flow) (c : Admin),
    StoreChkE irExt s.funcs → s.funcs[a]? = some fi → Validation.DefType.funcType? fi.type = some (ps, rs) →
    us.length = ps.length → c.IsCallRef → C s a us (s₂, fl) →
    (∃ ob, (ob = none ∨ ob = some rs.length) ∧ FlowOk [rs.length] rs.length ob fl ∧
        FuncsGoodE irExt s.funcs s₂.funcs) ∧
      (∀ vs, fl.retVals = some vs → Steps P host
        ⟨s, f, vals us ++ [.ref (.func a), c]⟩ ⟨s₂, f, vals (vs.take rs.length).reverse⟩) ∧
      (fl = .trap → Steps P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩ ⟨s₂, f, [.trap]⟩)

theorem OracleSoundX.sound {C : Abstract.CallRel H} (hC : OracleSoundX P host C) :
    OracleSoundE irExt P host C :=
  fun s s₂ f a fi ps rs us fl hS hfi hty hn hcall =>
    hC s s₂ f a fi ps rs us fl (.callRefType fi.type) hS hfi hty hn trivial hcall

section XCases

set_option linter.unusedSectionVars false

variable {C : Abstract.CallRel H} {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val}
  {es args : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow} {fl : Binaryen.Flow}
  {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {y : TypeIdx}

/-- The check of an extended call form whose type has the callee's counts. -/
theorem flatChk_ir {i : Instr} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {h : Nat} {o : Option Nat}
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y) (hy : typeArity mi y = some (ps.length, rs.length))
    (hc : flatChkE irExt F mi nl ret labels h i = some o) :
    ps.length + 1 ≤ h ∧ o = some (h - (ps.length + 1) + rs.length) := by
  rcases hi with ⟨x, rfl⟩ | rfl <;>
  · simp only [flatChkE, irExt, hy, Option.map_some, extStep] at hc
    split at hc
    · exact ⟨by assumption, (Option.some.inj hc).symm⟩
    · cases hc

/-- The pre-call facts of an indirect or reference call. -/
theorem arity_ir_pre {i : Instr} {top : Val} {labels : List Nat} {ret : Nat} {out : Option Nat}
    (hS : StoreChkE irExt s.funcs) (iha : ArityGoodE irExt s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (hc : chkE irExt s.funcs f.module f.locals.length ret labels (some stk.length)
      (.op i args :: es) = some out) :
    EvalInvE irExt s f (s₁, f₁, .normal (top :: stk₁)) ∧ ps.length ≤ stk₁.length ∧
      chkE irExt s.funcs f.module f.locals.length ret labels
        (some (stk₁.length - ps.length + rs.length)) es = some out := by
  obtain ⟨o, h1, h2⟩ := chk_consE.mp hc
  obtain ⟨hf, inv1⟩ := arity_args hS iha h1
  obtain ⟨hp, rfl⟩ := flatChk_ir hi hy hf
  simp only [List.length_cons] at hp h2
  refine ⟨inv1, by omega, ?_⟩
  have : stk₁.length + 1 - (ps.length + 1) + rs.length = stk₁.length - ps.length + rs.length := by
    omega
  rwa [this] at h2

/-- The oracle's facts at an indirect or reference call. -/
theorem oracleX_at (hC : OracleSoundX P host C) (hS : StoreChkE irExt s.funcs) {top : Val}
    (inv1 : EvalInvE irExt s f (s₁, f₁, .normal (top :: stk₁))) (hfi : s₁.funcs[fa]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hp : ps.length ≤ stk₁.length)
    (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (f' : Frame) {c : Admin}
    (hcr : c.IsCallRef) :
    (∃ ob, (ob = none ∨ ob = some rs.length) ∧ FlowOk [rs.length] rs.length ob fl ∧
        FuncsGoodE irExt s₁.funcs s₂.funcs) ∧
      (∀ vs, fl.retVals = some vs → Steps P host
        ⟨s₁, f', vals (stk₁.take ps.length).reverse ++ [.ref (.func fa), c]⟩
        ⟨s₂, f', vals (vs.take rs.length).reverse⟩) ∧
      (fl = .trap → Steps P host
        ⟨s₁, f', vals (stk₁.take ps.length).reverse ++ [.ref (.func fa), c]⟩ ⟨s₂, f', [.trap]⟩) :=
  hC s₁ s₂ f' fa fi ps rs _ fl c (storeChk_inv inv1 hS) hfi hty (take_rev_length hp) hcr hcall

theorem arityX_irOk {i : Instr} {top : Val} (hC : OracleSoundX P host C)
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (iha : ArityGoodE irExt s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
    (ihk : ArityGoodE irExt s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
    ArityGoodE irExt s f stk (.op i args :: es) r := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, h2⟩ := arity_ir_pre hS iha hi hy hc
  obtain ⟨⟨ob, hob, hok, hfuncs⟩, -, -⟩ :=
    oracleX_at hC hS inv1 hfi hty hp hcall f₁ (c := .callRefType fi.type) trivial
  have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
  have inv2 : EvalInvE irExt s f (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
    ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  have hlen : (vs.take rs.length ++ stk₁.drop ps.length).length =
      stk₁.length - ps.length + rs.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have h2' : chkE irExt s₂.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out := by
    rw [hlen]
    exact chk_inv inv2 h2
  obtain ⟨hok', inv3⟩ := ihk (storeChk_inv inv2 hS) h2'
  exact ⟨hok', inv2.trans inv3⟩

theorem arityX_irStop {i : Instr} {top : Val} (hC : OracleSoundX P host C)
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (iha : ArityGoodE irExt s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hfl : fl.Abrupt) :
    ArityGoodE irExt s f stk (.op i args :: es) (s₂, f₁, fl) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, -⟩ := arity_ir_pre hS iha hi hy hc
  obtain ⟨⟨_, _, hok, hfuncs⟩, -, -⟩ :=
    oracleX_at hC hS inv1 hfi hty hp hcall f₁ (c := .callRefType fi.type) trivial
  cases fl with
  | trap => exact ⟨trivial, inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  | throw t => exact absurd hok id
  | _ => exact absurd hfl id

/-- A trap reached from the arguments' checked height, with the invariants. -/
theorem arityX_irTrap {i : Instr} {top : Val}
    (iha : ArityGoodE irExt s f stk args (s₁, f₁, .normal (top :: stk₁))) :
    ArityGoodE irExt s f stk (.op i args :: es) (s₁, f₁, .trap) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨-, inv1⟩ := arity_args hS iha h1
  exact ⟨trivial, inv1⟩

/-- A tail call is not checked by `irExt`. -/
theorem flatChk_tail {i : Instr} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {h : Nat} {stk' : List Val} {o' : Option (Nat × List Val)}
    (hres : TailRes s₁ f₁ i stk' o') : flatChkE irExt F mi nl ret labels h i = none := by
  cases hres <;> rfl

theorem arityX_tail {i : Instr} {r' : Store H × Frame × Binaryen.Flow}
    {o' : Option (Nat × List Val)}
    (iha : ArityGoodE irExt s f stk args (s₁, f₁, .normal stk₁)) (hres : TailRes s₁ f₁ i stk₁ o') :
    ArityGoodE irExt s f stk (.op i args :: es) r' := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨hf, -⟩ := arity_args hS iha h1
  rw [flatChk_tail hres] at hf
  cases hf

theorem coreX_tail {i : Instr} {r' : Store H × Frame × Binaryen.Flow}
    {o' : Option (Nat × List Val)}
    (iha : ArityGoodE irExt s f stk args (s₁, f₁, .normal stk₁)) (hres : TailRes s₁ f₁ i stk₁ o') :
    CoreGoodE irExt P host s f stk (.op i args :: es) r' := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨hf, -⟩ := arity_args hS iha h1
  rw [flatChk_tail hres] at hf
  cases hf

/-- The Core run of an indirect or reference call answered by the oracle, from the
callee reference and call form on top of the arguments, in context. -/
theorem steps_oracle_ir {rest : List Admin} {fin : List Admin} {c : Admin}
    (hst : Steps P host
      ⟨s₁, f₁, vals (stk₁.take ps.length).reverse ++ [.ref (.func fa), c]⟩ ⟨s₂, f₁, fin⟩) :
    Steps P host ⟨s₁, f₁, vals stk₁.reverse ++ [.ref (.func fa), c] ++ rest⟩
      ⟨s₂, f₁, vals (stk₁.drop ps.length).reverse ++ fin ++ rest⟩ := by
  have hsplit : vals stk₁.reverse =
      vals (stk₁.drop ps.length).reverse ++ vals (stk₁.take ps.length).reverse := by
    conv_lhs => rw [← List.take_append_drop ps.length stk₁]
    simp [vals]
  have h₂ := Steps.ctx (P := P) (host := host) (stk₁.drop ps.length).reverse rest hst
  rw [hsplit]
  simpa only [List.append_assoc] using h₂

/-- An indirect or reference call: the callee answered, the continuation runs. -/
theorem coreX_irOk {i : Instr} {top : Val} (hC : OracleSoundX P host C)
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (aha : ArityGoodE irExt s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (iha : CoreGoodE irExt P host s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (hpre : Steps P host ⟨s₁, f₁, vals [top] ++ [.plain i]⟩
      ⟨s₁, f₁, [.ref (.func fa), .plain (.callRef y)]⟩)
    (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs)
    (ihk : CoreGoodE irExt P host s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
    CoreGoodE irExt P host s f stk (.op i args :: es) r := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, h2⟩ := arity_ir_pre hS aha hi hy hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  obtain ⟨⟨ob, hob, hok, hfuncs⟩, hret, -⟩ :=
    oracleX_at hC hS inv1 hfi hty hp hcall f₁ (c := .plain (.callRef y)) trivial
  have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
  have inv2 : EvalInvE irExt s f (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
    ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  have hlen : (vs.take rs.length ++ stk₁.drop ps.length).length =
      stk₁.length - ps.length + rs.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have h2' : chkE irExt s₂.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out := by
    rw [hlen]
    exact chk_inv inv2 h2
  have hk := ihk (storeChk_inv inv2 hS) h2'
  let E := expression (Binaryen.BExpr.lowerList es)
  have st₁ := Steps.ctx (P := P) (host := host) stk₁.reverse E hpre
  have st₂ := steps_oracle_ir (rest := E) (hret vs hvs)
  have e : vals (top :: stk₁).reverse ++ .plain i :: E =
      vals stk₁.reverse ++ (vals [top] ++ [.plain i]) ++ E := by simp [vals]
  rw [code_op]
  refine wp_append_normal (iha hS ha) ?_
  rw [e]
  refine WP.steps (st₁.trans st₂) ?_
  simpa [vals, List.reverse_append, List.append_assoc] using hk

/-- An indirect or reference call that traps before any call (unresolved
callee, null reference). -/
theorem coreX_irTrap {i : Instr} {top : Val}
    (iha : CoreGoodE irExt P host s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (hpre : Steps P host ⟨s₁, f₁, vals [top] ++ [.plain i]⟩ ⟨s₁, f₁, [.trap]⟩) :
    CoreGoodE irExt P host s f stk (.op i args :: es) (s₁, f₁, .trap) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  let E := expression (Binaryen.BExpr.lowerList es)
  have st₁ := Steps.ctx (P := P) (host := host) stk₁.reverse E hpre
  have e : vals (top :: stk₁).reverse ++ .plain i :: E =
      vals stk₁.reverse ++ (vals [top] ++ [.plain i]) ++ E := by simp [vals]
  rw [code_op]
  refine wp_append_normal (iha hS ha) ?_
  rw [e]
  refine ⟨s₁, f₁, [.trap], .trap, st₁.trans ?_, rfl, rfl, rfl, trivial⟩
  simpa using steps_trap (P := P) (host := host) s₁ f₁ stk₁.reverse E

/-- An indirect or reference call whose callee traps or throws. -/
theorem coreX_irStop {i : Instr} {top : Val} (hC : OracleSoundX P host C)
    (hi : (∃ x, i = .callIndirect x y) ∨ i = .callRef y)
    (aha : ArityGoodE irExt s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (iha : CoreGoodE irExt P host s f stk args (s₁, f₁, .normal (top :: stk₁)))
    (hpre : Steps P host ⟨s₁, f₁, vals [top] ++ [.plain i]⟩
      ⟨s₁, f₁, [.ref (.func fa), .plain (.callRef y)]⟩)
    (hfi : s₁.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f₁.module y = some (ps.length, rs.length))
    (hcall : C s₁ fa (stk₁.take ps.length).reverse (s₂, fl)) (hfl : fl.Abrupt) :
    CoreGoodE irExt P host s f stk (.op i args :: es) (s₂, f₁, fl) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, -⟩ := arity_ir_pre hS aha hi hy hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  obtain ⟨⟨_, _, hok, _⟩, -, htr⟩ :=
    oracleX_at hC hS inv1 hfi hty hp hcall f₁ (c := .plain (.callRef y)) trivial
  cases fl with
  | throw t => exact absurd hok id
  | trap =>
    let E := expression (Binaryen.BExpr.lowerList es)
    have st₁ := Steps.ctx (P := P) (host := host) stk₁.reverse E hpre
    have st₂ := steps_oracle_ir (rest := E) (htr rfl)
    have e : vals (top :: stk₁).reverse ++ .plain i :: E =
        vals stk₁.reverse ++ (vals [top] ++ [.plain i]) ++ E := by simp [vals]
    rw [code_op]
    refine wp_append_normal (iha hS ha) ?_
    rw [e]
    refine ⟨s₂, f₁, [.trap], .trap, (st₁.trans st₂).trans ?_, rfl, rfl, rfl, trivial⟩
    simpa using steps_trap (P := P) (host := host) s₂ f₁ (stk₁.drop ps.length).reverse E
  | _ => exact absurd hfl id

end XCases

/-- **Forward simulation of the indirect and reference calls**, with a sound
oracle: every `EvalOXT C` run of code checked by `irExt` is a Core 3.0 run, with
the arity invariants. Code with a tail call is rejected by `irExt`. -/
theorem evalOXT_goodE {C : Abstract.CallRel H} (hC : OracleSoundX P host C) {s : Store H}
    {f : Frame} {stk : List Val} {es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (h : EvalOXT C s f stk es r) :
    ArityGoodE irExt s f stk es r ∧ CoreGoodE irExt P host s f stk es r := by
  have hC' := hC.sound
  induction h with
  | nil => exact ⟨arity_nil, core_nil⟩
  | argsAbort _ hfl iha => exact ⟨arity_argsAbort iha.1 hfl, core_argsAbort iha.2 hfl⟩
  | callOk _ hfi hty hcall hvs _ iha ihk =>
    exact ⟨arityO_callOk hC' iha.1 hfi hty hcall hvs ihk.1,
      coreO_callOk hC' iha.1 iha.2 hfi hty hcall hvs ihk.2⟩
  | callTrap _ hfi hty hcall iha =>
    exact ⟨arityO_callTrap hC' iha.1 hfi hty hcall, coreO_callTrap hC' iha.1 iha.2 hfi hty hcall⟩
  | callThrow _ hfi hty hcall iha =>
    exact ⟨arityO_callThrow hC' iha.1 hfi hty hcall, coreO_callThrow hC' iha.1 hfi hty hcall⟩
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
  | callIndOk _ hres hfi hty hy hcall hvs _ iha ihk =>
    exact ⟨arityX_irOk hC (.inl ⟨_, rfl⟩) iha.1 hfi hty hy hcall hvs ihk.1,
      coreX_irOk hC (.inl ⟨_, rfl⟩) iha.1 iha.2
        (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_func hres) hfi hty hy hcall hvs ihk.2⟩
  | callIndRes _ hres iha =>
    exact ⟨arityX_irTrap iha.1,
      coreX_irTrap iha.2 (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_trap hres)⟩
  | callIndStop _ hres hfi hty hy hcall hfl iha =>
    exact ⟨arityX_irStop hC (.inl ⟨_, rfl⟩) iha.1 hfi hty hy hcall hfl,
      coreX_irStop hC (.inl ⟨_, rfl⟩) iha.1 iha.2
        (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_func hres) hfi hty hy hcall hfl⟩
  | callRefOk _ hfi hty hy hcall hvs _ iha ihk =>
    exact ⟨arityX_irOk hC (.inr rfl) iha.1 hfi hty hy hcall hvs ihk.1,
      coreX_irOk hC (.inr rfl) iha.1 iha.2 .refl hfi hty hy hcall hvs ihk.2⟩
  | callRefNull _ iha =>
    exact ⟨arityX_irTrap iha.1,
      coreX_irTrap iha.2 (.single (Step.callRefNull (c := .plain (.callRef _)) trivial))⟩
  | callRefStop _ hfi hty hy hcall hfl iha =>
    exact ⟨arityX_irStop hC (.inr rfl) iha.1 hfi hty hy hcall hfl,
      coreX_irStop hC (.inr rfl) iha.1 iha.2 .refl hfi hty hy hcall hfl⟩
  | tail _ hres _ _ _ _ iha => exact ⟨arityX_tail iha.1 hres, coreX_tail iha.1 hres⟩
  | tailRes _ hres iha => exact ⟨arityX_tail iha.1 hres, coreX_tail iha.1 hres⟩

end Silmaril.Wasm.Interp
