module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Control.Backward
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Control.Call

/-!
# Family C: backward lemmas for `call` and `return_call`

`Step_read/call` and `Step_read/return_call` read the state through `$moduleinst` and
`$funcinst`. `CtrlState` names their values on images and `ExecNumeric.Applies.unique` makes
them functions, so the address and the callee's type the rule computes are Core's.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV evalExp_imm_iff)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)

/-- A one-argument call at a bound variable, read back as `Applies`. -/
theorem applies_of_call1 {env : Env} {ρ : VarEnv} {x y : IL.Id} {w v : Value}
    (hd : ρ.findDef? x = none) (hy : ρ.findVal? y = some w)
    (h : EvalExp env ρ (.callE x [.expA (.varE y)]) v) : Applies env x [.val w] v :=
  (applies_iff_callDef hd (Equiv.evalArgs_cons (evalExp_varE_iff.2 hy) (evalArgs_nil env ρ))).2
    (evalExp_callE_iff.1 h)

section Bwd

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type} {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile}
  {host : HostSemantics H}
variable (B : Builtins) (D : CtrlDecode (simEnv B)) (S : CtrlReads (simEnv B) hn)

/-- The `FUNCS` field of an encoded module. -/
theorem moduleInstV_funcs (m : ModuleInst) :
    (Equiv.RuntimeBridge.moduleInstToValue CT m).field? "FUNCS" =
      some (.list (m.funcs.map fun a => .num (.natN a))) := by
  simp [Equiv.RuntimeBridge.moduleInstToValue, Value.field?]

/-- An entry of an encoded address list. -/
theorem addrs_getElem {l : List Nat} {k : Nat} {v : Value}
    (h : (l.map fun a => Value.num (.natN a))[k]? = some v) :
    ∃ a, v = .num (.natN a) ∧ l[k]? = some a := by
  rw [List.getElem?_map] at h
  obtain ⟨a, ha, he⟩ := Option.map_eq_some_iff.1 h
  exact ⟨a, he.symm, ha⟩

include S in
/-- The address `$moduleinst(z).FUNCS[x!%.0] = a` names, read back. -/
theorem funcAddr_of_eval {s : Store H} {f : Frame} {ρ : VarEnv} {k : Nat} {a' : Value}
    (hd : ρ.findDef? "moduleinst" = none) (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? "x" = some (pctV k)) (fa : ρ.findVal? "a" = some a')
    (h : EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT (.idxE (.dotE (.callE "moduleinst"
      [.expA (.varE "z")]) "FUNCS") (.projE (.uncaseE (.varE "x") "%") 0)) (.varE "a"))
      (.bool true)) :
    ∃ a, a' = .num (.natN a) ∧ f.module.funcs[k]? = some a := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
  have e₂ : v₂ = a' := EvalExp.unique h₂ (evalExp_var fa)
  have e₁ : v₁ = v₂ := by simpa [cmpValues] using hc
  obtain ⟨wl, i, hwl, hi, hidx⟩ := evalExp_idxE_iff.1 h₁
  obtain ⟨m, hm, hfld⟩ := evalExp_dotE_iff.1 hwl
  have em : m = Equiv.RuntimeBridge.moduleInstToValue CT f.module :=
    Equiv.ExecNumeric.Applies.unique (applies_of_call1 hd fz hm) (S.moduleinst s f)
  have ei : Value.num (.natN i) = .num (.natN k) :=
    EvalExp.unique hi ((evalExp_imm_iff fx).2 ⟨[], rfl⟩)
  have ewl : wl = .list (f.module.funcs.map fun a => .num (.natN a)) :=
    Option.some.inj (hfld.symm.trans (em ▸ moduleInstV_funcs f.module))
  have hget : (f.module.funcs.map fun a => Value.num (.natN a))[k]? = some v₁ := by
    have hk : i = k := by injection ei with ei; injection ei
    simpa [Value.idx?, ewl, hk] using hidx
  obtain ⟨a, hv, ha⟩ := addrs_getElem hget
  exact ⟨a, by rw [← e₂, ← e₁, hv], ha⟩

include S in
/-- The callee's type `$funcinst(z)[a].TYPE`, read back. -/
theorem funcType_of_eval {s : Store H} {f : Frame} {ρ : VarEnv} {a : Nat} {ty : Value}
    (hd : ρ.findDef? "funcinst" = none) (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fa : ρ.findVal? "a" = some (.num (.natN a)))
    (h : EvalExp (simEnv B) ρ (.dotE (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a"))
      "TYPE") ty) :
    ∃ fi, s.funcs[a]? = some fi ∧ ty = CT.defType fi.type := by
  obtain ⟨fv, hfv, hty⟩ := evalExp_dotE_iff.1 h
  obtain ⟨wl, i, hwl, hi, hidx⟩ := evalExp_idxE_iff.1 hfv
  have ewl : wl = .list (s.funcs.map (funcInstV hn)) :=
    Equiv.ExecNumeric.Applies.unique (applies_of_call1 hd fz hwl) (S.funcinst s f)
  have ei : Value.num (.natN i) = .num (.natN a) := EvalExp.unique hi (evalExp_var fa)
  subst ewl
  cases ei
  have hget : (s.funcs.map (funcInstV hn))[a]? = some fv := by simpa [Value.idx?] using hidx
  rw [List.getElem?_map] at hget
  obtain ⟨fi, hfi, rfl⟩ := Option.map_eq_some_iff.1 hget
  refine ⟨fi, hfi, ?_⟩
  simp [funcInstV, Value.field?] at hty
  exact hty.symm

/-- The two state reads of `call` and `return_call`, read back into Core's premises. -/
theorem callRead_inv (S : CtrlReads (simEnv B) hn) {s : Store H} {f : Frame} {ρ : VarEnv}
    {k : Nat} {a' ty : Value} (hd₁ : ρ.findDef? "moduleinst" = none)
    (hd₂ : ρ.findDef? "funcinst" = none) (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? "x" = some (pctV k)) (fa : ρ.findVal? "a" = some a')
    (h : EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT (.idxE (.dotE (.callE "moduleinst"
      [.expA (.varE "z")]) "FUNCS") (.projE (.uncaseE (.varE "x") "%") 0)) (.varE "a"))
      (.bool true))
    (hty : EvalExp (simEnv B) ρ (.dotE (.idxE (.callE "funcinst" [.expA (.varE "z")])
      (.varE "a")) "TYPE") ty) :
    ∃ a fi, a' = .num (.natN a) ∧ ty = CT.defType (FuncInst.type fi) ∧
      f.module.funcs[k]? = some a ∧ s.funcs[a]? = some fi := by
  obtain ⟨a, ha', hfa⟩ := funcAddr_of_eval B S hd₁ fz fx fa h
  obtain ⟨fi, hfi, hty'⟩ := funcType_of_eval B S hd₂ fz (ha' ▸ fa) hty
  exact ⟨a, fi, ha', hty', hfa, hfi⟩

include D S in
/-- `Backward.read 6` (`call`). -/
theorem bwd_call : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 6 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  intro c w _ hf
  obtain ⟨σ, -, he, hp⟩ := ruleBody_scope (fires_body (simEnv_readRules B).call hf)
  have hc : ∃ z x' a' ty, configV hn c = .case "%;%" (.tuple [z, .list [.case "CALL" x']]) ∧
      w = .list [.case "REF.FUNC_ADDR" a', .case "CALL_REF" ty] ∧
      (VarEnv.empty.bindVals σ).findVal? "z" = some z ∧
      (VarEnv.empty.bindVals σ).findVal? "x" = some x' ∧
      (VarEnv.empty.bindVals σ).findVal? "a" = some a' ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.dotE (.idxE (.callE "funcinst"
        [.expA (.varE "z")]) (.varE "a")) "TYPE") ty := by
    concl_inv he
  obtain ⟨z, x', a', ty, hcfg, hw, fz, fx, fa, hty⟩ := hc
  have hz : stateV hn c.store c.frame = z ∧ adminsToV c.code = [.case "CALL" x'] := by
    simpa [configV] using hcfg
  obtain ⟨a₀, hcode, ha₀⟩ := adminsToV_eq_single hz.2
  obtain ⟨y, hy⟩ := D.call a₀ _ ha₀
  have hx : x' = pctV y.toNat := by
    subst hy
    exact (Value.case.inj ha₀).2.symm
  obtain ⟨a, fi, ha', hty', hfa, hfi⟩ := callRead_inv B S rfl rfl (hz.1 ▸ fz) (hx ▸ fx) fa
    (ifPrem (hp _ (by simp))) hty
  refine ⟨[.ref (.func a), .callRefType fi.type], by rw [hw, ha', hty']; rfl, ?_⟩
  obtain ⟨s, f, is⟩ := c
  have hcode' : is = [.plain (.call y)] := hcode.trans (congrArg (· :: []) hy)
  subst hcode'
  exact .call hfa hfi

include D S in
/-- `Backward.read 7` (`return_call`). -/
theorem bwd_returnCall : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 7 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  intro c w _ hf
  obtain ⟨σ, -, he, hp⟩ := ruleBody_scope (fires_body (simEnv_readRules B).returnCall hf)
  have hc : ∃ z x' a' ty, configV hn c = .case "%;%" (.tuple [z, .list [.case "RETURN_CALL" x']]) ∧
      w = .list [.case "REF.FUNC_ADDR" a', .case "RETURN_CALL_REF" ty] ∧
      (VarEnv.empty.bindVals σ).findVal? "z" = some z ∧
      (VarEnv.empty.bindVals σ).findVal? "x" = some x' ∧
      (VarEnv.empty.bindVals σ).findVal? "a" = some a' ∧
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.dotE (.idxE (.callE "funcinst"
        [.expA (.varE "z")]) (.varE "a")) "TYPE") ty := by
    concl_inv he
  obtain ⟨z, x', a', ty, hcfg, hw, fz, fx, fa, hty⟩ := hc
  have hz : stateV hn c.store c.frame = z ∧ adminsToV c.code = [.case "RETURN_CALL" x'] := by
    simpa [configV] using hcfg
  obtain ⟨a₀, hcode, ha₀⟩ := adminsToV_eq_single hz.2
  obtain ⟨y, hy⟩ := D.returnCall a₀ _ ha₀
  have hx : x' = pctV y.toNat := by
    subst hy
    exact (Value.case.inj ha₀).2.symm
  obtain ⟨a, fi, ha', hty', hfa, hfi⟩ := callRead_inv B S rfl rfl (hz.1 ▸ fz) (hx ▸ fx) fa
    (ifPrem (hp _ (by simp))) hty
  refine ⟨[.ref (.func a), .returnCallRefType fi.type], by rw [hw, ha', hty']; rfl, ?_⟩
  obtain ⟨s, f, is⟩ := c
  have hcode' : is = [.plain (.returnCall y)] := hcode.trans (congrArg (· :: []) hy)
  subst hcode'
  exact .returnCall hfa hfi

end Bwd

end Silmaril.Wasm.SpecTec.Sim
