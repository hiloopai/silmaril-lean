module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Decode

/-!
# Track backward: `return_call_ref-frame-addr`, up to call annotations

`bwdUpTo_returnCallRefFrameAddr` is the `BackwardUpTo.read 11` field: a SpecTec
`return_call_ref-frame-addr` step from the image of a configuration lands on the image of
`vals vs ++ [REF.FUNC_ADDR a, c.retToCall]`, which is `ConfigEq`-related (`AdminEq.call`) to
Core's successor `vals vs ++ [REF.FUNC_ADDR a, c.retToCallIn fi.module]`. This is the rule of
obstruction 1, and the only `BackwardUpTo` field that needs the weakening.

Hypotheses: family C's `CtrlDecode` and `CtrlReads` (for `$funcinst`; `CtrlState` coerces to it),
and `CallInv` (`Expand` read back), all discharged for `Prims.builtins`; `RetDecode` and the `REF.FUNC_ADDR` decoder are proved.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Bwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV iterPat valsPat valsNPat evalExp_iterPat
  evalExp_valsPat)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

set_option maxHeartbeats 4000000 in
/-- No source instruction is encoded with the tag `REF.FUNC_ADDR`. -/
theorem instrToV_ne_refFuncAddr {i : Instr} {w : Value} :
    instrToV i ≠ .case "REF.FUNC_ADDR" w := by
  intro h
  cases i
  all_goals try first
    | exact absurd (Value.case.inj h).1 (by decide)
    | (have h' : schemaInstrV (Silmaril.Wasm.SpecTecEnc.encodeInstruction _) = _ := h
       obtain ⟨w', hw'⟩ := Exn.schemaInstrV_case (Silmaril.Wasm.SpecTecEnc.encodeInstruction _)
       rw [hw'] at h'
       exact absurd (Value.case.inj h').1 (by simp [Silmaril.Wasm.SpecTecEnc.encodeInstruction]))
  iterate 4 (all_goals (try (rename_i x; cases x)))
  all_goals first
    | exact absurd (Value.case.inj h).1 (by decide)
    | exact Value.noConfusion h

/-- An image headed `REF.FUNC_ADDR` is a function reference. -/
theorem decode_refFuncAddr {a : Admin} {x : Value} (h : adminToV a = .case "REF.FUNC_ADDR" x) :
    ∃ addr, a = .ref (.func addr) ∧ x = .num (.natN addr) := by
  cases a with
  | plain i => exact absurd h instrToV_ne_refFuncAddr
  | ref r =>
    cases r with
    | func addr => exact ⟨addr, rfl, (Value.case.inj h).2.symm⟩
    | extern r => exact absurd (Value.case.inj h).1 (by decide)
    | _ => exact absurd (Value.case.inj h).1 (by decide)
  | _ => exact absurd (Value.case.inj h).1 (by decide)

/-- A pair, read back. -/
theorem tup2_inv {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂]) v) :
    ∃ w₁ w₂, EvalExp env ρ e₁ w₁ ∧ EvalExp env ρ e₂ w₂ ∧ v = .tuple [w₁, w₂] := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 h
  obtain ⟨w₁, ws, h₁, hws, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨w₂, ws', h₂, hws', rfl⟩ := evalExps_cons_iff.1 hws
  obtain rfl := evalExps_nil_iff.1 hws'
  exact ⟨w₁, w₂, h₁, h₂, rfl⟩

/-- `%(e)`, read back. -/
theorem pct1_inv {env : Env} {ρ : VarEnv} {e : Exp} {u : Value}
    (h : EvalExp env ρ (.caseE "%" (.tupE [e])) u) :
    ∃ x, EvalExp env ρ e x ∧ u = .case "%" (.tuple [x]) := by
  obtain ⟨v, hv, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hv
  obtain ⟨x, xs, hx, hxs, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain rfl := evalExps_nil_iff.1 hxs
  exact ⟨x, hx, rfl⟩

/-- `FUNC %(t_1^n) -> %(t_2^m)`, read back: `n` is the length of `t_1*`. -/
theorem funcTypePat_inv {env : Env} {ρ : VarEnv} {w : Value}
    (h : EvalExp env ρ (.caseE "FUNC%->%" (.tupE [.caseE "%" (.tupE [.iterE (.varE "t_1")
        (.mk (.listN (.varE "n") none) [.mk "t_1" (.varE "t_1*")])]),
      .caseE "%" (.tupE [.iterE (.varE "t_2")
        (.mk (.listN (.varE "m") none) [.mk "t_2" (.varE "t_2*")])])])) w) :
    ∃ T₁ T₂, ρ.findVal? "n" = some (.num (.natN T₁.length)) ∧
      ρ.findVal? "m" = some (.num (.natN T₂.length)) ∧
      w = .case "FUNC%->%" (.tuple [.case "%" (.tuple [.list T₁]), .case "%" (.tuple [.list T₂])]) := by
  obtain ⟨v, hv, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨u₁, u₂, h₁, h₂, rfl⟩ := tup2_inv hv
  obtain ⟨x₁, hx₁, rfl⟩ := pct1_inv h₁
  obtain ⟨x₂, hx₂, rfl⟩ := pct1_inv h₂
  obtain ⟨T₁, -, fn, rfl⟩ := Exn.evalExp_varN_inv (by decide) hx₁
  obtain ⟨T₂, -, fm, rfl⟩ := Exn.evalExp_varN_inv (by decide) hx₂
  exact ⟨T₁, T₂, fn, fm, rfl⟩

/-- A body `val'* val* x y instr*`, decoded. -/
theorem decode_split2two {env : Env} (D : CtrlDecode env) {σ : List (IL.Id × Value)}
    {body : List Admin} {ws₁ ws rest : List Value} {x y : Value}
    (h : .list (adminsToV body) = Value.list (ws₁ ++ ws ++ [x] ++ [y] ++ rest))
    (ht₁ : HasTyp env (VarEnv.empty.bindVals σ) valsT (.list ws₁))
    (ht : HasTyp env (VarEnv.empty.bindVals σ) valsT (.list ws)) :
    ∃ vs' vs b c rest', body = vals vs' ++ vals vs ++ [b, c] ++ rest' ∧
      adminsToV (vals vs) = ws ∧ ws.length = vs.length ∧ adminToV b = x ∧ adminToV c = y := by
  have e : ws₁ ++ ws ++ [x] ++ [y] ++ rest = ws₁ ++ ws ++ [x] ++ (y :: rest) := by simp
  obtain ⟨vs', vs, b, l₃, rfl, h₂, hlen, hb, h₃⟩ := decode_split2 D (e ▸ h) ht₁ ht
  obtain ⟨c, rest', rfl, hc⟩ : ∃ c rest', l₃ = c :: rest' ∧ adminToV c = y := by
    match l₃, h₃ with
    | c :: rest', hl => exact ⟨c, rest', rfl, (List.cons.inj hl).1⟩
  exact ⟨vs', vs, b, c, rest', by simp, h₂, hlen, hb, hc⟩

/-- A `RulePr` premise without arguments, read back with its instance. -/
theorem rulePrem_inv {env : Env} {D : Interp} {els : Prop} {ρ : VarEnv} {x : IL.Id}
    {op : MixopS} {e : Exp} (h : PremW env D els ρ (.rulePr x [] op e)) :
    ∃ w, EvalExp env ρ e w ∧ D x op [] w := by
  cases h with
  | rulePr ha he hd =>
    obtain rfl := evalArgs_nil_iff.1 ha
    exact ⟨_, he, hd⟩

section Bwd

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}
variable (B : Builtins) (D : CtrlDecode (simEnv B)) (S : CtrlReads (simEnv B) hn)
  (C : CallInv (simEnv B))

/-- The two successors of `return_call_ref-frame-addr` are equivalent. -/
theorem codeEq_retToCall {c : Admin} (hc : c.IsReturnCallRef) (m : ModuleInst) (vs : List Val)
    (a : Nat) : CodeEq (vals vs ++ [.ref (.func a), c.retToCallIn m])
      (vals vs ++ [.ref (.func a), c.retToCall]) :=
  (CodeEq.refl _).append
    (.cons (.refl _) (.cons (.call (retToCallIn_isCallRef hc m) (retToCall_isCallRef hc)) .nil))

include S C in
/-- The premise of `return_call_ref-frame-addr`, read back into Core's. -/
theorem frameAddr_prem {s : Store H} {f : Frame} {ρ : VarEnv} {addr : Nat} {ws : List Value}
    {els : Prop}
    (hd : ρ.findDef? "funcinst" = none) (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fa : ρ.findVal? "a" = some (.num (.natN addr)))
    (fn : ρ.findVal? "n" = some (.num (.natN ws.length)))
    (hp : PremW (simEnv B) (DDerives (simEnv B) (otherwise (simEnv B))) els ρ (.rulePr "Expand" []
      "%~~%" (.tupE [.dotE (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a")) "TYPE",
        .caseE "FUNC%->%" (.tupE [.caseE "%" (.tupE [.iterE (.varE "t_1")
          (.mk (.listN (.varE "n") none) [.mk "t_1" (.varE "t_1*")])]),
        .caseE "%" (.tupE [.iterE (.varE "t_2")
          (.mk (.listN (.varE "m") none) [.mk "t_2" (.varE "t_2*")])])])]))) :
    ∃ fn ps rs, s.funcs[addr]? = some fn ∧ Validation.Expand fn.type (.func ps rs) ∧
      ws.length = ps.length := by
  obtain ⟨w', hw', hexp⟩ := rulePrem_inv hp
  obtain ⟨ty, ft, hty, hft, rfl⟩ := tup2_inv hw'
  obtain ⟨fi, hfi, rfl⟩ := funcType_of_eval B S hd fz fa hty
  obtain ⟨T₁, T₂, fn₁, -, rfl⟩ := funcTypePat_inv hft
  obtain ⟨ps, rs, hex, hlen, -⟩ := C.expand fi.type T₁ T₂ hexp
  have hn : ws.length = T₁.length := natN_inj (Option.some.inj (fn.symm.trans fn₁))
  exact ⟨fi, ps, rs, hfi, hex, hn.trans hlen⟩

include D S C in
/-- **`BackwardUpTo.read 11`** (`return_call_ref-frame-addr`): SpecTec's successor keeps the
annotation (`c.retToCall`), Core's resolves it (`c.retToCallIn fi.module`); they are
`CodeEq`-related. -/
theorem bwdUpTo_returnCallRefFrameAddr : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 11 (.tuple [configV hn c, w]) →
    ∃ is' js, CodeEq is' js ∧ w = .list (adminsToV js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (simEnv_readRules B).returnCallRefFrameAddr hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨kv, fk, -⟩ := quant_of (x := "k") (t := nT) hq (.tail _ (.head _))
  obtain ⟨fr, ffr, -⟩ := quant_of (x := "f") (t := frameT) hq (.tail _ (.tail _ (.head _)))
  obtain ⟨ws₁, fv₁, htv₁⟩ := quant_list (x := "val'*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  have ev₁ : EvalExp (simEnv B) _ (valsPat "val'" "val'*") (.list ws₁) :=
    evalExp_valsPat (by decide) fv₁
  obtain ⟨ws', fv', htv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  obtain ⟨av, fa, -⟩ := quant_of (x := "a") (t := .varT "addr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  obtain ⟨yy, fy, -⟩ := quant_of (x := "yy") (t := typeuseT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
  have ex : EvalExp (simEnv B) _ (.listE [.caseE "REF.FUNC_ADDR" (.varE "a"),
      .caseE "CALL_REF" (.varE "yy")]) (.list [.case "REF.FUNC_ADDR" av, .case "CALL_REF" yy]) :=
    evalExp_listE_iff.2 ⟨_, evalExps_cons (evalExp_case (evalExp_var fa))
      (evalExps_cons (evalExp_case (evalExp_var fy)) evalExps_nil), rfl⟩
  obtain ⟨rest, fr', -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))
  obtain ⟨hl, hr⟩ := Exn.evalExp_tup2_inv he
  obtain ⟨ws, fv, fn, hw⟩ := valsN_cat hr ex
  have ew : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  have hbody : EvalExp (simEnv B) _ (.catE (.catE (.catE (.catE (valsPat "val'" "val'*")
      (valsNPat "val" "val*" "n")) (.listE [.caseE "REF.FUNC_ADDR" (.varE "a")]))
      (.listE [.caseE "RETURN_CALL_REF" (.varE "yy")])) (iterPat "instr" "instr*"))
      (.list (ws₁ ++ ws ++ [.case "REF.FUNC_ADDR" av] ++ [.case "RETURN_CALL_REF" yy] ++ rest)) :=
    evalExp_cat (evalExp_cat (evalExp_cat (evalExp_cat ev₁ (evalExp_valsNPat (by decide) fn fv))
      (evalExp_list1 (evalExp_case (evalExp_var fa))))
      (evalExp_list1 (evalExp_case (evalExp_var fy)))) (evalExp_iterPat (by decide) fr')
  have hc : configV hn ⟨s, f, code⟩ = cfgV z [.case "FRAME_%{%}%" (.tuple [kv, fr,
      .list (ws₁ ++ ws ++ [.case "REF.FUNC_ADDR" av] ++ [.case "RETURN_CALL_REF" yy] ++ rest)])] :=
    EvalExp.unique hl (evalExp_case (evalExp_tup2 (evalExp_var fz)
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fk) (evalExp_var ffr) hbody)))))
  have e₁ := configV_cfgV hc
  obtain ⟨k, fi, body, rfl, -, -, hb⟩ := decode_frame D e₁.2.symm
  obtain ⟨vs', vs, b, c, rest', rfl, h₂, hlen, hb₁, hc₁⟩ :=
    decode_split2two D hb.symm htv₁ (ew ▸ htv)
  obtain ⟨addr, rfl, hav⟩ := decode_refFuncAddr hb₁
  have hcr : c.IsReturnCallRef := retDecode.returnCallRef c _ hc₁
  obtain ⟨yy', hyy, hyy'⟩ := adminToV_retToCall hcr
  have eyy : yy' = yy := (Value.case.inj (hyy.symm.trans hc₁)).2
  obtain ⟨fn₀, ps, rs, hfn, hex, hn⟩ :=
    frameAddr_prem B S C rfl (e₁.1 ▸ fz) (hav ▸ fa) fn (hp _ (.head _))
  have hw' : w = .list (adminsToV (vals vs ++ [.ref (.func addr), c.retToCall])) := by
    rw [hw, adminsToV_append, h₂, hav, ← eyy, ← hyy']
    rfl
  exact ⟨_, _, codeEq_retToCall hcr fi.module vs addr, hw',
    .returnCallRefFrameAddr hcr hfn hex (hlen ▸ hn)⟩

end Bwd

end Silmaril.Wasm.SpecTec.Sim.Bwd
