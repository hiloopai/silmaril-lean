module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.RMRead.Return
public import Silmaril.Wasm.SpecTec.Sim.Round9.RMCall.Thms

/-!
# Round 9, rm: `return_call_ref-frame-addr` at `configVD` (unrefined)

Round 6's `Bwd.bwdUpTo_returnCallRefFrameAddr` (rule 11), re-run at `configVD`, in every
`simEnv B` with `Bwd.CallInv`: the premise reads `$funcinst(z)[a].TYPE`, which at a `stateVD` image
is the type of the store's function (`funcTypeD_of_eval`, through
`HostRulesD.applies_funcinstD`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMRead

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV iterPat valsPat valsNPat evalExp_iterPat
  evalExp_valsPat)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Round7.MemSimd (configVD stateVD funcInstVD adminsToVD adminToVD instrsToVD
  adminsToVD_eq_single adminsToVD_append adminsToVD_vals configVD_cfgV)
open RMPure (toV_of_atomD labelD_of handlerD_of frameD_of valsD_of splitD_of adminsToVD_eq_split
  split2D_of)

variable {H : Type} {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile}
  {host : HostSemantics H}

/-- `$funcinst(z)[a].TYPE`, read back at a `stateVD` image. -/
theorem funcTypeD_of_eval {B : Builtins} {s : Store H} {f : Frame} {ρ : VarEnv} {a : Nat}
    {ty : Value} (hd : ρ.findDef? "funcinst" = none)
    (fz : ρ.findVal? "z" = some (stateVD hn s f)) (fa : ρ.findVal? "a" = some (.num (.natN a)))
    (h : EvalExp (simEnv B) ρ (.dotE (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a"))
      "TYPE") ty) :
    ∃ fi, s.funcs[a]? = some fi ∧ ty = CT.defType fi.type := by
  obtain ⟨fv, hfv, hty⟩ := evalExp_dotE_iff.1 h
  obtain ⟨wl, i, hwl, hi, hidx⟩ := evalExp_idxE_iff.1 hfv
  have hap : Applies (simEnv B) "funcinst" [.val (stateVD hn s f)] wl :=
    (applies_iff_callDef hd (Equiv.evalArgs_cons (evalExp_var fz) (evalArgs_nil _ ρ))).2
      (evalExp_callE_iff.1 hwl)
  have ewl : wl = .list (s.funcs.map (funcInstVD hn)) :=
    Equiv.ExecNumeric.Applies.unique hap (Round7.HostRulesD.applies_funcinstD B s f)
  have ei : Value.num (.natN i) = .num (.natN a) := EvalExp.unique hi (evalExp_var fa)
  subst ewl
  cases ei
  have hget : (s.funcs.map (funcInstVD hn))[a]? = some fv := by simpa [Value.idx?] using hidx
  rw [List.getElem?_map] at hget
  obtain ⟨fi, hfi, rfl⟩ := Option.map_eq_some_iff.1 hget
  refine ⟨fi, hfi, ?_⟩
  simp [funcInstVD, Value.field?] at hty
  exact hty.symm

/-- The premise of `return_call_ref-frame-addr` at a `stateVD` image. -/
theorem frameAddrD_prem {B : Builtins} (C : Bwd.CallInv (simEnv B)) {s : Store H} {f : Frame}
    {ρ : VarEnv} {addr : Nat} {ws : List Value} {els : Prop}
    (hd : ρ.findDef? "funcinst" = none) (fz : ρ.findVal? "z" = some (stateVD hn s f))
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
  obtain ⟨w', hw', hexp⟩ := Bwd.rulePrem_inv hp
  obtain ⟨ty, ft, hty, hft, rfl⟩ := Bwd.tup2_inv hw'
  obtain ⟨fi, hfi, rfl⟩ := funcTypeD_of_eval hd fz fa hty
  obtain ⟨T₁, T₂, fn₁, -, rfl⟩ := Bwd.funcTypePat_inv hft
  obtain ⟨ps, rs, hex, hlen, -⟩ := C.expand fi.type T₁ T₂ hexp
  have hn : ws.length = T₁.length := Bwd.natN_inj (Option.some.inj (fn.symm.trans fn₁))
  exact ⟨fi, ps, rs, hfi, hex, hn.trans hlen⟩

/-- **`Step_read` rule 11 (`return_call_ref-frame-addr`) backward at `configVD`**, up to
`CodeEq`. -/
theorem bwdRD_returnCallRefFrameAddr (B : Builtins) (C : Bwd.CallInv (simEnv B))
    (c : Config H) (w : Value)
    (hf : Fires (simEnv B) "Step_read" 11 (.tuple [configVD hn c, w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩ := by
  obtain ⟨s, f, code⟩ := c
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
  obtain ⟨ws, fv, fn, hw⟩ := Bwd.valsN_cat hr ex
  have ew : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  have hbody : EvalExp (simEnv B) _ (.catE (.catE (.catE (.catE (valsPat "val'" "val'*")
      (valsNPat "val" "val*" "n")) (.listE [.caseE "REF.FUNC_ADDR" (.varE "a")]))
      (.listE [.caseE "RETURN_CALL_REF" (.varE "yy")])) (iterPat "instr" "instr*"))
      (.list (ws₁ ++ ws ++ [.case "REF.FUNC_ADDR" av] ++ [.case "RETURN_CALL_REF" yy] ++ rest)) :=
    evalExp_cat (evalExp_cat (evalExp_cat (evalExp_cat ev₁ (evalExp_valsNPat (by decide) fn fv))
      (evalExp_list1 (evalExp_case (evalExp_var fa))))
      (evalExp_list1 (evalExp_case (evalExp_var fy)))) (evalExp_iterPat (by decide) fr')
  have hc : configVD hn ⟨s, f, code⟩ = cfgV z [.case "FRAME_%{%}%" (.tuple [kv, fr,
      .list (ws₁ ++ ws ++ [.case "REF.FUNC_ADDR" av] ++ [.case "RETURN_CALL_REF" yy] ++ rest)])] :=
    EvalExp.unique hl (evalExp_case (evalExp_tup2 (evalExp_var fz)
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fk) (evalExp_var ffr) hbody)))))
  have e₁ := configVD_cfgV hc
  obtain ⟨a, hcode, ha⟩ := adminsToVD_eq_single e₁.2.symm
  subst hcode
  obtain ⟨k, fi, body, rfl, -, -, hb⟩ := frameD_of ha
  have e₂ : ws₁ ++ ws ++ [.case "REF.FUNC_ADDR" av] ++ [.case "RETURN_CALL_REF" yy] ++ rest =
      ws₁ ++ ws ++ [.case "REF.FUNC_ADDR" av] ++ (.case "RETURN_CALL_REF" yy :: rest) := by simp
  obtain ⟨vs', vs, b, l₃, rfl, h₂, hlen, hb₁, h₃⟩ :=
    split2D_of B ((Value.list.inj hb).symm.trans e₂) htv₁ (ew ▸ htv)
  obtain ⟨c, rest', rfl, hc₁⟩ : ∃ c rest', l₃ = c :: rest' ∧
      adminToVD c = .case "RETURN_CALL_REF" yy := by
    match l₃, h₃ with
    | c :: rest', hl => exact ⟨c, rest', rfl, (List.cons.inj hl).1⟩
  obtain ⟨addr, rfl, hav⟩ := Bwd.decode_refFuncAddr (toV_of_atomD hb₁ rfl)
  obtain ⟨hcr, hc₁'⟩ := retCallRefD_of hc₁
  obtain ⟨yy', hyy, hyy'⟩ := adminToV_retToCall hcr
  have eyy : yy' = yy := (Value.case.inj (hyy.symm.trans hc₁')).2
  obtain ⟨fn₀, ps, rs, hfn, hex, hn⟩ :=
    frameAddrD_prem C rfl (e₁.1 ▸ fz) (hav ▸ fa) fn (hp _ (.head _))
  have hms : Round6.MemSimd.AdminsMS (vals vs ++ [.ref (.func addr), c.retToCall]) :=
    Round7.HostRulesD.adminsMS_append (Round7.HostRulesD.adminsMS_vals vs)
      ⟨trivial, Round7.HostRulesD.adminMS_callRef (retToCall_isCallRef hcr), trivial⟩
  have hw' : w = .list (adminsToVD (vals vs ++ [.ref (.func addr), c.retToCall])) := by
    rw [Round7.MemSimd.adminsToVD_eq _ hms, hw, adminsToV_append, h₂, hav, ← eyy, ← hyy']
    rfl
  have hst : Step P host ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func addr), c] ++
      rest')]⟩ ⟨s, f, vals vs ++ [.ref (.func addr), c.retToCallIn fi.module]⟩ :=
    .returnCallRefFrameAddr hcr hfn hex (hlen ▸ hn)
  have e₃ : vals vs' ++ vals vs ++ [.ref (.func addr)] ++ c :: rest' =
      vals vs' ++ vals vs ++ [.ref (.func addr), c] ++ rest' := by simp
  rw [e₃]
  exact ⟨_, _, Bwd.codeEq_retToCall hcr fi.module vs addr, hw', hst⟩

end Silmaril.Wasm.SpecTec.Sim.Round9.RMRead
