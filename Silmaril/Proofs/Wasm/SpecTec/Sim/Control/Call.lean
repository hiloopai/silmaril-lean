module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Control.Read

/-!
# Family C: `block`, `loop`, `call` and `return_call`

The four `Step_read` rules of the family that call a SpecTec function on the state:
`$blocktype_` (`block`, `loop`), `$funcinst` and `$moduleinst` (`call`, `return_call`). Under the
evaluator reading `block` and `loop` never fire (`ExecReadControl.not_ruleFires_block`): their
`if $blocktype_(z, bt) = t_1^m -> t_2^n` mentions `t_1*`, `t_2*` nowhere else. Under the
declarative reading they are quantified and typed like every other variable, and the rules fire.

The state functions enter through `CtrlState` (`Control/Defs.lean`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV valsNPat iterPat evalExp_iterPat evalExp_imm_iff)
open Silmaril.SpecTec.Equiv.ExecRead (blockRule loopRule callRule returnCallRule)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.ExecReadAggregate (evalExp_iterNVar)

/-! ## Calls of state functions -/

/-- A one-argument call of a function, at a bound variable. -/
theorem evalExp_call1 {env : Env} {ρ : VarEnv} {x y : IL.Id} {w v : Value}
    (hd : ρ.findDef? x = none) (hy : ρ.findVal? y = some w) (h : Applies env x [.val w] v) :
    EvalExp env ρ (.callE x [.expA (.varE y)]) v :=
  evalExp_callE_iff.2 ((applies_iff_callDef hd
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 hy) (evalArgs_nil env ρ))).1 h)

/-- A two-argument call of a function, at bound variables. -/
theorem evalExp_call2 {env : Env} {ρ : VarEnv} {x y₁ y₂ : IL.Id} {w₁ w₂ v : Value}
    (hd : ρ.findDef? x = none) (hy₁ : ρ.findVal? y₁ = some w₁) (hy₂ : ρ.findVal? y₂ = some w₂)
    (h : Applies env x [.val w₁, .val w₂] v) :
    EvalExp env ρ (.callE x [.expA (.varE y₁), .expA (.varE y₂)]) v :=
  evalExp_callE_iff.2 ((applies_iff_callDef hd
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 hy₁)
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 hy₂) (evalArgs_nil env ρ)))).1 h)

/-- `$blocktype_(z, bt) = %(t_1^m) ->_ [] %(t_2^n)`, at a call that returns those lists. -/
theorem evalExp_blocktypeEq {env : Env} {ρ : VarEnv} {z bt : Value} {T₁ T₂ : List Value}
    (hd : ρ.findDef? "blocktype_" = none) (fz : ρ.findVal? "z" = some z)
    (fb : ρ.findVal? "bt" = some bt) (fm : ρ.findVal? "m" = some (.num (.natN T₁.length)))
    (fn : ρ.findVal? "n" = some (.num (.natN T₂.length)))
    (f₁ : ρ.findVal? "t_1*" = some (.list T₁)) (f₂ : ρ.findVal? "t_2*" = some (.list T₂))
    (h : Applies env "blocktype_" [.val z, .val bt]
      (.case "%->_%%" (.tuple [.case "%" (.tuple [.list T₁]), .list [],
        .case "%" (.tuple [.list T₂])]))) :
    EvalExp env ρ (.cmpE .eqOp .boolT
      (.callE "blocktype_" [.expA (.varE "z"), .expA (.varE "bt")])
      (.caseE "%->_%%" (.tupE [.caseE "%" (.tupE [.iterE (.varE "t_1")
        (.mk (.listN (.varE "m") none) [.mk "t_1" (.varE "t_1*")])]), .listE [],
        .caseE "%" (.tupE [.iterE (.varE "t_2")
          (.mk (.listN (.varE "n") none) [.mk "t_2" (.varE "t_2*")])])]))) (.bool true) := by
  have e₁ : EvalExp env ρ (.caseE "%" (.tupE [.iterE (.varE "t_1")
      (.mk (.listN (.varE "m") none) [.mk "t_1" (.varE "t_1*")])])) (.case "%" (.tuple [.list T₁])) :=
    evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_iterNVar (by decide) fm f₁)
      evalExps_nil, rfl⟩)
  have e₂ : EvalExp env ρ (.caseE "%" (.tupE [.iterE (.varE "t_2")
      (.mk (.listN (.varE "n") none) [.mk "t_2" (.varE "t_2*")])])) (.case "%" (.tuple [.list T₂])) :=
    evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_iterNVar (by decide) fn f₂)
      evalExps_nil, rfl⟩)
  exact evalExp_cmpE_iff.2 ⟨_, _, evalExp_call2 hd fz fb h,
    evalExp_case (evalExp_tup3 e₁ evalExp_listNil e₂), by simp [cmpValues]⟩

/-! ## The constructions -/

/-- `Step_read/block`. -/
theorem sread_block {env : Env} (h : HasRuleAt env "Step_read" "%~>%" 0 blockRule)
    {z bt : Value} {ws is T₁ T₂ : List Value} (hlen : ws.length = T₁.length)
    (hz : TypedV env stateT z) (hm : TypedV env mT (.num (.natN T₁.length)))
    (hw : TypedV env valsT (.list ws)) (hbt : TypedV env blocktypeT bt)
    (his : TypedV env instrsT (.list is)) (hn : TypedV env nT (.num (.natN T₂.length)))
    (h₁ : TypedV env valtypesT (.list T₁)) (h₂ : TypedV env valtypesT (.list T₂))
    (hb : Applies env "blocktype_" [.val z, .val bt]
      (.case "%->_%%" (.tuple [.case "%" (.tuple [.list T₁]), .list [],
        .case "%" (.tuple [.list T₂])]))) :
    SRead env (cfgV z (ws ++ [.case "BLOCK" (.tuple [bt, .list is])]))
      [.case "LABEL_%{%}%" (.tuple [.num (.natN T₂.length), .list [], .list (ws ++ is)])] := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("m", .num (.natN T₁.length)), ("val*", .list ws),
    ("bt", bt), ("instr*", .list is), ("n", .num (.natN T₂.length)), ("t_1*", .list T₁),
    ("t_2*", .list T₂)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fm : ρ.findVal? "m" = some (.num (.natN T₁.length)) := rfl
  have fv : ρ.findVal? "val*" = some (.list ws) := rfl
  have fb : ρ.findVal? "bt" = some bt := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN T₂.length)) := rfl
  have f₁ : ρ.findVal? "t_1*" = some (.list T₁) := rfl
  have f₂ : ρ.findVal? "t_2*" = some (.list T₂) := rfl
  have evn : EvalExp env ρ (valsNPat "val" "val*" "m") (.list ws) :=
    evalExp_valsNPat (by decide) (hlen ▸ fm) fv
  have ei : EvalExp env ρ (iterPat "instr" "instr*") (.list is) := evalExp_iterPat (by decide) fi
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fm (hm ρ hρ) (QuantsOk.cons fv (hw ρ hρ)
      (QuantsOk.cons fb (hbt ρ hρ) (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons fn (hn ρ hρ)
      (QuantsOk.cons f₁ (h₁ ρ hρ) (QuantsOk.cons f₂ (h₂ ρ hρ) QuantsOk.nil))))))))
    (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_cat evn
        (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fb) ei))))))
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) evalExp_listNil
        (evalExp_cat evn ei)))))
    (prems_one (.ifPr (evalExp_blocktypeEq rfl fz fb fm fn f₁ f₂ hb)))

/-- `Step_read/loop`. -/
theorem sread_loop {env : Env} (h : HasRuleAt env "Step_read" "%~>%" 1 loopRule)
    {z bt : Value} {ws is T₁ T₂ : List Value} (hlen : ws.length = T₁.length)
    (hz : TypedV env stateT z) (hm : TypedV env mT (.num (.natN T₁.length)))
    (hw : TypedV env valsT (.list ws)) (hbt : TypedV env blocktypeT bt)
    (his : TypedV env instrsT (.list is)) (hn : TypedV env nT (.num (.natN T₂.length)))
    (h₁ : TypedV env valtypesT (.list T₁)) (h₂ : TypedV env valtypesT (.list T₂))
    (hb : Applies env "blocktype_" [.val z, .val bt]
      (.case "%->_%%" (.tuple [.case "%" (.tuple [.list T₁]), .list [],
        .case "%" (.tuple [.list T₂])]))) :
    SRead env (cfgV z (ws ++ [.case "LOOP" (.tuple [bt, .list is])]))
      [.case "LABEL_%{%}%" (.tuple [.num (.natN T₁.length),
        .list [.case "LOOP" (.tuple [bt, .list is])], .list (ws ++ is)])] := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("m", .num (.natN T₁.length)), ("val*", .list ws),
    ("bt", bt), ("instr*", .list is), ("t_1*", .list T₁), ("n", .num (.natN T₂.length)),
    ("t_2*", .list T₂)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fm : ρ.findVal? "m" = some (.num (.natN T₁.length)) := rfl
  have fv : ρ.findVal? "val*" = some (.list ws) := rfl
  have fb : ρ.findVal? "bt" = some bt := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have fn : ρ.findVal? "n" = some (.num (.natN T₂.length)) := rfl
  have f₁ : ρ.findVal? "t_1*" = some (.list T₁) := rfl
  have f₂ : ρ.findVal? "t_2*" = some (.list T₂) := rfl
  have evn : EvalExp env ρ (valsNPat "val" "val*" "m") (.list ws) :=
    evalExp_valsNPat (by decide) (hlen ▸ fm) fv
  have ei : EvalExp env ρ (iterPat "instr" "instr*") (.list is) := evalExp_iterPat (by decide) fi
  have el : EvalExp env ρ (.caseE "LOOP" (.tupE [.varE "bt", iterPat "instr" "instr*"]))
      (.case "LOOP" (.tuple [bt, .list is])) := evalExp_case (evalExp_tup2 (evalExp_var fb) ei)
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fm (hm ρ hρ) (QuantsOk.cons fv (hw ρ hρ)
      (QuantsOk.cons fb (hbt ρ hρ) (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons f₁ (h₁ ρ hρ)
      (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons f₂ (h₂ ρ hρ) QuantsOk.nil))))))))
    (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_cat evn (evalExp_list1 el))))
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fm) (evalExp_list1 el)
        (evalExp_cat evn ei)))))
    (prems_one (.ifPr (evalExp_blocktypeEq rfl fz fb fm fn f₁ f₂ hb)))

/-- The callee's type, read off `$funcinst(z)[a].TYPE`. -/
theorem evalExp_funcinstType {env : Env} {ρ : VarEnv} {z fv ty : Value} {fs : List Value}
    {a : Nat} (hd : ρ.findDef? "funcinst" = none) (fz : ρ.findVal? "z" = some z)
    (fa : ρ.findVal? "a" = some (.num (.natN a))) (hfs : Applies env "funcinst" [.val z] (.list fs))
    (hget : fs[a]? = some fv) (hty : fv.field? "TYPE" = some ty) :
    EvalExp env ρ (.subE (.dotE (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a")) "TYPE")
      (.varT "deftype" []) (.varT "typeuse" [])) ty :=
  evalExp_sub (evalExp_dotE_iff.2 ⟨fv, evalExp_idxE_iff.2 ⟨_, a, evalExp_call1 hd fz hfs,
    evalExp_var fa, by simpa [Value.idx?] using hget⟩, hty⟩)

/-- `$moduleinst(z).FUNCS[x!%.0] = a`. -/
theorem evalExp_funcAddrEq {env : Env} {ρ : VarEnv} {z mv : Value} {fas : List Value} {k a : Nat}
    (hd : ρ.findDef? "moduleinst" = none) (fz : ρ.findVal? "z" = some z)
    (fx : ρ.findVal? "x" = some (pctV k)) (fa : ρ.findVal? "a" = some (.num (.natN a)))
    (hm : Applies env "moduleinst" [.val z] mv) (hf : mv.field? "FUNCS" = some (.list fas))
    (hget : fas[k]? = some (.num (.natN a))) :
    EvalExp env ρ (.cmpE .eqOp .boolT (.idxE (.dotE (.callE "moduleinst" [.expA (.varE "z")])
      "FUNCS") (.projE (.uncaseE (.varE "x") "%") 0)) (.varE "a")) (.bool true) :=
  evalExp_cmpE_iff.2 ⟨_, _, evalExp_idxE_iff.2 ⟨_, k,
    evalExp_dotE_iff.2 ⟨mv, evalExp_call1 hd fz hm, hf⟩, (evalExp_imm_iff fx).2 ⟨[], rfl⟩,
    by simpa [Value.idx?] using hget⟩, evalExp_var fa, by simp [cmpValues]⟩

/-- `Step_read/call`. -/
theorem sread_call {env : Env} (h : HasRuleAt env "Step_read" "%~>%" 6 callRule)
    {z mv fv ty : Value} {fs fas : List Value} {k a : Nat}
    (hz : TypedV env stateT z) (hx : TypedV env idxT (pctV k))
    (ha : TypedV env addrT (.num (.natN a))) (hfs : Applies env "funcinst" [.val z] (.list fs))
    (hget : fs[a]? = some fv) (hty : fv.field? "TYPE" = some ty)
    (hm : Applies env "moduleinst" [.val z] mv) (hf : mv.field? "FUNCS" = some (.list fas))
    (hfa : fas[k]? = some (.num (.natN a))) :
    SRead env (cfgV z [.case "CALL" (pctV k)])
      [.case "REF.FUNC_ADDR" (.num (.natN a)), .case "CALL_REF" ty] := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("x", pctV k), ("a", .num (.natN a))]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fx : ρ.findVal? "x" = some (pctV k) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN a)) := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fx (hx ρ hρ) (QuantsOk.cons fa (ha ρ hρ)
      QuantsOk.nil)))
    (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_list1 (evalExp_case (evalExp_var fx)))))
      (evalExp_list2 (evalExp_case (evalExp_var fa))
        (evalExp_case (evalExp_funcinstType rfl fz fa hfs hget hty))))
    (prems_one (.ifPr (evalExp_funcAddrEq rfl fz fx fa hm hf hfa)))

/-- `Step_read/return_call`. -/
theorem sread_returnCall {env : Env} (h : HasRuleAt env "Step_read" "%~>%" 7 returnCallRule)
    {z mv fv ty : Value} {fs fas : List Value} {k a : Nat}
    (hz : TypedV env stateT z) (hx : TypedV env idxT (pctV k))
    (ha : TypedV env addrT (.num (.natN a))) (hfs : Applies env "funcinst" [.val z] (.list fs))
    (hget : fs[a]? = some fv) (hty : fv.field? "TYPE" = some ty)
    (hm : Applies env "moduleinst" [.val z] mv) (hf : mv.field? "FUNCS" = some (.list fas))
    (hfa : fas[k]? = some (.num (.natN a))) :
    SRead env (cfgV z [.case "RETURN_CALL" (pctV k)])
      [.case "REF.FUNC_ADDR" (.num (.natN a)), .case "RETURN_CALL_REF" ty] := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("x", pctV k), ("a", .num (.natN a))]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fx : ρ.findVal? "x" = some (pctV k) := rfl
  have fa : ρ.findVal? "a" = some (.num (.natN a)) := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fx (hx ρ hρ) (QuantsOk.cons fa (ha ρ hρ)
      QuantsOk.nil)))
    (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_list1 (evalExp_case (evalExp_var fx)))))
      (evalExp_list2 (evalExp_case (evalExp_var fa))
        (evalExp_case (evalExp_funcinstType rfl fz fa hfs hget hty))))
    (prems_one (.ifPr (evalExp_funcAddrEq rfl fz fx fa hm hf hfa)))

/-! ## The forward fields -/

section Fwd

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type} {hn : H → String}
variable (B : Builtins) (T : TypingFacts (simEnv B) hn) (Ty : CtrlTyping (simEnv B))
  (S : CtrlState (simEnv B) hn)

include T Ty S in
/-- `Forward.block`. -/
theorem fwd_block : ∀ {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr}
    {vs : List Val} {t₁ t₂ : List CValType} (_ : f.module.blockType? bt = some (t₁, t₂))
    (_ : vs.length = t₁.length),
    FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩
      ⟨s, f, [.label t₂.length [] (vals vs ++ expression body)]⟩ := by
  intro s f bt body vs t₁ t₂ hbt hlen
  obtain ⟨T₁, T₂, hl₁, hl₂, h₁, h₂, hb⟩ := S.blocktype s f bt t₁ t₂ hbt
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hz h => ?_
  have hv : TypedV (simEnv B) valsT (.list (adminsToV (vals vs))) := typedV_vals_prefix T h
  have hblk : TypedV (simEnv B) instrT (adminToV (.plain (.block bt body))) :=
    typedV_code h (.plain (.block bt body)) (by simp)
  obtain ⟨hbtT, hbody⟩ := Ty.blockInv _ _ hblk
  have hw : (adminsToV (vals vs)).length = T₁.length := by
    rw [adminsToV_length, vals_length, hlen, hl₁]
  have key := sread_block (simEnv_readRules B).block (z := stateV hn s f)
    (ws := adminsToV (vals vs)) (is := instrsToV body) hw hz (Ty.natM _) hv hbtT hbody
    (Ty.nat _) h₁ h₂ hb
  rw [hl₂] at key
  have e : adminsToV (vals vs ++ expression body) = adminsToV (vals vs) ++ instrsToV body := by
    rw [adminsToV_append, adminsToV_expression]
  have e' : adminsToV (vals vs ++ [.plain (.block bt body)]) =
      adminsToV (vals vs) ++ [adminToV (.plain (.block bt body))] := by
    rw [adminsToV_append]; rfl
  show SRead _ (cfgV _ (adminsToV (vals vs ++ [.plain (.block bt body)])))
    [adminToV (.label t₂.length [] (vals vs ++ expression body))]
  rw [e', adminToV_label, e]
  exact key

include T Ty S in
/-- `Forward.loop`. -/
theorem fwd_loop : ∀ {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr}
    {vs : List Val} {t₁ t₂ : List CValType} (_ : f.module.blockType? bt = some (t₁, t₂))
    (_ : vs.length = t₁.length),
    FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩
      ⟨s, f, [.label t₁.length [.loop bt body] (vals vs ++ expression body)]⟩ := by
  intro s f bt body vs t₁ t₂ hbt hlen
  obtain ⟨T₁, T₂, hl₁, hl₂, h₁, h₂, hb⟩ := S.blocktype s f bt t₁ t₂ hbt
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hz h => ?_
  have hv : TypedV (simEnv B) valsT (.list (adminsToV (vals vs))) := typedV_vals_prefix T h
  have hlp : TypedV (simEnv B) instrT (adminToV (.plain (.loop bt body))) :=
    typedV_code h (.plain (.loop bt body)) (by simp)
  obtain ⟨hbtT, hbody⟩ := Ty.loopInv _ _ hlp
  have hw : (adminsToV (vals vs)).length = T₁.length := by
    rw [adminsToV_length, vals_length, hlen, hl₁]
  have key := sread_loop (simEnv_readRules B).loop (z := stateV hn s f)
    (ws := adminsToV (vals vs)) (is := instrsToV body) hw hz (Ty.natM _) hv hbtT hbody
    (Ty.nat _) h₁ h₂ hb
  rw [hl₁] at key
  have e : adminsToV (vals vs ++ expression body) = adminsToV (vals vs) ++ instrsToV body := by
    rw [adminsToV_append, adminsToV_expression]
  have e' : adminsToV (vals vs ++ [.plain (.loop bt body)]) =
      adminsToV (vals vs) ++ [adminToV (.plain (.loop bt body))] := by
    rw [adminsToV_append]; rfl
  show SRead _ (cfgV _ (adminsToV (vals vs ++ [.plain (.loop bt body)])))
    [adminToV (.label t₁.length [.loop bt body] (vals vs ++ expression body))]
  rw [e', adminToV_label, e]
  exact key

/-- `$funcinst(z)[a]` at an existing function. -/
theorem funcs_getElem_map {s : Store H} {a : Nat} {fi : FuncInst H} (h : s.funcs[a]? = some fi) :
    (s.funcs.map (funcInstV hn))[a]? = some (funcInstV hn fi) := by
  simp [h]

/-- `$moduleinst(z).FUNCS[x]` at an existing function index. -/
theorem moduleFuncs_getElem_map {m : ModuleInst} {k a : Nat} (h : m.funcs[k]? = some a) :
    (m.funcs.map fun a => Value.num (.natN a))[k]? = some (.num (.natN a)) := by
  simp [h]

include T Ty S in
/-- `Forward.call`. -/
theorem fwd_call : ∀ {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (_ : f.module.funcs[x.toNat]? = some a) (_ : s.funcs[a]? = some fi),
    FwdP (simEnv B) hn ⟨s, f, [.plain (.call x)]⟩ ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩ := by
  intro s f x a fi hx hfi
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hz _ => ?_
  exact sread_call (simEnv_readRules B).call (k := x.toNat) hz (Ty.idx x) (Ty.addr a)
    (S.funcinst s f) (funcs_getElem_map hfi) rfl (S.moduleinst s f) rfl
    (moduleFuncs_getElem_map hx)

include T Ty S in
/-- `Forward.returnCall`. -/
theorem fwd_returnCall : ∀ {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (_ : f.module.funcs[x.toNat]? = some a) (_ : s.funcs[a]? = some fi),
    FwdP (simEnv B) hn ⟨s, f, [.plain (.returnCall x)]⟩
      ⟨s, f, [.ref (.func a), .returnCallRefType fi.type]⟩ := by
  intro s f x a fi hx hfi
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hz _ => ?_
  exact sread_returnCall (simEnv_readRules B).returnCall (k := x.toNat) hz (Ty.idx x) (Ty.addr a)
    (S.funcinst s f) (funcs_getElem_map hfi) rfl (S.moduleinst s f) rfl
    (moduleFuncs_getElem_map hx)

end Fwd

end Silmaril.Wasm.SpecTec.Sim
