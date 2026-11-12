module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Control.Basic

/-!
# Family C: the control rules of `Step_pure`, constructed

Each `spure_*` builds, under the declarative reading, the `Step_pure` derivation of one control
rule for arbitrary values of the rule's IL types; the hypotheses are exactly the rule's premises
and the typing of its quantified variables.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution
  (pctV caseNilV valsPat valsNPat iterPat evalExp_iterPat evalExp_valsPat evalExp_imm_iff)
open Silmaril.SpecTec.Equiv.Execution
  (ifTrueRule ifFalseRule labelValsRule brLabelZeroRule brLabelSuccRule brHandlerRule
   brIfTrueRule brIfFalseRule frameValsRule returnFrameRule returnLabelRule returnHandlerRule
   trapInstrsRule trapLabelRule trapHandlerRule trapFrameRule)
open Silmaril.SpecTec.Equiv.ExecDefault (brTableLtRule brTableGeRule)
open Silmaril.SpecTec.Equiv.ExecRef
  (brOnNullNullRule brOnNonNullNullRule callIndirectRule returnCallIndirectRule)

/-! ## Side conditions on immediates -/

/-- `x!%.0 op m`, for an immediate `x = %(k)`. -/
theorem evalExp_immCmp {env : Env} {ρ : VarEnv} {x : IL.Id} {k : Nat} {op : CmpOp} {t : OpTyp}
    {m : Num} {r : Value} (hx : ρ.findVal? x = some (pctV k))
    (hc : cmpValues op (.num (.natN k)) (.num m) = .ok r) :
    EvalExp env ρ (.cmpE op t (.projE (.uncaseE (.varE x) "%") 0) (.numE m)) r :=
  evalExp_cmpE_iff.2 ⟨_, _, (evalExp_imm_iff hx).2 ⟨[], rfl⟩, evalExp_numE_iff.2 rfl, hc⟩

/-- `x!%.0 =/= 0`. -/
theorem evalExp_immNe {env : Env} {ρ : VarEnv} {x : IL.Id} {k : Nat} {t : OpTyp}
    (hx : ρ.findVal? x = some (pctV k)) (hk : k ≠ 0) :
    EvalExp env ρ (.cmpE .neOp t (.projE (.uncaseE (.varE x) "%") 0) (.numE (.natN 0)))
      (.bool true) :=
  evalExp_immCmp hx (by simp [cmpValues, hk])

/-- `x!%.0 = 0`. -/
theorem evalExp_immEq {env : Env} {ρ : VarEnv} {x : IL.Id} {t : OpTyp}
    (hx : ρ.findVal? x = some (pctV 0)) :
    EvalExp env ρ (.cmpE .eqOp t (.projE (.uncaseE (.varE x) "%") 0) (.numE (.natN 0)))
      (.bool true) :=
  evalExp_immCmp hx (by simp [cmpValues])

/-! ## `if` -/

/-- `Step_pure/if-true`. -/
theorem spure_ifTrue {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 5 ifTrueRule)
    {k : Nat} (hk : k ≠ 0) {bt : Value} {b₁ b₂ : List Value} (hc : TypedV env i32T (pctV k))
    (hbt : TypedV env blocktypeT bt) (h₁ : TypedV env instrsT (.list b₁))
    (h₂ : TypedV env instrsT (.list b₂)) :
    SPure env [.case "CONST" (.tuple [caseNilV "I32", pctV k]),
        .case "IF%%ELSE%" (.tuple [bt, .list b₁, .list b₂])]
      [.case "BLOCK" (.tuple [bt, .list b₁])] := by
  let ρ := VarEnv.empty.bindVals
    [("c", pctV k), ("bt", bt), ("instr_1*", .list b₁), ("instr_2*", .list b₂)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fc : ρ.findVal? "c" = some (pctV k) := rfl
  have fb : ρ.findVal? "bt" = some bt := rfl
  have f₁ : ρ.findVal? "instr_1*" = some (.list b₁) := rfl
  have f₂ : ρ.findVal? "instr_2*" = some (.list b₂) := rfl
  have e₁ : EvalExp env ρ (iterPat "instr_1" "instr_1*") (.list b₁) := evalExp_iterPat (by decide) f₁
  have e₂ : EvalExp env ρ (iterPat "instr_2" "instr_2*") (.list b₂) := evalExp_iterPat (by decide) f₂
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fc (hc ρ hρ) (QuantsOk.cons fb (hbt ρ hρ)
      (QuantsOk.cons f₁ (h₁ ρ hρ) (QuantsOk.cons f₂ (h₂ ρ hρ) QuantsOk.nil))))
    (evalExp_tup2
      (evalExp_list2 (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var fc)))
        (evalExp_case (evalExp_tup3 (evalExp_var fb) e₁ e₂)))
      (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fb) e₁))))
    (prems_one (.ifPr (evalExp_immNe fc hk)))

/-- `Step_pure/if-false`. -/
theorem spure_ifFalse {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 6 ifFalseRule)
    {bt : Value} {b₁ b₂ : List Value} (hc : TypedV env i32T (pctV 0))
    (hbt : TypedV env blocktypeT bt) (h₁ : TypedV env instrsT (.list b₁))
    (h₂ : TypedV env instrsT (.list b₂)) :
    SPure env [.case "CONST" (.tuple [caseNilV "I32", pctV 0]),
        .case "IF%%ELSE%" (.tuple [bt, .list b₁, .list b₂])]
      [.case "BLOCK" (.tuple [bt, .list b₂])] := by
  let ρ := VarEnv.empty.bindVals
    [("c", pctV 0), ("bt", bt), ("instr_1*", .list b₁), ("instr_2*", .list b₂)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fc : ρ.findVal? "c" = some (pctV 0) := rfl
  have fb : ρ.findVal? "bt" = some bt := rfl
  have f₁ : ρ.findVal? "instr_1*" = some (.list b₁) := rfl
  have f₂ : ρ.findVal? "instr_2*" = some (.list b₂) := rfl
  have e₁ : EvalExp env ρ (iterPat "instr_1" "instr_1*") (.list b₁) := evalExp_iterPat (by decide) f₁
  have e₂ : EvalExp env ρ (iterPat "instr_2" "instr_2*") (.list b₂) := evalExp_iterPat (by decide) f₂
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fc (hc ρ hρ) (QuantsOk.cons fb (hbt ρ hρ)
      (QuantsOk.cons f₁ (h₁ ρ hρ) (QuantsOk.cons f₂ (h₂ ρ hρ) QuantsOk.nil))))
    (evalExp_tup2
      (evalExp_list2 (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var fc)))
        (evalExp_case (evalExp_tup3 (evalExp_var fb) e₁ e₂)))
      (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fb) e₂))))
    (prems_one (.ifPr (evalExp_immEq fc)))

/-! ## Labels -/

/-- `Step_pure/label-vals`. -/
theorem spure_labelVals {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 7 labelValsRule)
    {n : Value} {cont ws : List Value} (hn : TypedV env nT n)
    (hc : TypedV env instrsT (.list cont)) (hw : TypedV env valsT (.list ws)) :
    SPure env [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list ws])] ws := by
  let ρ := VarEnv.empty.bindVals [("n", n), ("instr*", .list cont), ("val*", .list ws)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fn : ρ.findVal? "n" = some n := rfl
  have fi : ρ.findVal? "instr*" = some (.list cont) := rfl
  have fv : ρ.findVal? "val*" = some (.list ws) := rfl
  have ev : EvalExp env ρ (valsPat "val" "val*") (.list ws) := evalExp_valsPat (by decide) fv
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons fi (hc ρ hρ)
      (QuantsOk.cons fv (hw ρ hρ) QuantsOk.nil)))
    (evalExp_tup2
      (evalExp_list1 (evalExp_case
        (evalExp_tup3 (evalExp_var fn) (evalExp_iterPat (by decide) fi) ev))) ev)
    (fun _ h => nomatch h)

/-- `Step_pure/br-label-zero`. -/
theorem spure_brLabelZero {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 8 brLabelZeroRule)
    {l : Value} {cont ws' ws is : List Value} (hl₀ : l = pctV 0)
    (hn : TypedV env nT (.num (.natN ws.length))) (hc : TypedV env instrsT (.list cont))
    (hw' : TypedV env valsT (.list ws')) (hw : TypedV env valsT (.list ws))
    (hl : TypedV env labelidxT l) (his : TypedV env instrsT (.list is)) :
    SPure env [.case "LABEL_%{%}%" (.tuple [.num (.natN ws.length), .list cont,
        .list (ws' ++ ws ++ [.case "BR" l] ++ is)])] (ws ++ cont) := by
  subst hl₀
  let ρ := VarEnv.empty.bindVals [("n", .num (.natN ws.length)), ("instr'*", .list cont),
    ("val'*", .list ws'), ("val*", .list ws), ("l", pctV 0), ("instr*", .list is)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fn : ρ.findVal? "n" = some (.num (.natN ws.length)) := rfl
  have fc : ρ.findVal? "instr'*" = some (.list cont) := rfl
  have fv' : ρ.findVal? "val'*" = some (.list ws') := rfl
  have fv : ρ.findVal? "val*" = some (.list ws) := rfl
  have fl : ρ.findVal? "l" = some (pctV 0) := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have evn : EvalExp env ρ (valsNPat "val" "val*" "n") (.list ws) :=
    evalExp_valsNPat (by decide) fn fv
  have ec : EvalExp env ρ (iterPat "instr'" "instr'*") (.list cont) :=
    evalExp_iterPat (by decide) fc
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons fc (hc ρ hρ)
      (QuantsOk.cons fv' (hw' ρ hρ) (QuantsOk.cons fv (hw ρ hρ)
      (QuantsOk.cons fl (hl ρ hρ) (QuantsOk.cons fi (his ρ hρ) QuantsOk.nil))))))
    (evalExp_tup2
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) ec
        (evalExp_cat (evalExp_cat (evalExp_cat (evalExp_valsPat (by decide) fv') evn)
          (evalExp_list1 (evalExp_case (evalExp_var fl))))
          (evalExp_iterPat (by decide) fi)))))
      (evalExp_cat evn ec))
    (prems_one (.ifPr (evalExp_immEq fl)))

/-- `BR (l - 1)`, evaluated. -/
theorem evalExp_brSuccIdx {env : Env} {ρ : VarEnv} {j : Nat} (hj : 0 < j)
    (hl : ρ.findVal? "l" = some (pctV j)) :
    EvalExp env ρ (.caseE "%" (.tupE [.cvtE (.binE .subOp (.numT .intT)
        (.cvtE (.projE (.uncaseE (.varE "l") "%") 0) .natT .intT)
        (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT])) (pctV (j - 1)) := by
  have hp : EvalExp env ρ (.projE (.uncaseE (.varE "l") "%") 0) (.num (.natN j)) :=
    (evalExp_imm_iff hl).2 ⟨[], rfl⟩
  have h₁ : EvalExp env ρ (.cvtE (.projE (.uncaseE (.varE "l") "%") 0) .natT .intT)
      (.num (.intN j)) := evalExp_cvtE_iff.2 ⟨_, _, hp, rfl, rfl⟩
  have h₂ : EvalExp env ρ (.cvtE (.numE (.natN 1)) .natT .intT) (.num (.intN 1)) :=
    evalExp_cvtE_iff.2 ⟨_, _, evalExp_numE_iff.2 rfl, rfl, rfl⟩
  have h₃ : EvalExp env ρ (.binE .subOp (.numT .intT)
      (.cvtE (.projE (.uncaseE (.varE "l") "%") 0) .natT .intT)
      (.cvtE (.numE (.natN 1)) .natT .intT)) (.num (.intN ((j : Int) - 1))) := by
    refine evalExp_binE_iff.2 ⟨_, h₁, .inr ⟨?_, _, h₂, ?_⟩⟩
    · simp [boolShort]
    · simp [binValues, Num.bin, Res.ofOption]
  have h₄ : EvalExp env ρ (.cvtE (.binE .subOp (.numT .intT)
      (.cvtE (.projE (.uncaseE (.varE "l") "%") 0) .natT .intT)
      (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT) (.num (.natN (j - 1))) := by
    refine evalExp_cvtE_iff.2 ⟨_, _, h₃, ?_, rfl⟩
    simp only [Num.cvt]
    split
    · congr 2
      omega
    · omega
  exact evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons h₄ evalExps_nil, rfl⟩)

/-- `Step_pure/br-label-succ`. -/
theorem spure_brLabelSucc {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 9 brLabelSuccRule)
    {n : Value} {j : Nat} (hj : 0 < j) {cont ws is : List Value}
    (hn : TypedV env nT n) (hc : TypedV env instrsT (.list cont))
    (hw : TypedV env valsT (.list ws)) (hl : TypedV env labelidxT (pctV j))
    (his : TypedV env instrsT (.list is)) :
    SPure env [.case "LABEL_%{%}%" (.tuple [n, .list cont,
        .list (ws ++ [.case "BR" (pctV j)] ++ is)])] (ws ++ [.case "BR" (pctV (j - 1))]) := by
  let ρ := VarEnv.empty.bindVals [("n", n), ("instr'*", .list cont), ("val*", .list ws),
    ("l", pctV j), ("instr*", .list is)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fn : ρ.findVal? "n" = some n := rfl
  have fc : ρ.findVal? "instr'*" = some (.list cont) := rfl
  have fv : ρ.findVal? "val*" = some (.list ws) := rfl
  have fl : ρ.findVal? "l" = some (pctV j) := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have ev : EvalExp env ρ (valsPat "val" "val*") (.list ws) := evalExp_valsPat (by decide) fv
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons fc (hc ρ hρ)
      (QuantsOk.cons fv (hw ρ hρ) (QuantsOk.cons fl (hl ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) QuantsOk.nil)))))
    (evalExp_tup2
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
        (evalExp_iterPat (by decide) fc)
        (evalExp_cat (evalExp_cat ev (evalExp_list1 (evalExp_case (evalExp_var fl))))
          (evalExp_iterPat (by decide) fi)))))
      (evalExp_cat ev (evalExp_list1 (evalExp_case (evalExp_brSuccIdx hj fl)))))
    (prems_one (.ifPr (evalExp_immCmp fl (by simp [cmpValues, Num.cmp, Res.ofOption, hj]))))

/-- `Step_pure/br-handler`. -/
theorem spure_brHandler {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 10 brHandlerRule)
    {n l : Value} {cs ws is : List Value} (hn : TypedV env nT n)
    (hc : TypedV env catchesT (.list cs)) (hw : TypedV env valsT (.list ws))
    (hl : TypedV env labelidxT l) (his : TypedV env instrsT (.list is)) :
    SPure env [.case "HANDLER_%{%}%" (.tuple [n, .list cs,
        .list (ws ++ [.case "BR" l] ++ is)])] (ws ++ [.case "BR" l]) := by
  let ρ := VarEnv.empty.bindVals [("n", n), ("catch*", .list cs), ("val*", .list ws),
    ("l", l), ("instr*", .list is)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fn : ρ.findVal? "n" = some n := rfl
  have fc : ρ.findVal? "catch*" = some (.list cs) := rfl
  have fv : ρ.findVal? "val*" = some (.list ws) := rfl
  have fl : ρ.findVal? "l" = some l := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have ev : EvalExp env ρ (valsPat "val" "val*") (.list ws) := evalExp_valsPat (by decide) fv
  have eb : EvalExp env ρ (.listE [.caseE "BR" (.varE "l")]) (.list [.case "BR" l]) :=
    evalExp_list1 (evalExp_case (evalExp_var fl))
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons fc (hc ρ hρ)
      (QuantsOk.cons fv (hw ρ hρ) (QuantsOk.cons fl (hl ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) QuantsOk.nil)))))
    (evalExp_tup2
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
        (evalExp_iterPat (by decide) fc)
        (evalExp_cat (evalExp_cat ev eb) (evalExp_iterPat (by decide) fi)))))
      (evalExp_cat ev eb))
    (fun _ h => nomatch h)

/-! ## Conditional branches -/

/-- `Step_pure/br_if-true`. -/
theorem spure_brIfTrue {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 11 brIfTrueRule)
    {k : Nat} (hk : k ≠ 0) {l : Value} (hc : TypedV env i32T (pctV k))
    (hl : TypedV env labelidxT l) :
    SPure env [.case "CONST" (.tuple [caseNilV "I32", pctV k]), .case "BR_IF" l]
      [.case "BR" l] := by
  let ρ := VarEnv.empty.bindVals [("c", pctV k), ("l", l)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fc : ρ.findVal? "c" = some (pctV k) := rfl
  have fl : ρ.findVal? "l" = some l := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fc (hc ρ hρ) (QuantsOk.cons fl (hl ρ hρ) QuantsOk.nil))
    (evalExp_tup2
      (evalExp_list2 (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var fc)))
        (evalExp_case (evalExp_var fl)))
      (evalExp_list1 (evalExp_case (evalExp_var fl))))
    (prems_one (.ifPr (evalExp_immNe fc hk)))

/-- `Step_pure/br_if-false`. -/
theorem spure_brIfFalse {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 12 brIfFalseRule)
    {l : Value} (hc : TypedV env i32T (pctV 0)) (hl : TypedV env labelidxT l) :
    SPure env [.case "CONST" (.tuple [caseNilV "I32", pctV 0]), .case "BR_IF" l] [] := by
  let ρ := VarEnv.empty.bindVals [("c", pctV 0), ("l", l)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fc : ρ.findVal? "c" = some (pctV 0) := rfl
  have fl : ρ.findVal? "l" = some l := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fc (hc ρ hρ) (QuantsOk.cons fl (hl ρ hρ) QuantsOk.nil))
    (evalExp_tup2
      (evalExp_list2 (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var fc)))
        (evalExp_case (evalExp_var fl)))
      evalExp_listNil)
    (prems_one (.ifPr (evalExp_immEq fc)))

/-- `Step_pure/br_table-lt`. -/
theorem spure_brTableLt {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 13 brTableLtRule)
    {k : Nat} {ls : List Value} {l' l : Value} (hk : ls[k]? = some l)
    (hc : TypedV env i32T (pctV k)) (hls : TypedV env labelidxsT (.list ls))
    (hl' : TypedV env labelidxT l') :
    SPure env [.case "CONST" (.tuple [caseNilV "I32", pctV k]),
        .case "BR_TABLE" (.tuple [.list ls, l'])] [.case "BR" l] := by
  let ρ := VarEnv.empty.bindVals [("i", pctV k), ("l*", .list ls), ("l'", l')]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fi : ρ.findVal? "i" = some (pctV k) := rfl
  have fls : ρ.findVal? "l*" = some (.list ls) := rfl
  have fl' : ρ.findVal? "l'" = some l' := rfl
  have els : EvalExp env ρ (iterPat "l" "l*") (.list ls) := evalExp_iterPat (by decide) fls
  have hlt : k < ls.length := (List.getElem?_eq_some_iff.1 hk).1
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fi (hc ρ hρ) (QuantsOk.cons fls (hls ρ hρ)
      (QuantsOk.cons fl' (hl' ρ hρ) QuantsOk.nil)))
    (evalExp_tup2
      (evalExp_list2 (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var fi)))
        (evalExp_case (evalExp_tup2 els (evalExp_var fl'))))
      (evalExp_list1 (evalExp_case (evalExp_idxE_iff.2
        ⟨_, k, els, (evalExp_imm_iff fi).2 ⟨[], rfl⟩, by simpa [Value.idx?] using hk⟩))))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, (evalExp_imm_iff fi).2 ⟨[], rfl⟩,
      evalExp_lenE_iff.2 ⟨ls, els, rfl⟩, by simp [cmpValues, Num.cmp, Res.ofOption, hlt]⟩)))

/-- `Step_pure/br_table-ge`. -/
theorem spure_brTableGe {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 14 brTableGeRule)
    {k : Nat} {ls : List Value} {l' : Value} (hk : ls.length ≤ k)
    (hc : TypedV env i32T (pctV k)) (hls : TypedV env labelidxsT (.list ls))
    (hl' : TypedV env labelidxT l') :
    SPure env [.case "CONST" (.tuple [caseNilV "I32", pctV k]),
        .case "BR_TABLE" (.tuple [.list ls, l'])] [.case "BR" l'] := by
  let ρ := VarEnv.empty.bindVals [("i", pctV k), ("l*", .list ls), ("l'", l')]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fi : ρ.findVal? "i" = some (pctV k) := rfl
  have fls : ρ.findVal? "l*" = some (.list ls) := rfl
  have fl' : ρ.findVal? "l'" = some l' := rfl
  have els : EvalExp env ρ (iterPat "l" "l*") (.list ls) := evalExp_iterPat (by decide) fls
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fi (hc ρ hρ) (QuantsOk.cons fls (hls ρ hρ)
      (QuantsOk.cons fl' (hl' ρ hρ) QuantsOk.nil)))
    (evalExp_tup2
      (evalExp_list2 (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var fi)))
        (evalExp_case (evalExp_tup2 els (evalExp_var fl'))))
      (evalExp_list1 (evalExp_case (evalExp_var fl'))))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, (evalExp_imm_iff fi).2 ⟨[], rfl⟩,
      evalExp_lenE_iff.2 ⟨ls, els, rfl⟩, by simp [cmpValues, Num.cmp, Res.ofOption, hk]⟩)))

/-- `Step_pure/br_on_null-null`. -/
theorem spure_brOnNullNull {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 15 brOnNullNullRule)
    {l : Value} (hv : TypedV env valT (caseNilV "REF.NULL_ADDR")) (hl : TypedV env labelidxT l) :
    SPure env [caseNilV "REF.NULL_ADDR", .case "BR_ON_NULL" l] [.case "BR" l] := by
  let ρ := VarEnv.empty.bindVals [("val", caseNilV "REF.NULL_ADDR"), ("l", l)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fv : ρ.findVal? "val" = some (caseNilV "REF.NULL_ADDR") := rfl
  have fl : ρ.findVal? "l" = some l := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fv (hv ρ hρ) (QuantsOk.cons fl (hl ρ hρ) QuantsOk.nil))
    (evalExp_tup2
      (evalExp_list2 (evalExp_sub (evalExp_var fv)) (evalExp_case (evalExp_var fl)))
      (evalExp_list1 (evalExp_case (evalExp_var fl))))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_var fv, evalExp_caseNil,
      by simp [cmpValues]⟩)))

/-- `Step_pure/br_on_non_null-null`. -/
theorem spure_brOnNonNullNull {env : Env}
    (h : HasRuleAt env "Step_pure" "%~>%" 17 brOnNonNullNullRule)
    {l : Value} (hv : TypedV env valT (caseNilV "REF.NULL_ADDR")) (hl : TypedV env labelidxT l) :
    SPure env [caseNilV "REF.NULL_ADDR", .case "BR_ON_NON_NULL" l] [] := by
  let ρ := VarEnv.empty.bindVals [("val", caseNilV "REF.NULL_ADDR"), ("l", l)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fv : ρ.findVal? "val" = some (caseNilV "REF.NULL_ADDR") := rfl
  have fl : ρ.findVal? "l" = some l := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fv (hv ρ hρ) (QuantsOk.cons fl (hl ρ hρ) QuantsOk.nil))
    (evalExp_tup2
      (evalExp_list2 (evalExp_sub (evalExp_var fv)) (evalExp_case (evalExp_var fl)))
      evalExp_listNil)
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_var fv, evalExp_caseNil,
      by simp [cmpValues]⟩)))

/-! ## Indirect calls -/

/-- `Step_pure/call_indirect`. -/
theorem spure_callIndirect {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 19 callIndirectRule)
    {x yy : Value} (hx : TypedV env idxT x) (hy : TypedV env typeuseT yy) :
    SPure env [.case "CALL_INDIRECT" (.tuple [x, yy])]
      [.case "TABLE.GET" x, .case "REF.CAST" (.case "REF" (.tuple [.opt (some (caseNilV "NULL")), yy])),
        .case "CALL_REF" yy] := by
  let ρ := VarEnv.empty.bindVals [("x", x), ("yy", yy)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fx : ρ.findVal? "x" = some x := rfl
  have fy : ρ.findVal? "yy" = some yy := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fx (hx ρ hρ) (QuantsOk.cons fy (hy ρ hρ) QuantsOk.nil))
    (evalExp_tup2
      (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fx) (evalExp_var fy))))
      (evalExp_list3 (evalExp_case (evalExp_var fx))
        (evalExp_case (evalExp_case (evalExp_tup2
          (evalExp_optE_some_iff.2 ⟨_, evalExp_caseNil, rfl⟩) (evalExp_sub (evalExp_var fy)))))
        (evalExp_case (evalExp_var fy))))
    (fun _ h => nomatch h)

/-- `Step_pure/return_call_indirect`. -/
theorem spure_returnCallIndirect {env : Env}
    (h : HasRuleAt env "Step_pure" "%~>%" 20 returnCallIndirectRule)
    {x yy : Value} (hx : TypedV env idxT x) (hy : TypedV env typeuseT yy) :
    SPure env [.case "RETURN_CALL_INDIRECT" (.tuple [x, yy])]
      [.case "TABLE.GET" x, .case "REF.CAST" (.case "REF" (.tuple [.opt (some (caseNilV "NULL")), yy])),
        .case "RETURN_CALL_REF" yy] := by
  let ρ := VarEnv.empty.bindVals [("x", x), ("yy", yy)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fx : ρ.findVal? "x" = some x := rfl
  have fy : ρ.findVal? "yy" = some yy := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fx (hx ρ hρ) (QuantsOk.cons fy (hy ρ hρ) QuantsOk.nil))
    (evalExp_tup2
      (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fx) (evalExp_var fy))))
      (evalExp_list3 (evalExp_case (evalExp_var fx))
        (evalExp_case (evalExp_case (evalExp_tup2
          (evalExp_optE_some_iff.2 ⟨_, evalExp_caseNil, rfl⟩) (evalExp_sub (evalExp_var fy)))))
        (evalExp_case (evalExp_var fy))))
    (fun _ h => nomatch h)

/-! ## Frames and `return` -/

/-- `Step_pure/frame-vals`. -/
theorem spure_frameVals {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 21 frameValsRule)
    {f : Value} {ws : List Value} (hn : TypedV env nT (.num (.natN ws.length)))
    (hf : TypedV env frameT f) (hw : TypedV env valsT (.list ws)) :
    SPure env [.case "FRAME_%{%}%" (.tuple [.num (.natN ws.length), f, .list ws])] ws := by
  let ρ := VarEnv.empty.bindVals [("n", .num (.natN ws.length)), ("f", f), ("val*", .list ws)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fn : ρ.findVal? "n" = some (.num (.natN ws.length)) := rfl
  have ff : ρ.findVal? "f" = some f := rfl
  have fv : ρ.findVal? "val*" = some (.list ws) := rfl
  have evn : EvalExp env ρ (valsNPat "val" "val*" "n") (.list ws) :=
    evalExp_valsNPat (by decide) fn fv
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons ff (hf ρ hρ)
      (QuantsOk.cons fv (hw ρ hρ) QuantsOk.nil)))
    (evalExp_tup2
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) (evalExp_var ff) evn))) evn)
    (fun _ h => nomatch h)

/-- `Step_pure/return-frame`. -/
theorem spure_returnFrame {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 22 returnFrameRule)
    {f : Value} {ws' ws is : List Value} (hn : TypedV env nT (.num (.natN ws.length)))
    (hf : TypedV env frameT f) (hw' : TypedV env valsT (.list ws'))
    (hw : TypedV env valsT (.list ws)) (his : TypedV env instrsT (.list is)) :
    SPure env [.case "FRAME_%{%}%" (.tuple [.num (.natN ws.length), f,
        .list (ws' ++ ws ++ [caseNilV "RETURN"] ++ is)])] ws := by
  let ρ := VarEnv.empty.bindVals [("n", .num (.natN ws.length)), ("f", f), ("val'*", .list ws'),
    ("val*", .list ws), ("instr*", .list is)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fn : ρ.findVal? "n" = some (.num (.natN ws.length)) := rfl
  have ff : ρ.findVal? "f" = some f := rfl
  have fv' : ρ.findVal? "val'*" = some (.list ws') := rfl
  have fv : ρ.findVal? "val*" = some (.list ws) := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have evn : EvalExp env ρ (valsNPat "val" "val*" "n") (.list ws) :=
    evalExp_valsNPat (by decide) fn fv
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons ff (hf ρ hρ)
      (QuantsOk.cons fv' (hw' ρ hρ) (QuantsOk.cons fv (hw ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) QuantsOk.nil)))))
    (evalExp_tup2
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) (evalExp_var ff)
        (evalExp_cat (evalExp_cat (evalExp_cat (evalExp_valsPat (by decide) fv') evn)
          (evalExp_list1 evalExp_caseNil)) (evalExp_iterPat (by decide) fi))))) evn)
    (fun _ h => nomatch h)

/-- `Step_pure/return-label`. -/
theorem spure_returnLabel {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 23 returnLabelRule)
    {n : Value} {cont ws is : List Value} (hn : TypedV env nT n)
    (hc : TypedV env instrsT (.list cont)) (hw : TypedV env valsT (.list ws))
    (his : TypedV env instrsT (.list is)) :
    SPure env [.case "LABEL_%{%}%" (.tuple [n, .list cont,
        .list (ws ++ [caseNilV "RETURN"] ++ is)])] (ws ++ [caseNilV "RETURN"]) := by
  let ρ := VarEnv.empty.bindVals [("n", n), ("instr'*", .list cont), ("val*", .list ws),
    ("instr*", .list is)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fn : ρ.findVal? "n" = some n := rfl
  have fc : ρ.findVal? "instr'*" = some (.list cont) := rfl
  have fv : ρ.findVal? "val*" = some (.list ws) := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have ev : EvalExp env ρ (valsPat "val" "val*") (.list ws) := evalExp_valsPat (by decide) fv
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons fc (hc ρ hρ)
      (QuantsOk.cons fv (hw ρ hρ) (QuantsOk.cons fi (his ρ hρ) QuantsOk.nil))))
    (evalExp_tup2
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
        (evalExp_iterPat (by decide) fc)
        (evalExp_cat (evalExp_cat ev (evalExp_list1 evalExp_caseNil))
          (evalExp_iterPat (by decide) fi)))))
      (evalExp_cat ev (evalExp_list1 evalExp_caseNil)))
    (fun _ h => nomatch h)

/-- `Step_pure/return-handler`. -/
theorem spure_returnHandler {env : Env}
    (h : HasRuleAt env "Step_pure" "%~>%" 24 returnHandlerRule)
    {n : Value} {cs ws is : List Value} (hn : TypedV env nT n)
    (hc : TypedV env catchesT (.list cs)) (hw : TypedV env valsT (.list ws))
    (his : TypedV env instrsT (.list is)) :
    SPure env [.case "HANDLER_%{%}%" (.tuple [n, .list cs,
        .list (ws ++ [caseNilV "RETURN"] ++ is)])] (ws ++ [caseNilV "RETURN"]) := by
  let ρ := VarEnv.empty.bindVals [("n", n), ("catch*", .list cs), ("val*", .list ws),
    ("instr*", .list is)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fn : ρ.findVal? "n" = some n := rfl
  have fc : ρ.findVal? "catch*" = some (.list cs) := rfl
  have fv : ρ.findVal? "val*" = some (.list ws) := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have ev : EvalExp env ρ (valsPat "val" "val*") (.list ws) := evalExp_valsPat (by decide) fv
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons fc (hc ρ hρ)
      (QuantsOk.cons fv (hw ρ hρ) (QuantsOk.cons fi (his ρ hρ) QuantsOk.nil))))
    (evalExp_tup2
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
        (evalExp_iterPat (by decide) fc)
        (evalExp_cat (evalExp_cat ev (evalExp_list1 evalExp_caseNil))
          (evalExp_iterPat (by decide) fi)))))
      (evalExp_cat ev (evalExp_list1 evalExp_caseNil)))
    (fun _ h => nomatch h)

/-! ## Traps -/

/-- `Step_pure/trap-instrs`. -/
theorem spure_trapInstrs {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 26 trapInstrsRule)
    {ws is : List Value} (hne : ws ≠ [] ∨ is ≠ []) (hw : TypedV env valsT (.list ws))
    (his : TypedV env instrsT (.list is)) :
    SPure env (ws ++ ([caseNilV "TRAP"] ++ is)) [caseNilV "TRAP"] := by
  let ρ := VarEnv.empty.bindVals [("val*", .list ws), ("instr*", .list is)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fv : ρ.findVal? "val*" = some (.list ws) := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have ei : EvalExp env ρ (iterPat "instr" "instr*") (.list is) := evalExp_iterPat (by decide) fi
  have hor : EvalExp env ρ (.binE .orOp .boolT
      (.cmpE .neOp .boolT (iterPat "val" "val*") (.listE []))
      (.cmpE .neOp .boolT (iterPat "instr" "instr*") (.listE [])))
      (.bool (decide (ws ≠ [] ∨ is ≠ []))) :=
    evalExp_or (evalExp_ne_nil (evalExp_iterPat (by decide) fv)) (evalExp_ne_nil ei)
  have hd : decide (ws ≠ [] ∨ is ≠ []) = true := decide_eq_true hne
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fv (hw ρ hρ) (QuantsOk.cons fi (his ρ hρ) QuantsOk.nil))
    (evalExp_tup2
      (evalExp_cat (evalExp_valsPat (by decide) fv) (evalExp_cat (evalExp_list1 evalExp_caseNil) ei))
      (evalExp_list1 evalExp_caseNil))
    (prems_one (.ifPr (hd ▸ hor)))

/-- `Step_pure/trap-label`. -/
theorem spure_trapLabel {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 27 trapLabelRule)
    {n : Value} {cont : List Value} (hn : TypedV env nT n)
    (hc : TypedV env instrsT (.list cont)) :
    SPure env [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list [caseNilV "TRAP"]])]
      [caseNilV "TRAP"] := by
  let ρ := VarEnv.empty.bindVals [("n", n), ("instr'*", .list cont)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fn : ρ.findVal? "n" = some n := rfl
  have fc : ρ.findVal? "instr'*" = some (.list cont) := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons fc (hc ρ hρ) QuantsOk.nil))
    (evalExp_tup2
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
        (evalExp_iterPat (by decide) fc) (evalExp_list1 evalExp_caseNil))))
      (evalExp_list1 evalExp_caseNil))
    (fun _ h => nomatch h)

/-- `Step_pure/trap-handler`. -/
theorem spure_trapHandler {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 28 trapHandlerRule)
    {n : Value} {cs : List Value} (hn : TypedV env nT n)
    (hc : TypedV env catchesT (.list cs)) :
    SPure env [.case "HANDLER_%{%}%" (.tuple [n, .list cs, .list [caseNilV "TRAP"]])]
      [caseNilV "TRAP"] := by
  let ρ := VarEnv.empty.bindVals [("n", n), ("catch*", .list cs)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fn : ρ.findVal? "n" = some n := rfl
  have fc : ρ.findVal? "catch*" = some (.list cs) := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons fc (hc ρ hρ) QuantsOk.nil))
    (evalExp_tup2
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
        (evalExp_iterPat (by decide) fc) (evalExp_list1 evalExp_caseNil))))
      (evalExp_list1 evalExp_caseNil))
    (fun _ h => nomatch h)

/-- `Step_pure/trap-frame`. -/
theorem spure_trapFrame {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 29 trapFrameRule)
    {n f : Value} (hn : TypedV env nT n) (hf : TypedV env frameT f) :
    SPure env [.case "FRAME_%{%}%" (.tuple [n, f, .list [caseNilV "TRAP"]])]
      [caseNilV "TRAP"] := by
  let ρ := VarEnv.empty.bindVals [("n", n), ("f", f)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fn : ρ.findVal? "n" = some n := rfl
  have ff : ρ.findVal? "f" = some f := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons ff (hf ρ hρ) QuantsOk.nil))
    (evalExp_tup2
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) (evalExp_var ff)
        (evalExp_list1 evalExp_caseNil))))
      (evalExp_list1 evalExp_caseNil))
    (fun _ h => nomatch h)

end Silmaril.Wasm.SpecTec.Sim
