module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Basic
public import Silmaril.Wasm.SpecTec.Sim.FloatSimd.Defs

/-!
# Family V: the vector rules of `Step_pure`, constructed under the declarative reading

Each lemma builds one of the rules 54–78 of `Step_pure` for arbitrary IL values of the right types,
from the rule's provenance (`HasRuleAt`, `Equiv.ExecVector.HasVectorRules`) and the denotation of
the operator call in its premise (`Equiv.ExecNumeric.Applies`). Nothing here says what an operator
computes; that is the agreement layer (`Sim/FloatSimd/Defs.lean`, `VecAgree`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Vec

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.ExecVector
open Silmaril.SpecTec.Equiv.Execution (caseNilV)

/-! ## Evaluation helpers -/

theorem evalExp_list2 {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v₁ v₂ : Value}
    (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) :
    EvalExp env ρ (.listE [e₁, e₂]) (.list [v₁, v₂]) :=
  evalExp_listE_iff.2 ⟨_, evalExps_cons h₁ (evalExps_cons h₂ evalExps_nil), rfl⟩

theorem evalExp_list3 {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {v₁ v₂ v₃ : Value}
    (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) (h₃ : EvalExp env ρ e₃ v₃) :
    EvalExp env ρ (.listE [e₁, e₂, e₃]) (.list [v₁, v₂, v₃]) :=
  evalExp_listE_iff.2 ⟨_, evalExps_cons h₁ (evalExps_cons h₂
    (evalExps_cons h₃ evalExps_nil)), rfl⟩

theorem evalExp_list4 {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ e₄ : Exp} {v₁ v₂ v₃ v₄ : Value}
    (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) (h₃ : EvalExp env ρ e₃ v₃)
    (h₄ : EvalExp env ρ e₄ v₄) :
    EvalExp env ρ (.listE [e₁, e₂, e₃, e₄]) (.list [v₁, v₂, v₃, v₄]) :=
  evalExp_listE_iff.2 ⟨_, evalExps_cons h₁ (evalExps_cons h₂
    (evalExps_cons h₃ (evalExps_cons h₄ evalExps_nil))), rfl⟩

/-- `V128`, a nullary case. -/
theorem evalExp_v128 {env : Env} {ρ : VarEnv} :
    EvalExp env ρ (.caseE "V128" (.tupE [])) v128V :=
  evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_nil, rfl⟩)

/-- `I32`, a nullary case. -/
theorem evalExp_i32 {env : Env} {ρ : VarEnv} :
    EvalExp env ρ (.caseE "I32" (.tupE [])) Equiv.Execution.i32V :=
  evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_nil, rfl⟩)

/-- `TRAP`, a nullary case. -/
theorem evalExp_trap {env : Env} {ρ : VarEnv} :
    EvalExp env ρ (.caseE "TRAP" (.tupE [])) Equiv.Execution.trapV :=
  evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_nil, rfl⟩)

/-- `VCONST V128 c` for a bound `c`. -/
theorem evalExp_vconst {env : Env} {ρ : VarEnv} {x : IL.Id} {c : Value}
    (h : ρ.findVal? x = some c) :
    EvalExp env ρ (.caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE x])) (vconstV c) :=
  evalExp_case (evalExp_tup2 evalExp_v128 (evalExp_var h))

/-- `CONST I32 c` for a bound `c`. -/
theorem evalExp_constI32 {env : Env} {ρ : VarEnv} {x : IL.Id} {c : Value}
    (h : ρ.findVal? x = some c) :
    EvalExp env ρ (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE x]))
      (Equiv.Execution.constV Equiv.Execution.i32V c) :=
  evalExp_case (evalExp_tup2 evalExp_i32 (evalExp_var h))

/-- An operator instruction `OP (x, y)` over two bound variables. -/
theorem evalExp_op2 {env : Env} {ρ : VarEnv} {mo : MixopS} {x y : IL.Id} {a b : Value}
    (hx : ρ.findVal? x = some a) (hy : ρ.findVal? y = some b) :
    EvalExp env ρ (.caseE mo (.tupE [.varE x, .varE y])) (.case mo (.tuple [a, b])) :=
  evalExp_case (evalExp_tup2 (evalExp_var hx) (evalExp_var hy))

/-- An operator instruction `OP (x, y, z)` over three bound variables. -/
theorem evalExp_op3 {env : Env} {ρ : VarEnv} {mo : MixopS} {x y z : IL.Id} {a b c : Value}
    (hx : ρ.findVal? x = some a) (hy : ρ.findVal? y = some b) (hz : ρ.findVal? z = some c) :
    EvalExp env ρ (.caseE mo (.tupE [.varE x, .varE y, .varE z])) (.case mo (.tuple [a, b, c])) :=
  evalExp_case (evalExp_tup3 (evalExp_var hx) (evalExp_var hy) (evalExp_var hz))

/-! ## The premise shapes -/

/-- A call denotes what `Applies` says, when the scope binds no definition of that name. -/
theorem evalExp_call {env : Env} {ρ : VarEnv} {f : IL.Id} {args : List Arg} {ws : List ArgV}
    {w : Value} (hd : ρ.findDef? f = none) (hx : EvalArgs env ρ args ws)
    (ha : Applies env f ws w) : EvalExp env ρ (.callE f args) w :=
  evalExp_callE_iff.2 ((applies_iff_callDef hd hx).1 ha)

/-- `c <- $f(args)`. -/
theorem evalExp_mem_call {env : Env} {ρ : VarEnv} {c : IL.Id} {cv : Value} {f : IL.Id}
    {args : List Arg} {ws : List ArgV} {L : List Value} (hc : ρ.findVal? c = some cv)
    (hd : ρ.findDef? f = none) (hx : EvalArgs env ρ args ws)
    (ha : Applies env f ws (.list L)) (hm : cv ∈ L) :
    EvalExp env ρ (.memE (.varE c) (.callE f args)) (.bool true) :=
  evalExp_memE_iff.2 ⟨cv, _, evalExp_var hc, evalExp_call hd hx ha,
    by simp [memValue, hm]⟩

/-- `c = $f(args)`. -/
theorem evalExp_eq_call {env : Env} {ρ : VarEnv} {c : IL.Id} {cv : Value} {f : IL.Id}
    {args : List Arg} {ws : List ArgV} (hc : ρ.findVal? c = some cv)
    (hd : ρ.findDef? f = none) (hx : EvalArgs env ρ args ws) (ha : Applies env f ws cv) :
    EvalExp env ρ (.cmpE .eqOp .boolT (.varE c) (.callE f args)) (.bool true) :=
  evalExp_cmpE_iff.2 ⟨cv, cv, evalExp_var hc, evalExp_call hd hx ha, by simp [cmpValues]⟩

/-- `$f(args) = c`. -/
theorem evalExp_call_eq {env : Env} {ρ : VarEnv} {c : IL.Id} {cv : Value} {f : IL.Id}
    {args : List Arg} {ws : List ArgV} (hc : ρ.findVal? c = some cv)
    (hd : ρ.findDef? f = none) (hx : EvalArgs env ρ args ws) (ha : Applies env f ws cv) :
    EvalExp env ρ (.cmpE .eqOp .boolT (.callE f args) (.varE c)) (.bool true) :=
  evalExp_cmpE_iff.2 ⟨cv, cv, evalExp_call hd hx ha, evalExp_var hc, by simp [cmpValues]⟩

/-- `$f(args) = []`. -/
theorem evalExp_call_nil {env : Env} {ρ : VarEnv} {f : IL.Id} {args : List Arg}
    {ws : List ArgV} (hd : ρ.findDef? f = none) (hx : EvalArgs env ρ args ws)
    (ha : Applies env f ws (.list [])) :
    EvalExp env ρ (.cmpE .eqOp .boolT (.callE f args) (.listE [])) (.bool true) :=
  evalExp_cmpE_iff.2 ⟨_, _, evalExp_call hd hx ha,
    evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩, by simp [cmpValues]⟩

/-- One more argument, a bound variable. -/
theorem evalArgs_var {env : Env} {ρ : VarEnv} {x : IL.Id} {v : Value} {rest : List Arg}
    {ws : List ArgV} (h : ρ.findVal? x = some v) (hs : EvalArgs env ρ rest ws) :
    EvalArgs env ρ (.expA (.varE x) :: rest) (.val v :: ws) :=
  Equiv.evalArgs_cons (evalExp_var h) hs

/-- One more argument, `V128`. -/
theorem evalArgs_v128 {env : Env} {ρ : VarEnv} {rest : List Arg} {ws : List ArgV}
    (hs : EvalArgs env ρ rest ws) :
    EvalArgs env ρ (.expA (.caseE "V128" (.tupE [])) :: rest) (.val v128V :: ws) :=
  Equiv.evalArgs_cons evalExp_v128 hs

/-! ## The rules -/

/-- The scope of a rule instance binds no definition. -/
theorem findDef_bindVals (σ : List (IL.Id × Value)) (f : IL.Id) :
    (VarEnv.empty.bindVals σ).findDef? f = none := rfl

/-- `Step_pure/vvunop` (rule 54). -/
theorem spure_vvunop {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 54 vvunopRule)
    {c₁ op c : Value} {L : List Value} (hc₁ : TypedV env vecT c₁)
    (hop : TypedV env (.varT "vvunop" []) op) (hc : TypedV env vecT c)
    (ha : Applies env "vvunop_" [.val v128V, .val op, .val c₁] (.list L)) (hm : c ∈ L) :
    SPure env [vconstV c₁, .case "VVUNOP" (.tuple [v128V, op])] [vconstV c] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("vvunop", op), ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "vvunop" = some op := rfl
  have f3 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "vvunop" (.varT "vvunop" []), .expP "c" vecT] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hop ρ hρ) (QuantsOk.cons f3 (hc ρ hρ)
      QuantsOk.nil))
  have hx : EvalArgs env ρ [.expA (.caseE "V128" (.tupE [])), .expA (.varE "vvunop"),
      .expA (.varE "c_1")] [.val v128V, .val op, .val c₁] :=
    evalArgs_v128 (evalArgs_var f2 (evalArgs_var f1 Equiv.evalArgs_nil))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list2 (evalExp_vconst f1)
        (evalExp_case (evalExp_tup2 evalExp_v128 (evalExp_var f2))))
      (evalExp_list1 (evalExp_vconst f3)))
    (prems_one (.ifPr (evalExp_mem_call f3 rfl hx ha hm)))

/-- `Step_pure/vvbinop` (rule 55). -/
theorem spure_vvbinop {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 55 vvbinopRule)
    {c₁ c₂ op c : Value} {L : List Value} (hc₁ : TypedV env vecT c₁) (hc₂ : TypedV env vecT c₂)
    (hop : TypedV env (.varT "vvbinop" []) op) (hc : TypedV env vecT c)
    (ha : Applies env "vvbinop_" [.val v128V, .val op, .val c₁, .val c₂] (.list L))
    (hm : c ∈ L) :
    SPure env [vconstV c₁, vconstV c₂, .case "VVBINOP" (.tuple [v128V, op])] [vconstV c] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("c_2", c₂), ("vvbinop", op), ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "c_2" = some c₂ := rfl
  have f3 : ρ.findVal? "vvbinop" = some op := rfl
  have f4 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "c_2" vecT,
      .expP "vvbinop" (.varT "vvbinop" []), .expP "c" vecT] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hc₂ ρ hρ) (QuantsOk.cons f3 (hop ρ hρ)
      (QuantsOk.cons f4 (hc ρ hρ) QuantsOk.nil)))
  have hx : EvalArgs env ρ [.expA (.caseE "V128" (.tupE [])), .expA (.varE "vvbinop"),
      .expA (.varE "c_1"), .expA (.varE "c_2")] [.val v128V, .val op, .val c₁, .val c₂] :=
    evalArgs_v128 (evalArgs_var f3 (evalArgs_var f1 (evalArgs_var f2 Equiv.evalArgs_nil)))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list3 (evalExp_vconst f1) (evalExp_vconst f2)
        (evalExp_case (evalExp_tup2 evalExp_v128 (evalExp_var f3))))
      (evalExp_list1 (evalExp_vconst f4)))
    (prems_one (.ifPr (evalExp_mem_call f4 rfl hx ha hm)))

/-- `Step_pure/vvternop` (rule 56). -/
theorem spure_vvternop {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 56 vvternopRule)
    {c₁ c₂ c₃ op c : Value} {L : List Value} (hc₁ : TypedV env vecT c₁)
    (hc₂ : TypedV env vecT c₂) (hc₃ : TypedV env vecT c₃)
    (hop : TypedV env (.varT "vvternop" []) op) (hc : TypedV env vecT c)
    (ha : Applies env "vvternop_" [.val v128V, .val op, .val c₁, .val c₂, .val c₃] (.list L))
    (hm : c ∈ L) :
    SPure env [vconstV c₁, vconstV c₂, vconstV c₃, .case "VVTERNOP" (.tuple [v128V, op])]
      [vconstV c] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("c_2", c₂), ("c_3", c₃), ("vvternop", op),
    ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "c_2" = some c₂ := rfl
  have f3 : ρ.findVal? "c_3" = some c₃ := rfl
  have f4 : ρ.findVal? "vvternop" = some op := rfl
  have f5 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "c_2" vecT, .expP "c_3" vecT,
      .expP "vvternop" (.varT "vvternop" []), .expP "c" vecT] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hc₂ ρ hρ) (QuantsOk.cons f3 (hc₃ ρ hρ)
      (QuantsOk.cons f4 (hop ρ hρ) (QuantsOk.cons f5 (hc ρ hρ) QuantsOk.nil))))
  have hx : EvalArgs env ρ [.expA (.caseE "V128" (.tupE [])), .expA (.varE "vvternop"),
      .expA (.varE "c_1"), .expA (.varE "c_2"), .expA (.varE "c_3")]
      [.val v128V, .val op, .val c₁, .val c₂, .val c₃] :=
    evalArgs_v128 (evalArgs_var f4 (evalArgs_var f1 (evalArgs_var f2 (evalArgs_var f3
      Equiv.evalArgs_nil))))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list4 (evalExp_vconst f1) (evalExp_vconst f2) (evalExp_vconst f3)
        (evalExp_case (evalExp_tup2 evalExp_v128 (evalExp_var f4))))
      (evalExp_list1 (evalExp_vconst f5)))
    (prems_one (.ifPr (evalExp_mem_call f5 rfl hx ha hm)))

/-- `Step_pure/vunop-val` (rule 58). -/
theorem spure_vunopVal {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 58 vunopValRule)
    {c₁ sh op c : Value} {L : List Value} (hc₁ : TypedV env vecT c₁) (hsh : TypedV env shapeT sh)
    (hop : TypedDep env "sh" sh (.varT "vunop_" [.expA (.varE "sh")]) op)
    (hc : TypedV env vecT c) (ha : Applies env "vunop_" [.val sh, .val op, .val c₁] (.list L))
    (hm : c ∈ L) :
    SPure env [vconstV c₁, vunopV sh op] [vconstV c] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("sh", sh), ("vunop", op), ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "sh" = some sh := rfl
  have f3 : ρ.findVal? "vunop" = some op := rfl
  have f4 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "sh" shapeT,
      .expP "vunop" (.varT "vunop_" [.expA (.varE "sh")]), .expP "c" vecT] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hsh ρ hρ) (QuantsOk.cons f3 (hop ρ hρ f2)
      (QuantsOk.cons f4 (hc ρ hρ) QuantsOk.nil)))
  have hx : EvalArgs env ρ [.expA (.varE "sh"), .expA (.varE "vunop"), .expA (.varE "c_1")]
      [.val sh, .val op, .val c₁] :=
    evalArgs_var f2 (evalArgs_var f3 (evalArgs_var f1 Equiv.evalArgs_nil))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list2 (evalExp_vconst f1) (evalExp_op2 f2 f3))
      (evalExp_list1 (evalExp_vconst f4)))
    (prems_one (.ifPr (evalExp_mem_call f4 rfl hx ha hm)))

/-- `Step_pure/vunop-trap` (rule 59). -/
theorem spure_vunopTrap {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 59 vunopTrapRule)
    {c₁ sh op : Value} (hc₁ : TypedV env vecT c₁) (hsh : TypedV env shapeT sh)
    (hop : TypedDep env "sh" sh (opT "vunop_" "sh") op)
    (ha : Applies env "vunop_" [.val sh, .val op, .val c₁] (.list [])) :
    SPure env [vconstV c₁, vunopV sh op] [Equiv.Execution.trapV] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("sh", sh), ("vunop", op)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "sh" = some sh := rfl
  have f3 : ρ.findVal? "vunop" = some op := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "sh" shapeT,
      .expP "vunop" (opT "vunop_" "sh")] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hsh ρ hρ) (QuantsOk.cons f3 (hop ρ hρ f2)
      QuantsOk.nil))
  have hx : EvalArgs env ρ [.expA (.varE "sh"), .expA (.varE "vunop"), .expA (.varE "c_1")]
      [.val sh, .val op, .val c₁] :=
    evalArgs_var f2 (evalArgs_var f3 (evalArgs_var f1 Equiv.evalArgs_nil))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list2 (evalExp_vconst f1) (evalExp_op2 f2 f3))
      (evalExp_list1 evalExp_trap))
    (prems_one (.ifPr (evalExp_call_nil rfl hx ha)))

/-- `Step_pure/vbinop-val` (rule 60). -/
theorem spure_vbinopVal {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 60 vbinopValRule)
    {c₁ c₂ sh op c : Value} {L : List Value} (hc₁ : TypedV env vecT c₁)
    (hc₂ : TypedV env vecT c₂) (hsh : TypedV env shapeT sh)
    (hop : TypedDep env "sh" sh (opT "vbinop_" "sh") op) (hc : TypedV env vecT c)
    (ha : Applies env "vbinop_" [.val sh, .val op, .val c₁, .val c₂] (.list L)) (hm : c ∈ L) :
    SPure env [vconstV c₁, vconstV c₂, vbinopV sh op] [vconstV c] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("c_2", c₂), ("sh", sh), ("vbinop", op),
    ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "c_2" = some c₂ := rfl
  have f3 : ρ.findVal? "sh" = some sh := rfl
  have f4 : ρ.findVal? "vbinop" = some op := rfl
  have f5 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "c_2" vecT, .expP "sh" shapeT,
      .expP "vbinop" (opT "vbinop_" "sh"), .expP "c" vecT] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hc₂ ρ hρ) (QuantsOk.cons f3 (hsh ρ hρ)
      (QuantsOk.cons f4 (hop ρ hρ f3) (QuantsOk.cons f5 (hc ρ hρ) QuantsOk.nil))))
  have hx : EvalArgs env ρ [.expA (.varE "sh"), .expA (.varE "vbinop"), .expA (.varE "c_1"),
      .expA (.varE "c_2")] [.val sh, .val op, .val c₁, .val c₂] :=
    evalArgs_var f3 (evalArgs_var f4 (evalArgs_var f1 (evalArgs_var f2 Equiv.evalArgs_nil)))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list3 (evalExp_vconst f1) (evalExp_vconst f2) (evalExp_op2 f3 f4))
      (evalExp_list1 (evalExp_vconst f5)))
    (prems_one (.ifPr (evalExp_mem_call f5 rfl hx ha hm)))

/-- `Step_pure/vbinop-trap` (rule 61). -/
theorem spure_vbinopTrap {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 61 vbinopTrapRule)
    {c₁ c₂ sh op : Value} (hc₁ : TypedV env vecT c₁) (hc₂ : TypedV env vecT c₂)
    (hsh : TypedV env shapeT sh) (hop : TypedDep env "sh" sh (opT "vbinop_" "sh") op)
    (ha : Applies env "vbinop_" [.val sh, .val op, .val c₁, .val c₂] (.list [])) :
    SPure env [vconstV c₁, vconstV c₂, vbinopV sh op] [Equiv.Execution.trapV] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("c_2", c₂), ("sh", sh), ("vbinop", op)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "c_2" = some c₂ := rfl
  have f3 : ρ.findVal? "sh" = some sh := rfl
  have f4 : ρ.findVal? "vbinop" = some op := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "c_2" vecT, .expP "sh" shapeT,
      .expP "vbinop" (opT "vbinop_" "sh")] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hc₂ ρ hρ) (QuantsOk.cons f3 (hsh ρ hρ)
      (QuantsOk.cons f4 (hop ρ hρ f3) QuantsOk.nil)))
  have hx : EvalArgs env ρ [.expA (.varE "sh"), .expA (.varE "vbinop"), .expA (.varE "c_1"),
      .expA (.varE "c_2")] [.val sh, .val op, .val c₁, .val c₂] :=
    evalArgs_var f3 (evalArgs_var f4 (evalArgs_var f1 (evalArgs_var f2 Equiv.evalArgs_nil)))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list3 (evalExp_vconst f1) (evalExp_vconst f2) (evalExp_op2 f3 f4))
      (evalExp_list1 evalExp_trap))
    (prems_one (.ifPr (evalExp_call_nil rfl hx ha)))

/-- `Step_pure/vternop-val` (rule 62). -/
theorem spure_vternopVal {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 62 vternopValRule)
    {c₁ c₂ c₃ sh op c : Value} {L : List Value} (hc₁ : TypedV env vecT c₁)
    (hc₂ : TypedV env vecT c₂) (hc₃ : TypedV env vecT c₃) (hsh : TypedV env shapeT sh)
    (hop : TypedDep env "sh" sh (opT "vternop_" "sh") op) (hc : TypedV env vecT c)
    (ha : Applies env "vternop_" [.val sh, .val op, .val c₁, .val c₂, .val c₃] (.list L))
    (hm : c ∈ L) :
    SPure env [vconstV c₁, vconstV c₂, vconstV c₃, vternopV sh op] [vconstV c] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("c_2", c₂), ("c_3", c₃), ("sh", sh),
    ("vternop", op), ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "c_2" = some c₂ := rfl
  have f3 : ρ.findVal? "c_3" = some c₃ := rfl
  have f4 : ρ.findVal? "sh" = some sh := rfl
  have f5 : ρ.findVal? "vternop" = some op := rfl
  have f6 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "c_2" vecT, .expP "c_3" vecT,
      .expP "sh" shapeT, .expP "vternop" (opT "vternop_" "sh"), .expP "c" vecT] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hc₂ ρ hρ) (QuantsOk.cons f3 (hc₃ ρ hρ)
      (QuantsOk.cons f4 (hsh ρ hρ) (QuantsOk.cons f5 (hop ρ hρ f4)
      (QuantsOk.cons f6 (hc ρ hρ) QuantsOk.nil)))))
  have hx : EvalArgs env ρ [.expA (.varE "sh"), .expA (.varE "vternop"), .expA (.varE "c_1"),
      .expA (.varE "c_2"), .expA (.varE "c_3")] [.val sh, .val op, .val c₁, .val c₂, .val c₃] :=
    evalArgs_var f4 (evalArgs_var f5 (evalArgs_var f1 (evalArgs_var f2 (evalArgs_var f3
      Equiv.evalArgs_nil))))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list4 (evalExp_vconst f1) (evalExp_vconst f2) (evalExp_vconst f3)
        (evalExp_op2 f4 f5))
      (evalExp_list1 (evalExp_vconst f6)))
    (prems_one (.ifPr (evalExp_mem_call f6 rfl hx ha hm)))

/-- `Step_pure/vternop-trap` (rule 63). -/
theorem spure_vternopTrap {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 63 vternopTrapRule)
    {c₁ c₂ c₃ sh op : Value} (hc₁ : TypedV env vecT c₁) (hc₂ : TypedV env vecT c₂)
    (hc₃ : TypedV env vecT c₃) (hsh : TypedV env shapeT sh)
    (hop : TypedDep env "sh" sh (opT "vternop_" "sh") op)
    (ha : Applies env "vternop_" [.val sh, .val op, .val c₁, .val c₂, .val c₃] (.list [])) :
    SPure env [vconstV c₁, vconstV c₂, vconstV c₃, vternopV sh op] [Equiv.Execution.trapV] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("c_2", c₂), ("c_3", c₃), ("sh", sh),
    ("vternop", op)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "c_2" = some c₂ := rfl
  have f3 : ρ.findVal? "c_3" = some c₃ := rfl
  have f4 : ρ.findVal? "sh" = some sh := rfl
  have f5 : ρ.findVal? "vternop" = some op := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "c_2" vecT, .expP "c_3" vecT,
      .expP "sh" shapeT, .expP "vternop" (opT "vternop_" "sh")] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hc₂ ρ hρ) (QuantsOk.cons f3 (hc₃ ρ hρ)
      (QuantsOk.cons f4 (hsh ρ hρ) (QuantsOk.cons f5 (hop ρ hρ f4) QuantsOk.nil))))
  have hx : EvalArgs env ρ [.expA (.varE "sh"), .expA (.varE "vternop"), .expA (.varE "c_1"),
      .expA (.varE "c_2"), .expA (.varE "c_3")] [.val sh, .val op, .val c₁, .val c₂, .val c₃] :=
    evalArgs_var f4 (evalArgs_var f5 (evalArgs_var f1 (evalArgs_var f2 (evalArgs_var f3
      Equiv.evalArgs_nil))))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list4 (evalExp_vconst f1) (evalExp_vconst f2) (evalExp_vconst f3)
        (evalExp_op2 f4 f5))
      (evalExp_list1 evalExp_trap))
    (prems_one (.ifPr (evalExp_call_nil rfl hx ha)))

/-- `Step_pure/vrelop` (rule 65). -/
theorem spure_vrelop {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 65 vrelopRule)
    {c₁ c₂ sh op c : Value} (hc₁ : TypedV env vecT c₁) (hc₂ : TypedV env vecT c₂)
    (hsh : TypedV env shapeT sh) (hop : TypedDep env "sh" sh (opT "vrelop_" "sh") op)
    (hc : TypedV env vecT c) (ha : Applies env "vrelop_" [.val sh, .val op, .val c₁, .val c₂] c) :
    SPure env [vconstV c₁, vconstV c₂, .case "VRELOP" (.tuple [sh, op])] [vconstV c] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("c_2", c₂), ("sh", sh), ("vrelop", op),
    ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "c_2" = some c₂ := rfl
  have f3 : ρ.findVal? "sh" = some sh := rfl
  have f4 : ρ.findVal? "vrelop" = some op := rfl
  have f5 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "c_2" vecT, .expP "sh" shapeT,
      .expP "vrelop" (opT "vrelop_" "sh"), .expP "c" vecT] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hc₂ ρ hρ) (QuantsOk.cons f3 (hsh ρ hρ)
      (QuantsOk.cons f4 (hop ρ hρ f3) (QuantsOk.cons f5 (hc ρ hρ) QuantsOk.nil))))
  have hx : EvalArgs env ρ [.expA (.varE "sh"), .expA (.varE "vrelop"), .expA (.varE "c_1"),
      .expA (.varE "c_2")] [.val sh, .val op, .val c₁, .val c₂] :=
    evalArgs_var f3 (evalArgs_var f4 (evalArgs_var f1 (evalArgs_var f2 Equiv.evalArgs_nil)))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list3 (evalExp_vconst f1) (evalExp_vconst f2) (evalExp_op2 f3 f4))
      (evalExp_list1 (evalExp_vconst f5)))
    (prems_one (.ifPr (evalExp_eq_call f5 rfl hx ha)))

/-- `Step_pure/vshiftop` (rule 66). -/
theorem spure_vshiftop {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 66 vshiftopRule)
    {c₁ i sh op c : Value} (hc₁ : TypedV env vecT c₁) (hi : TypedV env i32T i)
    (hsh : TypedV env ishapeT sh) (hop : TypedDep env "sh" sh (opT "vshiftop_" "sh") op)
    (hc : TypedV env vecT c) (ha : Applies env "vshiftop_" [.val sh, .val op, .val c₁, .val i] c) :
    SPure env [vconstV c₁, Equiv.Execution.constV Equiv.Execution.i32V i,
      .case "VSHIFTOP" (.tuple [sh, op])]
      [vconstV c] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("i", i), ("sh", sh), ("vshiftop", op), ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "i" = some i := rfl
  have f3 : ρ.findVal? "sh" = some sh := rfl
  have f4 : ρ.findVal? "vshiftop" = some op := rfl
  have f5 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "i" i32T, .expP "sh" ishapeT,
      .expP "vshiftop" (opT "vshiftop_" "sh"), .expP "c" vecT] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hi ρ hρ) (QuantsOk.cons f3 (hsh ρ hρ)
      (QuantsOk.cons f4 (hop ρ hρ f3) (QuantsOk.cons f5 (hc ρ hρ) QuantsOk.nil))))
  have hx : EvalArgs env ρ [.expA (.varE "sh"), .expA (.varE "vshiftop"), .expA (.varE "c_1"),
      .expA (.varE "i")] [.val sh, .val op, .val c₁, .val i] :=
    evalArgs_var f3 (evalArgs_var f4 (evalArgs_var f1 (evalArgs_var f2 Equiv.evalArgs_nil)))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list3 (evalExp_vconst f1) (evalExp_constI32 f2) (evalExp_op2 f3 f4))
      (evalExp_list1 (evalExp_vconst f5)))
    (prems_one (.ifPr (evalExp_eq_call f5 rfl hx ha)))

/-- `Step_pure/vbitmask` (rule 67). -/
theorem spure_vbitmask {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 67 vbitmaskRule)
    {c₁ sh c : Value} (hc₁ : TypedV env vecT c₁) (hsh : TypedV env ishapeT sh)
    (hc : TypedV env i32T c) (ha : Applies env "vbitmaskop_" [.val sh, .val c₁] c) :
    SPure env [vconstV c₁, .case "VBITMASK" sh]
      [Equiv.Execution.constV Equiv.Execution.i32V c] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("sh", sh), ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "sh" = some sh := rfl
  have f3 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "sh" ishapeT, .expP "c" i32T] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hsh ρ hρ) (QuantsOk.cons f3 (hc ρ hρ)
      QuantsOk.nil))
  have hx : EvalArgs env ρ [.expA (.varE "sh"), .expA (.varE "c_1")] [.val sh, .val c₁] :=
    evalArgs_var f2 (evalArgs_var f1 Equiv.evalArgs_nil)
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list2 (evalExp_vconst f1) (evalExp_case (evalExp_var f2)))
      (evalExp_list1 (evalExp_constI32 f3)))
    (prems_one (.ifPr (evalExp_eq_call f3 rfl hx ha)))

/-- `Step_pure/vswizzlop` (rule 68). -/
theorem spure_vswizzlop {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 68 vswizzlopRule)
    {c₁ c₂ sh op c : Value} (hc₁ : TypedV env vecT c₁) (hc₂ : TypedV env vecT c₂)
    (hsh : TypedV env bshapeT sh) (hop : TypedDep env "sh" sh (opT "vswizzlop_" "sh") op)
    (hc : TypedV env vecT c)
    (ha : Applies env "vswizzlop_" [.val sh, .val op, .val c₁, .val c₂] c) :
    SPure env [vconstV c₁, vconstV c₂, .case "VSWIZZLOP" (.tuple [sh, op])] [vconstV c] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("c_2", c₂), ("sh", sh), ("swizzlop", op),
    ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "c_2" = some c₂ := rfl
  have f3 : ρ.findVal? "sh" = some sh := rfl
  have f4 : ρ.findVal? "swizzlop" = some op := rfl
  have f5 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "c_2" vecT, .expP "sh" bshapeT,
      .expP "swizzlop" (opT "vswizzlop_" "sh"), .expP "c" vecT] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hc₂ ρ hρ) (QuantsOk.cons f3 (hsh ρ hρ)
      (QuantsOk.cons f4 (hop ρ hρ f3) (QuantsOk.cons f5 (hc ρ hρ) QuantsOk.nil))))
  have hx : EvalArgs env ρ [.expA (.varE "sh"), .expA (.varE "swizzlop"), .expA (.varE "c_1"),
      .expA (.varE "c_2")] [.val sh, .val op, .val c₁, .val c₂] :=
    evalArgs_var f3 (evalArgs_var f4 (evalArgs_var f1 (evalArgs_var f2 Equiv.evalArgs_nil)))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list3 (evalExp_vconst f1) (evalExp_vconst f2) (evalExp_op2 f3 f4))
      (evalExp_list1 (evalExp_vconst f5)))
    (prems_one (.ifPr (evalExp_eq_call f5 rfl hx ha)))

/-- `Step_pure/vshuffle` (rule 69). -/
theorem spure_vshuffle {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 69 vshuffleRule)
    {c₁ c₂ sh c : Value} {is : List Value} (hc₁ : TypedV env vecT c₁)
    (hc₂ : TypedV env vecT c₂) (hsh : TypedV env bshapeT sh)
    (his : TypedV env laneidxsT (.list is)) (hc : TypedV env vecT c)
    (ha : Applies env "vshufflop_" [.val sh, .val (.list is), .val c₁, .val c₂] c) :
    SPure env [vconstV c₁, vconstV c₂, .case "VSHUFFLE" (.tuple [sh, .list is])]
      [vconstV c] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("c_2", c₂), ("sh", sh), ("i*", .list is),
    ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "c_2" = some c₂ := rfl
  have f3 : ρ.findVal? "sh" = some sh := rfl
  have f4 : ρ.findVal? "i*" = some (.list is) := rfl
  have f5 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "c_2" vecT, .expP "sh" bshapeT,
      .expP "i*" laneidxsT, .expP "c" vecT] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hc₂ ρ hρ) (QuantsOk.cons f3 (hsh ρ hρ)
      (QuantsOk.cons f4 (his ρ hρ) (QuantsOk.cons f5 (hc ρ hρ) QuantsOk.nil))))
  have ei : EvalExp env ρ (Equiv.Execution.iterPat "i" "i*") (.list is) :=
    Equiv.Execution.evalExp_iterPat (by decide) f4
  have hx : EvalArgs env ρ [.expA (.varE "sh"), .expA (Equiv.Execution.iterPat "i" "i*"),
      .expA (.varE "c_1"), .expA (.varE "c_2")] [.val sh, .val (.list is), .val c₁, .val c₂] :=
    evalArgs_var f3 (Equiv.evalArgs_cons ei (evalArgs_var f1 (evalArgs_var f2
      Equiv.evalArgs_nil)))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list3 (evalExp_vconst f1) (evalExp_vconst f2)
        (evalExp_case (evalExp_tup2 (evalExp_var f3) ei)))
      (evalExp_list1 (evalExp_vconst f5)))
    (prems_one (.ifPr (evalExp_eq_call f5 rfl hx ha)))

/-- `Step_pure/vextunop` (rule 74). -/
theorem spure_vextunop {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 74 vextunopRule)
    {c₁ sh₂ sh₁ op c : Value} (hc₁ : TypedV env vecT c₁) (hsh₂ : TypedV env ishapeT sh₂)
    (hsh₁ : TypedV env ishapeT sh₁)
    (hop : TypedDep2 env "sh_1" sh₁ "sh_2" sh₂ (opT2 "vextunop__") op) (hc : TypedV env vecT c)
    (ha : Applies env "vextunop__" [.val sh₁, .val sh₂, .val op, .val c₁] c) :
    SPure env [vconstV c₁, .case "VEXTUNOP" (.tuple [sh₂, sh₁, op])] [vconstV c] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("sh_2", sh₂), ("sh_1", sh₁), ("vextunop", op),
    ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "sh_2" = some sh₂ := rfl
  have f3 : ρ.findVal? "sh_1" = some sh₁ := rfl
  have f4 : ρ.findVal? "vextunop" = some op := rfl
  have f5 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "sh_2" ishapeT, .expP "sh_1" ishapeT,
      .expP "vextunop" (opT2 "vextunop__"), .expP "c" vecT] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hsh₂ ρ hρ) (QuantsOk.cons f3 (hsh₁ ρ hρ)
      (QuantsOk.cons f4 (hop ρ hρ f3 f2) (QuantsOk.cons f5 (hc ρ hρ) QuantsOk.nil))))
  have hx : EvalArgs env ρ [.expA (.varE "sh_1"), .expA (.varE "sh_2"),
      .expA (.varE "vextunop"), .expA (.varE "c_1")] [.val sh₁, .val sh₂, .val op, .val c₁] :=
    evalArgs_var f3 (evalArgs_var f2 (evalArgs_var f4 (evalArgs_var f1 Equiv.evalArgs_nil)))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list2 (evalExp_vconst f1) (evalExp_op3 f2 f3 f4))
      (evalExp_list1 (evalExp_vconst f5)))
    (prems_one (.ifPr (evalExp_call_eq f5 rfl hx ha)))

/-- `Step_pure/vextbinop` (rule 75). -/
theorem spure_vextbinop {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 75 vextbinopRule)
    {c₁ c₂ sh₂ sh₁ op c : Value} (hc₁ : TypedV env vecT c₁) (hc₂ : TypedV env vecT c₂)
    (hsh₂ : TypedV env ishapeT sh₂) (hsh₁ : TypedV env ishapeT sh₁)
    (hop : TypedDep2 env "sh_1" sh₁ "sh_2" sh₂ (opT2 "vextbinop__") op) (hc : TypedV env vecT c)
    (ha : Applies env "vextbinop__" [.val sh₁, .val sh₂, .val op, .val c₁, .val c₂] c) :
    SPure env [vconstV c₁, vconstV c₂, .case "VEXTBINOP" (.tuple [sh₂, sh₁, op])]
      [vconstV c] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("c_2", c₂), ("sh_2", sh₂), ("sh_1", sh₁),
    ("vextbinop", op), ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "c_2" = some c₂ := rfl
  have f3 : ρ.findVal? "sh_2" = some sh₂ := rfl
  have f4 : ρ.findVal? "sh_1" = some sh₁ := rfl
  have f5 : ρ.findVal? "vextbinop" = some op := rfl
  have f6 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "c_2" vecT, .expP "sh_2" ishapeT,
      .expP "sh_1" ishapeT, .expP "vextbinop" (opT2 "vextbinop__"), .expP "c" vecT] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hc₂ ρ hρ) (QuantsOk.cons f3 (hsh₂ ρ hρ)
      (QuantsOk.cons f4 (hsh₁ ρ hρ) (QuantsOk.cons f5 (hop ρ hρ f4 f3)
      (QuantsOk.cons f6 (hc ρ hρ) QuantsOk.nil)))))
  have hx : EvalArgs env ρ [.expA (.varE "sh_1"), .expA (.varE "sh_2"),
      .expA (.varE "vextbinop"), .expA (.varE "c_1"), .expA (.varE "c_2")]
      [.val sh₁, .val sh₂, .val op, .val c₁, .val c₂] :=
    evalArgs_var f4 (evalArgs_var f3 (evalArgs_var f5 (evalArgs_var f1 (evalArgs_var f2
      Equiv.evalArgs_nil))))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list3 (evalExp_vconst f1) (evalExp_vconst f2) (evalExp_op3 f3 f4 f5))
      (evalExp_list1 (evalExp_vconst f6)))
    (prems_one (.ifPr (evalExp_call_eq f6 rfl hx ha)))

/-- `Step_pure/vextternop` (rule 76). -/
theorem spure_vextternop {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 76 vextternopRule)
    {c₁ c₂ c₃ sh₂ sh₁ op c : Value} (hc₁ : TypedV env vecT c₁) (hc₂ : TypedV env vecT c₂)
    (hc₃ : TypedV env vecT c₃) (hsh₂ : TypedV env ishapeT sh₂) (hsh₁ : TypedV env ishapeT sh₁)
    (hop : TypedDep2 env "sh_1" sh₁ "sh_2" sh₂ (opT2 "vextternop__") op)
    (hc : TypedV env vecT c)
    (ha : Applies env "vextternop__" [.val sh₁, .val sh₂, .val op, .val c₁, .val c₂, .val c₃] c) :
    SPure env [vconstV c₁, vconstV c₂, vconstV c₃, .case "VEXTTERNOP" (.tuple [sh₂, sh₁, op])]
      [vconstV c] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("c_2", c₂), ("c_3", c₃), ("sh_2", sh₂),
    ("sh_1", sh₁), ("vextternop", op), ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "c_2" = some c₂ := rfl
  have f3 : ρ.findVal? "c_3" = some c₃ := rfl
  have f4 : ρ.findVal? "sh_2" = some sh₂ := rfl
  have f5 : ρ.findVal? "sh_1" = some sh₁ := rfl
  have f6 : ρ.findVal? "vextternop" = some op := rfl
  have f7 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "c_2" vecT, .expP "c_3" vecT,
      .expP "sh_2" ishapeT, .expP "sh_1" ishapeT, .expP "vextternop" (opT2 "vextternop__"),
      .expP "c" vecT] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hc₂ ρ hρ) (QuantsOk.cons f3 (hc₃ ρ hρ)
      (QuantsOk.cons f4 (hsh₂ ρ hρ) (QuantsOk.cons f5 (hsh₁ ρ hρ)
      (QuantsOk.cons f6 (hop ρ hρ f5 f4) (QuantsOk.cons f7 (hc ρ hρ) QuantsOk.nil))))))
  have hx : EvalArgs env ρ [.expA (.varE "sh_1"), .expA (.varE "sh_2"),
      .expA (.varE "vextternop"), .expA (.varE "c_1"), .expA (.varE "c_2"), .expA (.varE "c_3")]
      [.val sh₁, .val sh₂, .val op, .val c₁, .val c₂, .val c₃] :=
    evalArgs_var f5 (evalArgs_var f4 (evalArgs_var f6 (evalArgs_var f1 (evalArgs_var f2
      (evalArgs_var f3 Equiv.evalArgs_nil)))))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list4 (evalExp_vconst f1) (evalExp_vconst f2) (evalExp_vconst f3)
        (evalExp_op3 f4 f5 f6))
      (evalExp_list1 (evalExp_vconst f7)))
    (prems_one (.ifPr (evalExp_call_eq f7 rfl hx ha)))

/-- `Step_pure/vnarrow` (rule 77). The premise reads the shapes under their `ishape` wrappers
(`sh!%.0`). -/
theorem spure_vnarrow {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 77 vnarrowRule)
    {c₁ c₂ s₂ s₁ sx c : Value} (hc₁ : TypedV env vecT c₁) (hc₂ : TypedV env vecT c₂)
    (hsh₂ : TypedV env ishapeT (.case "%" (.tuple [s₂])))
    (hsh₁ : TypedV env ishapeT (.case "%" (.tuple [s₁])))
    (hsx : TypedV env (.varT "sx" []) sx) (hc : TypedV env vecT c)
    (ha : Applies env "vnarrowop__" [.val s₁, .val s₂, .val sx, .val c₁, .val c₂] c) :
    SPure env [vconstV c₁, vconstV c₂, .case "VNARROW" (.tuple [.case "%" (.tuple [s₂]),
      .case "%" (.tuple [s₁]), sx])] [vconstV c] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("c_2", c₂), ("sh_2", .case "%" (.tuple [s₂])),
    ("sh_1", .case "%" (.tuple [s₁])), ("sx", sx), ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "c_2" = some c₂ := rfl
  have f3 : ρ.findVal? "sh_2" = some (.case "%" (.tuple [s₂])) := rfl
  have f4 : ρ.findVal? "sh_1" = some (.case "%" (.tuple [s₁])) := rfl
  have f5 : ρ.findVal? "sx" = some sx := rfl
  have f6 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "c_2" vecT, .expP "sh_2" ishapeT,
      .expP "sh_1" ishapeT, .expP "sx" (.varT "sx" []), .expP "c" vecT] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hc₂ ρ hρ) (QuantsOk.cons f3 (hsh₂ ρ hρ)
      (QuantsOk.cons f4 (hsh₁ ρ hρ) (QuantsOk.cons f5 (hsx ρ hρ)
      (QuantsOk.cons f6 (hc ρ hρ) QuantsOk.nil)))))
  have e1 : EvalExp env ρ (.projE (.uncaseE (.varE "sh_1") "%") 0) s₁ :=
    evalExp_pctFst_iff.2 ⟨[], f4⟩
  have e2 : EvalExp env ρ (.projE (.uncaseE (.varE "sh_2") "%") 0) s₂ :=
    evalExp_pctFst_iff.2 ⟨[], f3⟩
  have hx : EvalArgs env ρ [.expA (.projE (.uncaseE (.varE "sh_1") "%") 0),
      .expA (.projE (.uncaseE (.varE "sh_2") "%") 0), .expA (.varE "sx"), .expA (.varE "c_1"),
      .expA (.varE "c_2")] [.val s₁, .val s₂, .val sx, .val c₁, .val c₂] :=
    Equiv.evalArgs_cons e1 (Equiv.evalArgs_cons e2 (evalArgs_var f5 (evalArgs_var f1
      (evalArgs_var f2 Equiv.evalArgs_nil))))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list3 (evalExp_vconst f1) (evalExp_vconst f2) (evalExp_op3 f3 f4 f5))
      (evalExp_list1 (evalExp_vconst f6)))
    (prems_one (.ifPr (evalExp_eq_call f6 rfl hx ha)))

/-- `Step_pure/vcvtop` (rule 78). -/
theorem spure_vcvtop {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 78 vcvtopRule)
    {c₁ sh₂ sh₁ op c : Value} (hc₁ : TypedV env vecT c₁) (hsh₂ : TypedV env shapeT sh₂)
    (hsh₁ : TypedV env shapeT sh₁)
    (hop : TypedDep2 env "sh_1" sh₁ "sh_2" sh₂ (opT2 "vcvtop__") op) (hc : TypedV env vecT c)
    (ha : Applies env "vcvtop__" [.val sh₁, .val sh₂, .val op, .val c₁] c) :
    SPure env [vconstV c₁, .case "VCVTOP" (.tuple [sh₂, sh₁, op])] [vconstV c] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("sh_2", sh₂), ("sh_1", sh₁), ("vcvtop", op),
    ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "sh_2" = some sh₂ := rfl
  have f3 : ρ.findVal? "sh_1" = some sh₁ := rfl
  have f4 : ρ.findVal? "vcvtop" = some op := rfl
  have f5 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "sh_2" shapeT, .expP "sh_1" shapeT,
      .expP "vcvtop" (opT2 "vcvtop__"), .expP "c" vecT] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hsh₂ ρ hρ) (QuantsOk.cons f3 (hsh₁ ρ hρ)
      (QuantsOk.cons f4 (hop ρ hρ f3 f2) (QuantsOk.cons f5 (hc ρ hρ) QuantsOk.nil))))
  have hx : EvalArgs env ρ [.expA (.varE "sh_1"), .expA (.varE "sh_2"), .expA (.varE "vcvtop"),
      .expA (.varE "c_1")] [.val sh₁, .val sh₂, .val op, .val c₁] :=
    evalArgs_var f3 (evalArgs_var f2 (evalArgs_var f4 (evalArgs_var f1 Equiv.evalArgs_nil)))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list2 (evalExp_vconst f1) (evalExp_op3 f2 f3 f4))
      (evalExp_list1 (evalExp_vconst f5)))
    (prems_one (.ifPr (evalExp_eq_call f5 rfl hx ha)))

/-- `Step_pure/vvtestop` (rule 57): `c = $inez_($vsize(V128), c_1)`. -/
theorem spure_vvtestop {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 57 vvtestopRule)
    {c₁ n c : Value} (hc₁ : TypedV env vecT c₁) (hc : TypedV env i32T c)
    (hn : Applies env "vsize" [.val v128V] n) (ha : Applies env "inez_" [.val n, .val c₁] c) :
    SPure env [vconstV c₁, .case "VVTESTOP" (.tuple [v128V, caseNilV "ANY_TRUE"])]
      [Equiv.Execution.constV Equiv.Execution.i32V c] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "c" i32T] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hc ρ hρ) QuantsOk.nil)
  have es : EvalExp env ρ (.callE "vsize" [.expA (.caseE "V128" (.tupE []))]) n :=
    evalExp_call rfl (evalArgs_v128 Equiv.evalArgs_nil) hn
  have hx : EvalArgs env ρ [.expA (.callE "vsize" [.expA (.caseE "V128" (.tupE []))]),
      .expA (.varE "c_1")] [.val n, .val c₁] :=
    Equiv.evalArgs_cons es (evalArgs_var f1 Equiv.evalArgs_nil)
  have eany : EvalExp env ρ (.caseE "ANY_TRUE" (.tupE [])) (caseNilV "ANY_TRUE") :=
    evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_nil, rfl⟩)
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list2 (evalExp_vconst f1)
        (evalExp_case (evalExp_tup2 evalExp_v128 eany)))
      (evalExp_list1 (evalExp_constI32 f2)))
    (prems_one (.ifPr (evalExp_eq_call f2 rfl hx ha)))

end Silmaril.Wasm.SpecTec.Sim.Vec
