module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StateVar
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeGrow10

/-!
# `block`, `loop` and `memory.grow-succeed` of 1.0, backwards

* `Step_read/block` (0) and `Step_read/loop` (1) read no state: they are V1's `PureStep.block` and
  `PureStep.loop` under `Step.pure`. `block`'s arity `n` is pinned by its premise
  `t? = eps /\ n = 0 \/ t? =/= eps /\ n = 1` (`block_arity10`); `loop`'s label has arity `0`. Both
  rules are `changed` from 2.0 (2.0's block types are `_RESULT`/`_IDX`), so they are transcribed
  (`blockRule10`, `loopRule10`).
* `Step/memory.grow-succeed` (11) never fires at the spec's builtins: 1.0's `$growmemory` clause
  fails definitely and `floatIntB` does not answer it (`Sim20.Whole.not_fires_memGrowSucceed10`,
  the first step of the 1.0 route, from pass 2). Its `simEnv10` is this module's `Sim10.simEnv10`
  (`simEnv10_eq`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  expression)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV iterPat evalExp_iterPat)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk evalExp_tup2 evalExp_tup3 evalExp_list1 evalExp_case
  quant_list quant_of)
open Silmaril.Wasm.SpecTec.Sim20.Pure (evalExp_list0)
open Silmaril.Wasm.SpecTec.Sim20.Whole (evalExp_subIterPat subIterPat)
open Silmaril.Wasm.Numerics (Profile)

set_option maxRecDepth 100000

variable (B : Builtins)

/-! ## The rules, transcribed -/

/-- `instr*` coerced to `admininstr*`. -/
abbrev instrsAdmE : Exp := subIterPat "instr" "instr*" (.varT "instr" []) (.varT "admininstr" [])

/-- `LOOP t? instr*`. -/
abbrev loopE : Exp := .caseE "LOOP" (.tupE [optT, iterPat "instr" "instr*"])

/-- `t? op eps`. -/
abbrev optCmpE (op : CmpOp) : Exp := .cmpE op .boolT optT (.optE none)

/-- `n = k`. -/
abbrev nEqE (k : Nat) : Exp := .cmpE .eqOp .boolT (.varE "n") (.numE (.natN k))

/-- `Step_read/block`, rule 0 of 1.0's `Step_read`. -/
def blockRule10 : Rule :=
  .ruleD "block" [.expP "z" (.varT "state" []), .expP "t?" (.iterT (.varT "valtype" []) .opt),
      .expP "instr*" (.iterT (.varT "instr" []) .list), .expP "n" (.varT "n" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [.caseE "BLOCK" (.tupE [optT,
        iterPat "instr" "instr*"])]]),
      .listE [.caseE "LABEL_%{%}%" (.tupE [.varE "n", .listE [], instrsAdmE])]])
    [.ifPr (.binE .orOp .boolT (.binE .andOp .boolT (optCmpE .eqOp) (nEqE 0))
      (.binE .andOp .boolT (optCmpE .neOp) (nEqE 1)))]

/-- `Step_read/loop`, rule 1 of 1.0's `Step_read`. -/
def loopRule10 : Rule :=
  .ruleD "loop" [.expP "z" (.varT "state" []), .expP "t?" (.iterT (.varT "valtype" []) .opt),
      .expP "instr*" (.iterT (.varT "instr" []) .list)] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [loopE]]),
      .listE [.caseE "LABEL_%{%}%" (.tupE [.numE (.natN 0), .listE [loopE], instrsAdmE])]]) []

theorem hasRuleAt10_block : HasRuleAt (simEnv10 B) "Step_read" "%~>%" 0 blockRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_loop : HasRuleAt (simEnv10 B) "Step_read" "%~>%" 1 loopRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## Reading the pieces back -/

variable {B} {H : Type} {hn : H → String}

/-- `expression body` is encoded as the body's instructions. -/
theorem adminsToV_expression (body : V1.Expr) : adminsToV (expression body) = instrsToV body := by
  induction body with
  | nil => rfl
  | cons i is ih =>
    show adminToV (.source i) :: adminsToV (expression is) = instrToV i :: instrsToV is
    rw [ih]
    rfl

/-- The pieces `t?` and `instr*` of a `BLOCK`/`LOOP` left-hand side, read back, with `instr*`
bound to the body. -/
theorem blockParts10 {σ : List (IL.Id × Value)} {qs : List Param} {op : MixopS} {bt : V1.BlockType}
    {body : V1.Expr} (hq : QuantsOk (simEnv10 B) (VarEnv.empty.bindVals σ) qs)
    (hm : Param.expP "instr*" (.iterT (.varT "instr" []) .list) ∈ qs)
    (h : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.caseE op (.tupE [optT, iterPat "instr" "instr*"]))
      (.case op (.tuple [blockTypeV bt, .list (instrsToV body)]))) :
    EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) optT (blockTypeV bt) ∧
      (VarEnv.empty.bindVals σ).findVal? "instr*" = some (.list (instrsToV body)) := by
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 h
  obtain rfl := (Value.case.inj hcu).2
  obtain ⟨u₁, u₂, h₁, h₂, he⟩ := Sim.State.evalExp_tup2_inv hu
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨l, fl, -⟩ := quant_list hq hm
  have el := EvalExp.unique h₂ (evalExp_iterPat (by decide) fl)
  rw [← el] at fl
  exact ⟨h₁, fl⟩

/-- A boolean disjunction, with the short circuit of `boolShort`. -/
theorem evalExp_orB {env : Env} {ρ : VarEnv} {t : OpTyp} {e₁ e₂ : Exp} {b₁ b₂ : Bool}
    (h₁ : EvalExp env ρ e₁ (.bool b₁)) (h₂ : EvalExp env ρ e₂ (.bool b₂)) :
    EvalExp env ρ (.binE .orOp t e₁ e₂) (.bool (b₁ || b₂)) := by
  cases b₁ with
  | true => exact evalExp_binE_iff.2 ⟨.bool true, h₁, Or.inl rfl⟩
  | false => exact evalExp_binE_iff.2 ⟨.bool false, h₁, Or.inr ⟨rfl, .bool b₂, h₂, rfl⟩⟩

/-- **`block`'s premise pins the label arity** to the number of results. -/
theorem block_arity10 {ρ : VarEnv} {bt : V1.BlockType} {N : Value}
    (ht : EvalExp (simEnv10 B) ρ optT (blockTypeV bt)) (hn : ρ.findVal? "n" = some N)
    (hp : EvalExp (simEnv10 B) ρ (.binE .orOp .boolT (.binE .andOp .boolT (optCmpE .eqOp) (nEqE 0))
      (.binE .andOp .boolT (optCmpE .neOp) (nEqE 1))) (.bool true)) :
    N = .num (.natN bt.toList.length) := by
  have hn₀ : ∀ k, EvalExp (simEnv10 B) ρ (nEqE k) (.bool (N == .num (.natN k))) := fun k =>
    evalExp_cmpE_iff.2 ⟨_, _, evalExp_var hn, evalExp_numE_iff.2 rfl, rfl⟩
  have hnone : EvalExp (simEnv10 B) ρ (.optE none) (.opt none) := evalExp_optE_none_iff.2 rfl
  have he : EvalExp (simEnv10 B) ρ (optCmpE .eqOp) (.bool (blockTypeV bt == .opt none)) :=
    evalExp_cmpE_iff.2 ⟨_, _, ht, hnone, rfl⟩
  have hne : EvalExp (simEnv10 B) ρ (optCmpE .neOp) (.bool (!(blockTypeV bt == .opt none))) :=
    evalExp_cmpE_iff.2 ⟨_, _, ht, hnone, rfl⟩
  have hv := EvalExp.unique hp (evalExp_orB (evalExp_and he (hn₀ 0)) (evalExp_and hne (hn₀ 1)))
  have hb := Value.bool.inj hv
  cases bt with
  | none =>
    have e₀ : (blockTypeV none == Value.opt none) = true := by simp [blockTypeV]
    rw [e₀] at hb
    simpa using hb
  | some t =>
    have e₀ : (blockTypeV (some t) == Value.opt none) = false := by simp [blockTypeV]
    rw [e₀] at hb
    simpa using hb

/-! ## Backwards -/

/-- **`Step_read/loop` backwards**: V1's `PureStep.loop`. -/
theorem bwd10_loop {host : HostSemantics H} {c : Config H} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_read" 1 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, -, hes, hrh, -⟩ := firesCfg10_inv (hasRuleAt10_loop B) hf
  obtain ⟨a, rfl, ha⟩ := codes10_one hes
  obtain ⟨bt, body, rfl⟩ := head10_loop (head10_of_caseE ha)
  obtain ⟨-, fb⟩ := blockParts10 hq (by simp) ha
  have he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "LABEL_%{%}%" (.tupE [.numE (.natN 0), .listE [loopE], instrsAdmE])])
      (.list (adminsToV [.label 0 [.loop bt body] (expression body)])) := by
    have hv : adminsToV [.label 0 [.loop bt body] (expression body)] =
        [.case "LABEL_%{%}%" (.tuple [.num (.natN 0), .list [adminToV (.source (.loop bt body))],
          .list (instrsToV body)])] := by
      show [adminToV _] = _
      simp only [adminToV, adminsToV_expression]
      rfl
    rw [hv]
    exact evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_numE_iff.2 rfl) (evalExp_list1 ha)
      (evalExp_subIterPat (by decide) fb)))
  exact ⟨_, Value.list.inj (EvalExp.unique hrh he), .pure s f (.loop bt body)⟩

/-- **`Step_read/block` backwards**: V1's `PureStep.block`. -/
theorem bwd10_block {host : HostSemantics H} {c : Config H} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_read" 0 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, -, hes, hrh, hp⟩ := firesCfg10_inv (hasRuleAt10_block B) hf
  obtain ⟨a, rfl, ha⟩ := codes10_one hes
  obtain ⟨bt, body, rfl⟩ := head10_block (head10_of_caseE ha)
  obtain ⟨ht, fb⟩ := blockParts10 hq (by simp) ha
  obtain ⟨N, fN, -⟩ := quant_of (x := "n") (t := .varT "n" []) hq (by simp)
  have hN : N = .num (.natN bt.toList.length) :=
    block_arity10 ht fN (Sim20.Pure.ifPrem (hp _ (.head _)))
  have hv : adminsToV [.label bt.toList.length [] (expression body)] =
      [.case "LABEL_%{%}%" (.tuple [.num (.natN bt.toList.length), .list [],
        .list (instrsToV body)])] := by
    show [adminToV _] = _
    simp only [adminToV, adminsToV_expression]
    rfl
  have he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "LABEL_%{%}%" (.tupE [.varE "n", .listE [], instrsAdmE])])
      (.list (adminsToV [.label bt.toList.length [] (expression body)])) :=
    hv ▸ evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var (hN ▸ fN)) evalExp_list0
      (evalExp_subIterPat (by decide) fb)))
  exact ⟨_, Value.list.inj (EvalExp.unique hrh he), .pure s f (.block bt body)⟩

/-- `Sim20.Whole.simEnv10`, of the 1.0 route's first step, is `Sim10.simEnv10`. -/
theorem simEnv10_eq (B : Builtins) : Sim20.Whole.simEnv10 B = simEnv10 B := rfl

/-- **`Step/memory.grow-succeed` never fires at the spec's builtins.** -/
theorem not_fires10_memGrowSucceed (P : Profile) (v : Value) :
    ¬ Fires (simEnv10 (Sim.Floats.floatIntB P)) "Step" 11 v := by
  rw [← simEnv10_eq]
  exact Sim20.Whole.not_fires_memGrowSucceed10_floatIntB P v

end Silmaril.Wasm.SpecTec.Sim10.Whole
