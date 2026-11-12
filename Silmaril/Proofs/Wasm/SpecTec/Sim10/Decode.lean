module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.WholeGood
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureBasic

/-!
# Decoding V1 code from its 1.0 image

The per-rule obligations `BwdParts10` start from a rule firing at the image `adminsToV code` of an
arbitrary V1 code sequence. This module reads the code back.

* `instrHead10`, `adminHead10`: the IL constructor each V1 instruction is encoded with;
  `adminToV_case10`: an image `.case op u` has `op = adminHead10 a`; `head10_*`: each constructor a
  rule mentions determines the V1 instruction.
* `firesPure10_inv`, `firesCfg10_inv`: a firing rule whose left-hand side is a list of expressions
  (`Step_pure`) or a configuration `z; es` (`Step_read`, `Step`) splits the code into instructions,
  each the value of its expression in the rule's scope; `codes10_one` … `codes10_four` name them.
* `val10_of_var`: a coerced `val` variable of a left-hand side is a V1 value (from the typing of
  the quantifier, `const_of_typed10`); `constI32_of_lhs10`: a `CONST I32 c` element is an `i32`
  constant.

All of it is generic in the environment except the reading of `val`'s typing, which is 1.0's.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk PremW DDerives otherwise ValsOnly cfgV stV)

/-! ## Heads -/

/-- The IL constructor `instrToV` encodes an instruction with. -/
def instrHead10 : V1.Instr → MixopS
  | .nop => "NOP" | .unreachable => "UNREACHABLE" | .drop => "DROP" | .select => "SELECT"
  | .block _ _ => "BLOCK" | .loop _ _ => "LOOP" | .if_ _ _ _ => "IF%%ELSE%" | .br _ => "BR"
  | .brIf _ => "BR_IF" | .brTable _ _ => "BR_TABLE" | .call _ => "CALL"
  | .callIndirect _ => "CALL_INDIRECT" | .return_ => "RETURN" | .localGet _ => "LOCAL.GET"
  | .localSet _ => "LOCAL.SET" | .localTee _ => "LOCAL.TEE" | .globalGet _ => "GLOBAL.GET"
  | .globalSet _ => "GLOBAL.SET" | .intLoad _ _ _ => "LOAD" | .floatLoad _ _ => "LOAD"
  | .intStore _ _ _ => "STORE" | .floatStore _ _ => "STORE" | .memorySize => "MEMORY.SIZE"
  | .memoryGrow => "MEMORY.GROW" | .intConst _ _ => "CONST" | .floatConst _ _ => "CONST"
  | .intUnOp _ _ => "UNOP" | .intBinOp _ _ => "BINOP" | .intTestOp _ _ => "TESTOP"
  | .intRelOp _ _ => "RELOP" | .floatUnOp _ _ => "UNOP" | .floatBinOp _ _ => "BINOP"
  | .floatRelOp _ _ => "RELOP" | .convert _ => "CVTOP"

/-- The IL constructor `adminToV` encodes an administrative instruction with. -/
def adminHead10 : Admin → MixopS
  | .source i => instrHead10 i
  | .invoke _ => "CALL_ADDR"
  | .label _ _ _ => "LABEL_%{%}%"
  | .frame _ _ _ => "FRAME_%{%}%"
  | .trap => "TRAP"

/-- Every instruction is encoded as a `case` with its head. -/
theorem instrToV_case10 (i : V1.Instr) : ∃ u, instrToV i = .case (instrHead10 i) u := by
  cases i <;> exact ⟨_, rfl⟩

/-- Every administrative instruction is encoded as a `case` with its head. -/
theorem adminToV_case10' (a : Admin) : ∃ u, adminToV a = .case (adminHead10 a) u := by
  cases a with
  | source i => exact instrToV_case10 i
  | _ => exact ⟨_, rfl⟩

/-- **An image `.case op u` has head `op`.** -/
theorem adminToV_case10 {a : Admin} {op : MixopS} {u : Value} (h : adminToV a = .case op u) :
    adminHead10 a = op := by
  obtain ⟨u', hu'⟩ := adminToV_case10' a
  exact (Value.case.inj (hu'.symm.trans h)).1

/-- Invert a 1.0 head by cases, comparing string literals. -/
macro "admin_head_inv10" : tactic => `(tactic| (
  first
    | (cases ‹Admin› with
        | source i => cases i <;> simp [adminHead10, instrHead10]
        | _ => simp [adminHead10])))

theorem head10_nop {a : Admin} (h : adminHead10 a = "NOP") : a = .source .nop := by
  revert h; admin_head_inv10

theorem head10_unreachable {a : Admin} (h : adminHead10 a = "UNREACHABLE") :
    a = .source .unreachable := by
  revert h; admin_head_inv10

theorem head10_drop {a : Admin} (h : adminHead10 a = "DROP") : a = .source .drop := by
  revert h; admin_head_inv10

theorem head10_select {a : Admin} (h : adminHead10 a = "SELECT") : a = .source .select := by
  revert h; admin_head_inv10

theorem head10_if {a : Admin} (h : adminHead10 a = "IF%%ELSE%") :
    ∃ bt b₁ b₂, a = .source (.if_ bt b₁ b₂) := by
  revert h; admin_head_inv10

theorem head10_brIf {a : Admin} (h : adminHead10 a = "BR_IF") : ∃ l, a = .source (.brIf l) := by
  revert h; admin_head_inv10

theorem head10_brTable {a : Admin} (h : adminHead10 a = "BR_TABLE") :
    ∃ ls l, a = .source (.brTable ls l) := by
  revert h; admin_head_inv10

theorem head10_localTee {a : Admin} (h : adminHead10 a = "LOCAL.TEE") :
    ∃ x, a = .source (.localTee x) := by
  revert h; admin_head_inv10

theorem head10_localGet {a : Admin} (h : adminHead10 a = "LOCAL.GET") :
    ∃ x, a = .source (.localGet x) := by
  revert h; admin_head_inv10

theorem head10_globalGet {a : Admin} (h : adminHead10 a = "GLOBAL.GET") :
    ∃ x, a = .source (.globalGet x) := by
  revert h; admin_head_inv10

theorem head10_localSet {a : Admin} (h : adminHead10 a = "LOCAL.SET") :
    ∃ x, a = .source (.localSet x) := by
  revert h; admin_head_inv10

theorem head10_globalSet {a : Admin} (h : adminHead10 a = "GLOBAL.SET") :
    ∃ x, a = .source (.globalSet x) := by
  revert h; admin_head_inv10

theorem head10_call {a : Admin} (h : adminHead10 a = "CALL") : ∃ x, a = .source (.call x) := by
  revert h; admin_head_inv10

theorem head10_block {a : Admin} (h : adminHead10 a = "BLOCK") :
    ∃ bt b, a = .source (.block bt b) := by
  revert h; admin_head_inv10

theorem head10_loop {a : Admin} (h : adminHead10 a = "LOOP") :
    ∃ bt b, a = .source (.loop bt b) := by
  revert h; admin_head_inv10

theorem head10_memoryGrow {a : Admin} (h : adminHead10 a = "MEMORY.GROW") :
    a = .source .memoryGrow := by
  revert h; admin_head_inv10

theorem head10_label {a : Admin} (h : adminHead10 a = "LABEL_%{%}%") :
    ∃ n cont body, a = .label n cont body := by
  revert h; admin_head_inv10

theorem head10_frame {a : Admin} (h : adminHead10 a = "FRAME_%{%}%") :
    ∃ n fi body, a = .frame n fi body := by
  revert h; admin_head_inv10

theorem head10_trap {a : Admin} (h : adminHead10 a = "TRAP") : a = .trap := by
  revert h; admin_head_inv10

/-- A `case` element of a left-hand side gives the instruction's head. -/
theorem head10_of_caseE {env : Env} {ρ : VarEnv} {op : MixopS} {e : Exp} {a : Admin}
    (h : EvalExp env ρ (.caseE op e) (adminToV a)) : adminHead10 a = op := by
  obtain ⟨u, -, hu⟩ := evalExp_caseE_iff.1 h
  exact adminToV_case10 hu

/-! ## Rule left-hand sides, element by element -/

theorem codes10_nil {env : Env} {ρ : VarEnv} {is : List Admin}
    (h : EvalExps env ρ [] (adminsToV is)) : is = [] := by
  have e := Silmaril.SpecTec.Sem.evalExps_nil_iff.1 h
  cases is with
  | nil => rfl
  | cons a l => simp [adminsToV] at e

theorem codes10_cons {env : Env} {ρ : VarEnv} {e : Exp} {es : List Exp} {is : List Admin}
    (h : EvalExps env ρ (e :: es) (adminsToV is)) :
    ∃ a is', is = a :: is' ∧ EvalExp env ρ e (adminToV a) ∧ EvalExps env ρ es (adminsToV is') := by
  obtain ⟨w, ws, hw, hws, he⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 h
  cases is with
  | nil => simp [adminsToV] at he
  | cons a l =>
      simp only [adminsToV, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨a, l, rfl, hw, hws⟩

theorem codes10_one {env : Env} {ρ : VarEnv} {e₁ : Exp} {is : List Admin}
    (h : EvalExps env ρ [e₁] (adminsToV is)) :
    ∃ a₁, is = [a₁] ∧ EvalExp env ρ e₁ (adminToV a₁) := by
  obtain ⟨a₁, is, rfl, h₁, h⟩ := codes10_cons h
  obtain rfl := codes10_nil h
  exact ⟨a₁, rfl, h₁⟩

theorem codes10_two {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {is : List Admin}
    (h : EvalExps env ρ [e₁, e₂] (adminsToV is)) :
    ∃ a₁ a₂, is = [a₁, a₂] ∧ EvalExp env ρ e₁ (adminToV a₁) ∧
      EvalExp env ρ e₂ (adminToV a₂) := by
  obtain ⟨a₁, is, rfl, h₁, h⟩ := codes10_cons h
  obtain ⟨a₂, rfl, h₂⟩ := codes10_one h
  exact ⟨a₁, a₂, rfl, h₁, h₂⟩

theorem codes10_three {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {is : List Admin}
    (h : EvalExps env ρ [e₁, e₂, e₃] (adminsToV is)) :
    ∃ a₁ a₂ a₃, is = [a₁, a₂, a₃] ∧ EvalExp env ρ e₁ (adminToV a₁) ∧
      EvalExp env ρ e₂ (adminToV a₂) ∧ EvalExp env ρ e₃ (adminToV a₃) := by
  obtain ⟨a₁, is, rfl, h₁, h⟩ := codes10_cons h
  obtain ⟨a₂, a₃, rfl, h₂, h₃⟩ := codes10_two h
  exact ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩

theorem codes10_four {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ e₄ : Exp} {is : List Admin}
    (h : EvalExps env ρ [e₁, e₂, e₃, e₄] (adminsToV is)) :
    ∃ a₁ a₂ a₃ a₄, is = [a₁, a₂, a₃, a₄] ∧ EvalExp env ρ e₁ (adminToV a₁) ∧
      EvalExp env ρ e₂ (adminToV a₂) ∧ EvalExp env ρ e₃ (adminToV a₃) ∧
      EvalExp env ρ e₄ (adminToV a₄) := by
  obtain ⟨a₁, is, rfl, h₁, h⟩ := codes10_cons h
  obtain ⟨a₂, a₃, a₄, rfl, h₂, h₃, h₄⟩ := codes10_three h
  exact ⟨a₁, a₂, a₃, a₄, rfl, h₁, h₂, h₃, h₄⟩

/-- **A firing `Step_pure` rule `es ~> rh`, inverted**: the code evaluates element by element in
the rule's scope, and so does the right-hand side. -/
theorem firesPure10_inv {env : Env} {k : Nat} {nm : IL.Id} {qs : List Param} {es : List Exp}
    {rh : Exp} {prems : List Prem} {is : List Admin} {w : Value}
    (h : HasRuleAt env "Step_pure" "%~>%" k (.ruleD nm qs "%~>%" (.tupE [.listE es, rh]) prems))
    (hf : Fires env "Step_pure" k (.tuple [.list (adminsToV is), w])) :
    ∃ σ, QuantsOk env (VarEnv.empty.bindVals σ) qs ∧
      EvalExps env (VarEnv.empty.bindVals σ) es (adminsToV is) ∧
      EvalExp env (VarEnv.empty.bindVals σ) rh w ∧
      ∀ pr ∈ prems, PremW env (DDerives env (otherwise env))
        (otherwise env "Step_pure" [] k (.tuple [.list (adminsToV is), w]))
        (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨σ, hq, he, hp⟩ := Sim20.Pure.fires_inv h hf
  exact ⟨σ, hq, Sim.RefsGC.elems_of_list (Sim.RefsGC.lhs_of_concl he),
    Sim.RefsGC.rhs_of_concl he, hp⟩

variable {H : Type}

/-- **A firing rule `z; es ~> rh` at a configuration, inverted**: the state variable is bound to
the image of the state, the code evaluates element by element, and so does the right-hand side. -/
theorem firesCfg10_inv {env : Env} {x : IL.Id} {k : Nat} {nm : IL.Id} {qs : List Param}
    {es : List Exp} {rh : Exp} {prems : List Prem} {hn : H → String} {c : Config H} {w : Value}
    (h : HasRuleAt env x "%~>%" k
      (.ruleD nm qs "%~>%" (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE es]), rh]) prems))
    (hf : Fires env x k (.tuple [configV hn c, w])) :
    ∃ σ, QuantsOk env (VarEnv.empty.bindVals σ) qs ∧
      (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn c.store c.frame) ∧
      EvalExps env (VarEnv.empty.bindVals σ) es (adminsToV c.code) ∧
      EvalExp env (VarEnv.empty.bindVals σ) rh w ∧
      ∀ pr ∈ prems, PremW env (DDerives env (otherwise env))
        (otherwise env x [] k (.tuple [configV hn c, w])) (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨σ, hq, he, hp⟩ := Sim20.Pure.fires_inv h hf
  have hl := Sim.RefsGC.lhs_of_concl he
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 hl
  have hu' : u = .tuple [stateV hn c.store c.frame, .list (adminsToV c.code)] :=
    (Value.case.inj hcu.symm).2
  obtain ⟨u₁, u₂, hZ, hL, hU⟩ := Sim.State.evalExp_tup2_inv (hu' ▸ hu)
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hU
  obtain ⟨rfl, rfl⟩ := hU
  exact ⟨σ, hq, evalExp_varE_iff.1 hZ, Sim.RefsGC.elems_of_list hL, Sim.RefsGC.rhs_of_concl he, hp⟩

/-! ## Values -/

variable {B : Builtins}

/-- The image of a V1 value. -/
theorem adminToV_value (v : Execution.Runtime.Value) : adminToV (value v) = valV v := by
  rcases v with ⟨⟨_⟩ | ⟨_⟩, _⟩ <;> rfl

/-- **A coerced `val` variable `(x : val <: admininstr)` of a left-hand side, at a well-typed
scope, is a V1 value**, and the variable is bound to its image. -/
theorem val10_of_var {σ : List (IL.Id × Value)} {qs : List Param} {x : IL.Id} {a : Admin}
    (hq : QuantsOk (simEnv10 B) (VarEnv.empty.bindVals σ) qs)
    (hm : Param.expP x (.varT "val" []) ∈ qs)
    (h : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.subE (.varE x) (.varT "val" []) (.varT "admininstr" [])) (adminToV a)) :
    ∃ v, a = value v ∧ (VarEnv.empty.bindVals σ).findVal? x = some (valV v) := by
  obtain ⟨R, fR, tR⟩ := hq x _ hm
  have e : adminToV a = R := EvalExp.unique (evalExp_subE_iff.1 h) (evalExp_var fR)
  obtain ⟨w, hw⟩ := const_of_typed10 (Sim.valsOnly_bindVals σ) (e ▸ tR)
  obtain ⟨v, rfl⟩ := admin_of_const10 hw
  refine ⟨v, rfl, ?_⟩
  rw [fR, ← e, adminToV_value]

/-- A `CONST I32 e` element of a left-hand side is an `i32` constant, and `e` evaluates to its
payload. -/
theorem constI32_of_lhs10 {env : Env} {ρ : VarEnv} {e : Exp} {a : Admin}
    (h : EvalExp env ρ (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), e])) (adminToV a)) :
    ∃ c : BitVec 32, a = value ⟨.int .i32, c⟩ ∧ EvalExp env ρ e (pctV c.toNat) := by
  obtain ⟨u, hu, he⟩ := evalExp_caseE_iff.1 h
  obtain ⟨u₁, u₂, hu₁, hu₂, rfl⟩ := Sim.State.evalExp_tup2_inv hu
  have e₁ : u₁ = caseNilV "I32" := by
    obtain ⟨z, hz, rfl⟩ := evalExp_caseE_iff.1 hu₁
    obtain ⟨zs, hzs, rfl⟩ := evalExp_tupE_iff.1 hz
    rw [Silmaril.SpecTec.Sem.evalExps_nil_iff.1 hzs]
    rfl
  subst e₁
  obtain ⟨v, rfl⟩ := admin_of_const10 he
  rcases v with ⟨⟨t⟩ | ⟨t⟩, b⟩
  · cases t
    · refine ⟨b, rfl, ?_⟩
      have hv : adminToV (value ⟨.int .i32, b⟩) =
          .case "CONST" (.tuple [caseNilV "I32", pctV b.toNat]) := rfl
      rw [hv] at he
      simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and] at he
      exact he.1 ▸ hu₂
    · simp [adminToV_value, valV, valTypeV, Sim20.numTypeV, caseNilV] at he
  · cases t <;> simp [adminToV_value, valV, valTypeV, Sim20.numTypeV, caseNilV] at he

end Silmaril.Wasm.SpecTec.Sim10.Whole
