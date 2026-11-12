module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeDead
public import Silmaril.Proofs.Wasm.SpecTec.Sim.State.Backward

/-!
# Decoding V2 code from its 2.0 image

The backward obligations `BwdLive20` start from a rule firing at the image `adminsToV code` of an
arbitrary V2 code sequence. This module reads the code back.

* `instrHead20`, `adminHead20`: the IL constructor each V2 instruction is encoded with;
  `adminToV_case20`: an image `.case op u` has `op = adminHead20 a`.
* `head20_*`: each constructor a live rule mentions determines the V2 instruction (a case split
  comparing string literals only).
* `admin_of_valHead`: an image with a `val` constructor is the image of a V2 value
  (`Val.toAdmin`).
* `fires_list20`: a firing `Step_pure` rule whose left-hand side is a list of `n` expressions
  splits the code into `n` instructions, each the value of its expression in the rule's scope;
  `codes20_one` … `codes20_four` name them.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk PremW DDerives otherwise ValsOnly)

/-! ## Heads -/

/-- The IL constructor `instrToV` encodes an instruction with. -/
def instrHead20 : V2.Instr → MixopS
  | .nop => "NOP" | .unreachable => "UNREACHABLE" | .drop => "DROP" | .select _ => "SELECT"
  | .block _ _ => "BLOCK" | .loop _ _ => "LOOP" | .if_ _ _ _ => "IF%%ELSE%" | .br _ => "BR"
  | .brIf _ => "BR_IF" | .brTable _ _ => "BR_TABLE" | .call _ => "CALL"
  | .callIndirect _ _ => "CALL_INDIRECT" | .return_ => "RETURN" | .intConst _ _ => "CONST"
  | .floatConst _ _ => "CONST" | .intUnOp _ _ => "UNOP" | .floatUnOp _ _ => "UNOP"
  | .intBinOp _ _ => "BINOP" | .floatBinOp _ _ => "BINOP" | .intTestOp _ _ => "TESTOP"
  | .intRelOp _ _ => "RELOP" | .floatRelOp _ _ => "RELOP" | .cvtOp _ _ _ => "CVTOP"
  | .vecConst _ => "VCONST" | .vvUnOp _ => "VVUNOP" | .vvBinOp _ => "VVBINOP"
  | .vvTernOp _ => "VVTERNOP" | .vvTestOp _ => "VVTESTOP" | .vecIntUnOp _ _ => "VUNOP"
  | .vecFloatUnOp _ _ => "VUNOP" | .vecIntBinOp _ _ => "VBINOP" | .vecFloatBinOp _ _ => "VBINOP"
  | .vecAllTrue _ => "VTESTOP" | .vecIntRelOp _ _ => "VRELOP" | .vecFloatRelOp _ _ => "VRELOP"
  | .vecShiftOp _ _ => "VSHIFTOP" | .vecBitmask _ => "VBITMASK" | .vecSwizzle => "VSWIZZLE"
  | .vecShuffle _ => "VSHUFFLE" | .vecSplat _ => "VSPLAT"
  | .vecExtractLane _ _ _ => "VEXTRACT_LANE" | .vecReplaceLane _ _ => "VREPLACE_LANE"
  | .vecExtUnOp _ _ _ => "VEXTUNOP" | .vecExtBinOp _ _ _ => "VEXTBINOP"
  | .vecNarrow _ _ _ => "VNARROW" | .vecCvtOp _ _ _ => "VCVTOP" | .refNull _ => "REF.NULL"
  | .refFunc _ => "REF.FUNC" | .refIsNull => "REF.IS_NULL" | .localGet _ => "LOCAL.GET"
  | .localSet _ => "LOCAL.SET" | .localTee _ => "LOCAL.TEE" | .globalGet _ => "GLOBAL.GET"
  | .globalSet _ => "GLOBAL.SET" | .tableGet _ => "TABLE.GET" | .tableSet _ => "TABLE.SET"
  | .tableSize _ => "TABLE.SIZE" | .tableGrow _ => "TABLE.GROW" | .tableFill _ => "TABLE.FILL"
  | .tableCopy _ _ => "TABLE.COPY" | .tableInit _ _ => "TABLE.INIT" | .elemDrop _ => "ELEM.DROP"
  | .intLoad _ _ _ => "LOAD" | .floatLoad _ _ => "LOAD" | .intStore _ _ _ => "STORE"
  | .floatStore _ _ => "STORE" | .vecLoad _ _ => "VLOAD" | .vecLoadLane _ _ _ => "VLOAD_LANE"
  | .vecStore _ => "VSTORE" | .vecStoreLane _ _ _ => "VSTORE_LANE"
  | .memorySize => "MEMORY.SIZE" | .memoryGrow => "MEMORY.GROW" | .memoryFill => "MEMORY.FILL"
  | .memoryCopy => "MEMORY.COPY" | .memoryInit _ => "MEMORY.INIT" | .dataDrop _ => "DATA.DROP"

/-- The IL constructor `adminToV` encodes an administrative instruction with. -/
def adminHead20 : Admin → MixopS
  | .plain i => instrHead20 i
  | .refFuncAddr _ => "REF.FUNC_ADDR"
  | .refHostAddr _ => "REF.HOST_ADDR"
  | .callAddr _ => "CALL_ADDR"
  | .label _ _ _ => "LABEL_%{%}%"
  | .frame _ _ _ => "FRAME_%{%}%"
  | .trap => "TRAP"

/-- Every instruction is encoded as a `case` with its head. -/
theorem instrToV_head20 (i : V2.Instr) : ∃ u, instrToV i = .case (instrHead20 i) u := by
  cases i
  case vvUnOp op => cases op; exact ⟨_, rfl⟩
  case vvBinOp op => cases op <;> exact ⟨_, rfl⟩
  case vvTernOp op => cases op; exact ⟨_, rfl⟩
  case vvTestOp op => cases op; exact ⟨_, rfl⟩
  all_goals exact ⟨_, rfl⟩

/-- Every administrative instruction is encoded as a `case` with its head. -/
theorem adminToV_head20 (a : Admin) : ∃ u, adminToV a = .case (adminHead20 a) u := by
  cases a with
  | plain i => exact instrToV_head20 i
  | _ => exact ⟨_, rfl⟩

/-- **An image `.case op u` has head `op`.** -/
theorem adminToV_case20 {a : Admin} {op : MixopS} {u : Value} (h : adminToV a = .case op u) :
    adminHead20 a = op := by
  obtain ⟨u', hu'⟩ := adminToV_head20 a
  exact (Value.case.inj (hu'.symm.trans h)).1

/-- Invert a 2.0 head by cases, comparing string literals. -/
macro "admin_head_inv20" : tactic => `(tactic| (
  first
    | (cases ‹Admin› with
        | plain i => cases i <;> simp [adminHead20, instrHead20]
        | _ => simp [adminHead20])))

theorem head20_nop {a : Admin} (h : adminHead20 a = "NOP") : a = .plain .nop := by
  revert h; admin_head_inv20

theorem head20_drop {a : Admin} (h : adminHead20 a = "DROP") : a = .plain .drop := by
  revert h; admin_head_inv20

theorem head20_select {a : Admin} (h : adminHead20 a = "SELECT") : ∃ ts, a = .plain (.select ts) := by
  revert h; admin_head_inv20

theorem head20_if {a : Admin} (h : adminHead20 a = "IF%%ELSE%") :
    ∃ bt b₁ b₂, a = .plain (.if_ bt b₁ b₂) := by
  revert h; admin_head_inv20

theorem head20_brIf {a : Admin} (h : adminHead20 a = "BR_IF") : ∃ l, a = .plain (.brIf l) := by
  revert h; admin_head_inv20

theorem head20_brTable {a : Admin} (h : adminHead20 a = "BR_TABLE") :
    ∃ ls l, a = .plain (.brTable ls l) := by
  revert h; admin_head_inv20

theorem head20_const {a : Admin} (h : adminHead20 a = "CONST") :
    (∃ t b, a = .plain (.intConst t b)) ∨ ∃ t b, a = .plain (.floatConst t b) := by
  revert h; admin_head_inv20

theorem head20_unop {a : Admin} (h : adminHead20 a = "UNOP") :
    (∃ t op, a = .plain (.intUnOp t op)) ∨ ∃ t op, a = .plain (.floatUnOp t op) := by
  revert h; admin_head_inv20

theorem head20_binop {a : Admin} (h : adminHead20 a = "BINOP") :
    (∃ t op, a = .plain (.intBinOp t op)) ∨ ∃ t op, a = .plain (.floatBinOp t op) := by
  revert h; admin_head_inv20

theorem head20_testop {a : Admin} (h : adminHead20 a = "TESTOP") :
    ∃ t op, a = .plain (.intTestOp t op) := by
  revert h
  cases a with
  | plain i =>
    cases i <;> simp [adminHead20, instrHead20]
    exact ⟨.eqz⟩
  | _ => simp [adminHead20]

theorem head20_relop {a : Admin} (h : adminHead20 a = "RELOP") :
    (∃ t op, a = .plain (.intRelOp t op)) ∨ ∃ t op, a = .plain (.floatRelOp t op) := by
  revert h; admin_head_inv20

theorem head20_cvtop {a : Admin} (h : adminHead20 a = "CVTOP") :
    ∃ t₁ t₂ op, a = .plain (.cvtOp t₁ t₂ op) := by
  revert h; admin_head_inv20

theorem head20_refIsNull {a : Admin} (h : adminHead20 a = "REF.IS_NULL") :
    a = .plain .refIsNull := by
  revert h; admin_head_inv20

theorem head20_localTee {a : Admin} (h : adminHead20 a = "LOCAL.TEE") :
    ∃ x, a = .plain (.localTee x) := by
  revert h; admin_head_inv20

theorem head20_localGet {a : Admin} (h : adminHead20 a = "LOCAL.GET") :
    ∃ x, a = .plain (.localGet x) := by
  revert h; admin_head_inv20

theorem head20_globalGet {a : Admin} (h : adminHead20 a = "GLOBAL.GET") :
    ∃ x, a = .plain (.globalGet x) := by
  revert h; admin_head_inv20

theorem head20_localSet {a : Admin} (h : adminHead20 a = "LOCAL.SET") :
    ∃ x, a = .plain (.localSet x) := by
  revert h; admin_head_inv20

theorem head20_globalSet {a : Admin} (h : adminHead20 a = "GLOBAL.SET") :
    ∃ x, a = .plain (.globalSet x) := by
  revert h; admin_head_inv20

/-! ## Values -/

/-- **An image with a `val` constructor is the image of a V2 value.** -/
theorem admin_of_head_val {a : Admin} (h : adminHead20 a ∈ Pure.valHeads20) :
    ∃ v : Val, a = v.toAdmin := by
  revert h
  cases a with
  | plain i =>
    cases i <;> simp [adminHead20, instrHead20, Pure.valHeads20]
    case intConst t b => exact ⟨.num ⟨.int t, b⟩, rfl⟩
    case floatConst t b => exact ⟨.num ⟨.float t, b⟩, rfl⟩
    case vecConst b => exact ⟨.vec b, rfl⟩
    case refNull t => exact ⟨.ref (.null t), rfl⟩
  | refFuncAddr x => exact fun _ => ⟨.ref (.funcAddr x), rfl⟩
  | refHostAddr x => exact fun _ => ⟨.ref (.hostAddr x), rfl⟩
  | _ => simp [adminHead20, Pure.valHeads20]

/-- An image that is a `val` head is the image of a V2 value. -/
theorem admin_of_valHead {a : Admin} (h : Pure.ValHead (adminToV a)) :
    ∃ v : Val, a = v.toAdmin := by
  obtain ⟨op, w, he, hm⟩ := h
  exact admin_of_head_val (adminToV_case20 he ▸ hm)

/-! ## Rule left-hand sides, element by element -/

/-- The empty code list. -/
theorem codes20_nil {env : Env} {ρ : VarEnv} {is : List Admin}
    (h : EvalExps env ρ [] (adminsToV is)) : is = [] := by
  have e := Silmaril.SpecTec.Sem.evalExps_nil_iff.1 h
  cases is with
  | nil => rfl
  | cons a l => simp [adminsToV] at e

/-- A non-empty code list. -/
theorem codes20_cons {env : Env} {ρ : VarEnv} {e : Exp} {es : List Exp} {is : List Admin}
    (h : EvalExps env ρ (e :: es) (adminsToV is)) :
    ∃ a is', is = a :: is' ∧ EvalExp env ρ e (adminToV a) ∧ EvalExps env ρ es (adminsToV is') := by
  obtain ⟨w, ws, hw, hws, he⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 h
  cases is with
  | nil => simp [adminsToV] at he
  | cons a l =>
      simp only [adminsToV, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨a, l, rfl, hw, hws⟩

theorem codes20_one {env : Env} {ρ : VarEnv} {e₁ : Exp} {is : List Admin}
    (h : EvalExps env ρ [e₁] (adminsToV is)) :
    ∃ a₁, is = [a₁] ∧ EvalExp env ρ e₁ (adminToV a₁) := by
  obtain ⟨a₁, is, rfl, h₁, h⟩ := codes20_cons h
  obtain rfl := codes20_nil h
  exact ⟨a₁, rfl, h₁⟩

theorem codes20_two {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {is : List Admin}
    (h : EvalExps env ρ [e₁, e₂] (adminsToV is)) :
    ∃ a₁ a₂, is = [a₁, a₂] ∧ EvalExp env ρ e₁ (adminToV a₁) ∧
      EvalExp env ρ e₂ (adminToV a₂) := by
  obtain ⟨a₁, is, rfl, h₁, h⟩ := codes20_cons h
  obtain ⟨a₂, rfl, h₂⟩ := codes20_one h
  exact ⟨a₁, a₂, rfl, h₁, h₂⟩

theorem codes20_three {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {is : List Admin}
    (h : EvalExps env ρ [e₁, e₂, e₃] (adminsToV is)) :
    ∃ a₁ a₂ a₃, is = [a₁, a₂, a₃] ∧ EvalExp env ρ e₁ (adminToV a₁) ∧
      EvalExp env ρ e₂ (adminToV a₂) ∧ EvalExp env ρ e₃ (adminToV a₃) := by
  obtain ⟨a₁, is, rfl, h₁, h⟩ := codes20_cons h
  obtain ⟨a₂, a₃, rfl, h₂, h₃⟩ := codes20_two h
  exact ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩

theorem codes20_four {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ e₄ : Exp} {is : List Admin}
    (h : EvalExps env ρ [e₁, e₂, e₃, e₄] (adminsToV is)) :
    ∃ a₁ a₂ a₃ a₄, is = [a₁, a₂, a₃, a₄] ∧ EvalExp env ρ e₁ (adminToV a₁) ∧
      EvalExp env ρ e₂ (adminToV a₂) ∧ EvalExp env ρ e₃ (adminToV a₃) ∧
      EvalExp env ρ e₄ (adminToV a₄) := by
  obtain ⟨a₁, is, rfl, h₁, h⟩ := codes20_cons h
  obtain ⟨a₂, a₃, a₄, rfl, h₂, h₃, h₄⟩ := codes20_three h
  exact ⟨a₁, a₂, a₃, a₄, rfl, h₁, h₂, h₃, h₄⟩

/-- **A firing `Step_pure` rule `es ~> rh`, inverted**: the code evaluates element by element in
the rule's scope. -/
theorem fires_list20 {env : Env} {k : Nat} {nm : IL.Id} {qs : List Param} {es : List Exp}
    {rh : Exp} {prems : List Prem} {is : List Admin} {w : Value}
    (h : HasRuleAt env "Step_pure" "%~>%" k (.ruleD nm qs "%~>%" (.tupE [.listE es, rh]) prems))
    (hf : Fires env "Step_pure" k (.tuple [.list (adminsToV is), w])) :
    ∃ σ, QuantsOk env (VarEnv.empty.bindVals σ) qs ∧
      EvalExps env (VarEnv.empty.bindVals σ) es (adminsToV is) := by
  obtain ⟨σ, hq, he, -⟩ := Sim.State.Fires.rule_eq h hf
  exact ⟨σ, hq, Sim.RefsGC.elems_of_list (Sim.RefsGC.lhs_of_concl he)⟩

/-- A `case` element of a left-hand side gives the instruction's head. -/
theorem head20_of_caseE {env : Env} {ρ : VarEnv} {op : MixopS} {e : Exp} {a : Admin}
    (h : EvalExp env ρ (.caseE op e) (adminToV a)) : adminHead20 a = op := by
  obtain ⟨u, -, hu⟩ := evalExp_caseE_iff.1 h
  exact adminToV_case20 hu

/-- A coerced `val` variable `(x : val <: admininstr)` of a left-hand side, at a well-typed
scope, is a V2 value. -/
theorem val20_of_var {B : Builtins} {σ : List (IL.Id × Value)} {qs : List Param} {x : IL.Id}
    {a : Admin} (hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) qs)
    (hm : Param.expP x (.varT "val" []) ∈ qs)
    (h : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.subE (.varE x) (.varT "val" []) (.varT "admininstr" [])) (adminToV a)) :
    ∃ v : Val, a = v.toAdmin := by
  obtain ⟨R, fR, tR⟩ := hq x _ hm
  have e : adminToV a = R := EvalExp.unique (evalExp_subE_iff.1 h) (evalExp_var fR)
  exact admin_of_valHead (Pure.valHead_of_typed (Pure.valsOnly_bindVals σ) (e ▸ tR))

end Silmaril.Wasm.SpecTec.Sim20.Whole
