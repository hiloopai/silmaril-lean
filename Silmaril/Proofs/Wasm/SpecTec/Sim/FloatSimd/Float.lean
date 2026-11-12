module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FloatSimd.Forward

/-!
# Family V, floats: scalar float operators and conversions, forward

The generic scalar rules `Step_pure/unop-val` (46), `binop-val` (48), `relop` (51), `cvtop-val`
(52) and `cvtop-trap` (53), constructed under the declarative reading for arbitrary IL values; then
the float constructors of Core's `NumericStep` (`floatUnOp`, `floatBinOp`, `floatRelOp`) and both
conversion constructors (`convert`, `convertTrap`, all `ConvertOp`s), forward, under `FloatTyping`
and `FloatAgree`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Vec

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecNumeric
  (Applies HasNumericRules unopValRule binopValRule relopRule cvtopValRule cvtopTrapRule)
open Silmaril.SpecTec.Equiv.ExecStepRules (pureRule)
open Silmaril.SpecTec.Equiv.Execution (constV trapV i32V)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core

/-! ## The scalar rules -/

/-- `CONST x y` over two bound variables. -/
theorem evalExp_constVar {env : Env} {ρ : VarEnv} {x y : IL.Id} {a b : Value}
    (hx : ρ.findVal? x = some a) (hy : ρ.findVal? y = some b) :
    EvalExp env ρ (.caseE "CONST" (.tupE [.varE x, .varE y])) (constV a b) :=
  evalExp_case (evalExp_tup2 (evalExp_var hx) (evalExp_var hy))

/-- `Step_pure/unop-val` (rule 46). -/
theorem spure_unopVal {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 46 unopValRule)
    {nt c₁ op c : Value} {L : List Value} (hnt : TypedV env numtypeT nt)
    (hc₁ : TypedDep env "nt" nt (numT "nt") c₁) (hop : TypedDep env "nt" nt (opT "unop_" "nt") op)
    (hc : TypedDep env "nt" nt (numT "nt") c)
    (ha : Applies env "unop_" [.val nt, .val op, .val c₁] (.list L)) (hm : c ∈ L) :
    SPure env [constV nt c₁, .case "UNOP" (.tuple [nt, op])] [constV nt c] := by
  let ρ := VarEnv.empty.bindVals [("nt", nt), ("c_1", c₁), ("unop", op), ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "nt" = some nt := rfl
  have f2 : ρ.findVal? "c_1" = some c₁ := rfl
  have f3 : ρ.findVal? "unop" = some op := rfl
  have f4 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "nt" numtypeT, .expP "c_1" (numT "nt"),
      .expP "unop" (opT "unop_" "nt"), .expP "c" (numT "nt")] :=
    QuantsOk.cons f1 (hnt ρ hρ) (QuantsOk.cons f2 (hc₁ ρ hρ f1) (QuantsOk.cons f3 (hop ρ hρ f1)
      (QuantsOk.cons f4 (hc ρ hρ f1) QuantsOk.nil)))
  have hx : EvalArgs env ρ [.expA (.varE "nt"), .expA (.varE "unop"), .expA (.varE "c_1")]
      [.val nt, .val op, .val c₁] :=
    evalArgs_var f1 (evalArgs_var f3 (evalArgs_var f2 Equiv.evalArgs_nil))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list2 (evalExp_constVar f1 f2) (evalExp_op2 f1 f3))
      (evalExp_list1 (evalExp_constVar f1 f4)))
    (prems_one (.ifPr (evalExp_mem_call f4 rfl hx ha hm)))

/-- `Step_pure/binop-val` (rule 48). -/
theorem spure_binopVal {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 48 binopValRule)
    {nt c₁ c₂ op c : Value} {L : List Value} (hnt : TypedV env numtypeT nt)
    (hc₁ : TypedDep env "nt" nt (numT "nt") c₁) (hc₂ : TypedDep env "nt" nt (numT "nt") c₂)
    (hop : TypedDep env "nt" nt (opT "binop_" "nt") op) (hc : TypedDep env "nt" nt (numT "nt") c)
    (ha : Applies env "binop_" [.val nt, .val op, .val c₁, .val c₂] (.list L)) (hm : c ∈ L) :
    SPure env [constV nt c₁, constV nt c₂, .case "BINOP" (.tuple [nt, op])] [constV nt c] := by
  let ρ := VarEnv.empty.bindVals [("nt", nt), ("c_1", c₁), ("c_2", c₂), ("binop", op), ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "nt" = some nt := rfl
  have f2 : ρ.findVal? "c_1" = some c₁ := rfl
  have f3 : ρ.findVal? "c_2" = some c₂ := rfl
  have f4 : ρ.findVal? "binop" = some op := rfl
  have f5 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "nt" numtypeT, .expP "c_1" (numT "nt"),
      .expP "c_2" (numT "nt"), .expP "binop" (opT "binop_" "nt"), .expP "c" (numT "nt")] :=
    QuantsOk.cons f1 (hnt ρ hρ) (QuantsOk.cons f2 (hc₁ ρ hρ f1) (QuantsOk.cons f3 (hc₂ ρ hρ f1)
      (QuantsOk.cons f4 (hop ρ hρ f1) (QuantsOk.cons f5 (hc ρ hρ f1) QuantsOk.nil))))
  have hx : EvalArgs env ρ [.expA (.varE "nt"), .expA (.varE "binop"), .expA (.varE "c_1"),
      .expA (.varE "c_2")] [.val nt, .val op, .val c₁, .val c₂] :=
    evalArgs_var f1 (evalArgs_var f4 (evalArgs_var f2 (evalArgs_var f3 Equiv.evalArgs_nil)))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list3 (evalExp_constVar f1 f2) (evalExp_constVar f1 f3)
        (evalExp_op2 f1 f4))
      (evalExp_list1 (evalExp_constVar f1 f5)))
    (prems_one (.ifPr (evalExp_mem_call f5 rfl hx ha hm)))

/-- `Step_pure/relop` (rule 51). -/
theorem spure_relop {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 51 relopRule)
    {nt c₁ c₂ op c : Value} (hnt : TypedV env numtypeT nt)
    (hc₁ : TypedDep env "nt" nt (numT "nt") c₁) (hc₂ : TypedDep env "nt" nt (numT "nt") c₂)
    (hop : TypedDep env "nt" nt (opT "relop_" "nt") op) (hc : TypedV env i32T c)
    (ha : Applies env "relop_" [.val nt, .val op, .val c₁, .val c₂] c) :
    SPure env [constV nt c₁, constV nt c₂, .case "RELOP" (.tuple [nt, op])] [constV i32V c] := by
  let ρ := VarEnv.empty.bindVals [("nt", nt), ("c_1", c₁), ("c_2", c₂), ("relop", op), ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "nt" = some nt := rfl
  have f2 : ρ.findVal? "c_1" = some c₁ := rfl
  have f3 : ρ.findVal? "c_2" = some c₂ := rfl
  have f4 : ρ.findVal? "relop" = some op := rfl
  have f5 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "nt" numtypeT, .expP "c_1" (numT "nt"),
      .expP "c_2" (numT "nt"), .expP "relop" (opT "relop_" "nt"), .expP "c" i32T] :=
    QuantsOk.cons f1 (hnt ρ hρ) (QuantsOk.cons f2 (hc₁ ρ hρ f1) (QuantsOk.cons f3 (hc₂ ρ hρ f1)
      (QuantsOk.cons f4 (hop ρ hρ f1) (QuantsOk.cons f5 (hc ρ hρ) QuantsOk.nil))))
  have hx : EvalArgs env ρ [.expA (.varE "nt"), .expA (.varE "relop"), .expA (.varE "c_1"),
      .expA (.varE "c_2")] [.val nt, .val op, .val c₁, .val c₂] :=
    evalArgs_var f1 (evalArgs_var f4 (evalArgs_var f2 (evalArgs_var f3 Equiv.evalArgs_nil)))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list3 (evalExp_constVar f1 f2) (evalExp_constVar f1 f3)
        (evalExp_op2 f1 f4))
      (evalExp_list1 (evalExp_constI32 f5)))
    (prems_one (.ifPr (evalExp_eq_call f5 rfl hx ha)))

/-- `Step_pure/cvtop-val` (rule 52). -/
theorem spure_cvtopVal {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 52 cvtopValRule)
    {nt₁ nt₂ c₁ op c : Value} {L : List Value} (hnt₁ : TypedV env numtypeT nt₁)
    (hnt₂ : TypedV env numtypeT nt₂) (hc₁ : TypedDep env "nt_1" nt₁ (numT "nt_1") c₁)
    (hop : TypedDep2 env "nt_1" nt₁ "nt_2" nt₂ cvtopT op)
    (hc : TypedDep env "nt_2" nt₂ (numT "nt_2") c)
    (ha : Applies env "cvtop__" [.val nt₁, .val nt₂, .val op, .val c₁] (.list L)) (hm : c ∈ L) :
    SPure env [constV nt₁ c₁, .case "CVTOP" (.tuple [nt₂, nt₁, op])] [constV nt₂ c] := by
  let ρ := VarEnv.empty.bindVals [("nt_1", nt₁), ("c_1", c₁), ("nt_2", nt₂), ("cvtop", op),
    ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "nt_1" = some nt₁ := rfl
  have f2 : ρ.findVal? "c_1" = some c₁ := rfl
  have f3 : ρ.findVal? "nt_2" = some nt₂ := rfl
  have f4 : ρ.findVal? "cvtop" = some op := rfl
  have f5 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "nt_1" numtypeT, .expP "c_1" (numT "nt_1"),
      .expP "nt_2" numtypeT, .expP "cvtop" cvtopT, .expP "c" (numT "nt_2")] :=
    QuantsOk.cons f1 (hnt₁ ρ hρ) (QuantsOk.cons f2 (hc₁ ρ hρ f1) (QuantsOk.cons f3 (hnt₂ ρ hρ)
      (QuantsOk.cons f4 (hop ρ hρ f1 f3) (QuantsOk.cons f5 (hc ρ hρ f3) QuantsOk.nil))))
  have hx : EvalArgs env ρ [.expA (.varE "nt_1"), .expA (.varE "nt_2"), .expA (.varE "cvtop"),
      .expA (.varE "c_1")] [.val nt₁, .val nt₂, .val op, .val c₁] :=
    evalArgs_var f1 (evalArgs_var f3 (evalArgs_var f4 (evalArgs_var f2 Equiv.evalArgs_nil)))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list2 (evalExp_constVar f1 f2) (evalExp_op3 f3 f1 f4))
      (evalExp_list1 (evalExp_constVar f3 f5)))
    (prems_one (.ifPr (evalExp_mem_call f5 rfl hx ha hm)))

/-- `Step_pure/cvtop-trap` (rule 53). -/
theorem spure_cvtopTrap {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 53 cvtopTrapRule)
    {nt₁ nt₂ c₁ op : Value} (hnt₁ : TypedV env numtypeT nt₁) (hnt₂ : TypedV env numtypeT nt₂)
    (hc₁ : TypedDep env "nt_1" nt₁ (numT "nt_1") c₁)
    (hop : TypedDep2 env "nt_1" nt₁ "nt_2" nt₂ cvtopT op)
    (ha : Applies env "cvtop__" [.val nt₁, .val nt₂, .val op, .val c₁] (.list [])) :
    SPure env [constV nt₁ c₁, .case "CVTOP" (.tuple [nt₂, nt₁, op])] [trapV] := by
  let ρ := VarEnv.empty.bindVals [("nt_1", nt₁), ("c_1", c₁), ("nt_2", nt₂), ("cvtop", op)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "nt_1" = some nt₁ := rfl
  have f2 : ρ.findVal? "c_1" = some c₁ := rfl
  have f3 : ρ.findVal? "nt_2" = some nt₂ := rfl
  have f4 : ρ.findVal? "cvtop" = some op := rfl
  have hq : QuantsOk env ρ [.expP "nt_1" numtypeT, .expP "c_1" (numT "nt_1"),
      .expP "nt_2" numtypeT, .expP "cvtop" cvtopT] :=
    QuantsOk.cons f1 (hnt₁ ρ hρ) (QuantsOk.cons f2 (hc₁ ρ hρ f1) (QuantsOk.cons f3 (hnt₂ ρ hρ)
      (QuantsOk.cons f4 (hop ρ hρ f1 f3) QuantsOk.nil)))
  have hx : EvalArgs env ρ [.expA (.varE "nt_1"), .expA (.varE "nt_2"), .expA (.varE "cvtop"),
      .expA (.varE "c_1")] [.val nt₁, .val nt₂, .val op, .val c₁] :=
    evalArgs_var f1 (evalArgs_var f3 (evalArgs_var f4 (evalArgs_var f2 Equiv.evalArgs_nil)))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list2 (evalExp_constVar f1 f2) (evalExp_op3 f3 f1 f4))
      (evalExp_list1 evalExp_trap))
    (prems_one (.ifPr (evalExp_call_nil rfl hx ha)))

/-! ## The encoding of scalar instructions -/

/-- `Encode.toValue` on number types is `numTypeV`. -/
theorem encode_numType (t : NumType) : Encode.toValue t = numTypeV t := by
  rcases t with t | t <;> cases t <;> rfl

/-- A number value as an instruction is `CONST nt c`. -/
theorem adminToV_valNum (n : NumVal) :
    adminToV (Val.num n).toAdmin = constV (numTypeV n.type) (numV n) := by
  obtain ⟨t, b⟩ := n
  rcases t with t | t <;> cases t <;> rfl

/-- `fN.const`. -/
theorem instrToV_floatConst (t : FloatType) (x : BitVec t.width) :
    instrToV (.floatConst t x) = constV (numTypeV (.float t)) (floatV t x) := by
  cases t <;> rfl

/-- `fN.unop`. -/
theorem instrToV_floatUnOp (t : FloatType) (op : FloatUnOp) :
    instrToV (.floatUnOp t op) = .case "UNOP" (.tuple [numTypeV (.float t), fUnOpV op]) := by
  cases t <;> cases op <;> rfl

/-- `fN.binop`. -/
theorem instrToV_floatBinOp (t : FloatType) (op : FloatBinOp) :
    instrToV (.floatBinOp t op) = .case "BINOP" (.tuple [numTypeV (.float t), fBinOpV op]) := by
  cases t <;> cases op <;> rfl

/-- `fN.relop`. -/
theorem instrToV_floatRelOp (t : FloatType) (op : FloatRelOp) :
    instrToV (.floatRelOp t op) =
      .case "RELOP" (.tuple [numTypeV (.float t), vFloatRelOpV op]) := by
  cases t <;> cases op <;> rfl

/-- `convertInstrV` agrees with `Equiv.instrV` on every conversion `Equiv.instrV` encodes (all
but the saturating truncations). -/
theorem convertInstrV_eq_instrV (op : ConvertOp) (hop : ∀ f i s, op ≠ .truncSat f i s) :
    convertInstrV op = Equiv.instrV (.convert op) := by
  cases op with
  | wrap => rfl
  | extend s => cases s <;> rfl
  | trunc f i s => cases f <;> cases i <;> cases s <;> rfl
  | truncSat f i s => exact absurd rfl (hop f i s)
  | convert i f s => cases i <;> cases f <;> cases s <;> rfl
  | demote => rfl
  | promote => rfl
  | reinterpretInt f => cases f <;> rfl
  | reinterpretFloat i => cases i <;> rfl

/-! ## `NumericStep`'s float and conversion constructors, forward -/

/-- Every scalar numeric rule fact about the pinned script holds of `simEnv B`. -/
theorem hasNumericRules_simEnv (B : Builtins) : HasNumericRules (simEnv B) := by
  have h := Silmaril.SpecTec.Equiv.ExecNumeric.hasNumericRules_wasm30
  cases h
  constructor <;> (apply hasRuleAt_simEnv; assumption)

section

variable {H : Type} {env : Env} {hn : H → String} {P : Profile}
  (T : TypingFacts env hn) (hr : HasRuleAt env "Step" "%~>%" 0 pureRule)
  (N : HasNumericRules env) (Ty : FloatTyping env) (A : FloatAgree env P)
  {s : Store H} {f : Frame}

include T hr N Ty A

/-- `NumericStep.floatUnOp`, forward (`Step_pure/unop-val`). -/
theorem fwd_floatUnOp {t : FloatType} {op : FloatUnOp} {x z : BitVec t.width}
    (h : floatUnOpP P t op x z) :
    FwdP env hn ⟨s, f, [.plain (.floatConst t x), .plain (.floatUnOp t op)]⟩
      ⟨s, f, [.plain (.floatConst t z)]⟩ := by
  obtain ⟨L, ha, hL⟩ := A.unop t op x
  have hm : floatV t z ∈ L := (hL _).2 ⟨z, h, rfl⟩
  have hs : SPure env [constV (numTypeV (.float t)) (floatV t x),
      .case "UNOP" (.tuple [numTypeV (.float t), fUnOpV op])]
      [constV (numTypeV (.float t)) (floatV t z)] :=
    spure_unopVal N.unopVal (Ty.numtype _) (Ty.num "nt" ⟨.float t, x⟩) (Ty.unop t op)
      (Ty.num "nt" ⟨.float t, z⟩) ha hm
  have e₁ : adminsToV [.plain (.floatConst t x), .plain (.floatUnOp t op)] =
      [constV (numTypeV (.float t)) (floatV t x),
        .case "UNOP" (.tuple [numTypeV (.float t), fUnOpV op])] := by
    simp only [adminsToV, adminToV, instrToV_floatConst, instrToV_floatUnOp]
  have e₂ : adminsToV [.plain (.floatConst t z)] = [constV (numTypeV (.float t)) (floatV t z)] := by
    simp only [adminsToV, adminToV, instrToV_floatConst]
  exact fwd_of_spure T hr (e₁ ▸ e₂ ▸ hs)

/-- `NumericStep.floatBinOp`, forward (`Step_pure/binop-val`). -/
theorem fwd_floatBinOp {t : FloatType} {op : FloatBinOp} {x y z : BitVec t.width}
    (h : floatBinOpP P t op x y z) :
    FwdP env hn ⟨s, f, [.plain (.floatConst t x), .plain (.floatConst t y),
      .plain (.floatBinOp t op)]⟩ ⟨s, f, [.plain (.floatConst t z)]⟩ := by
  obtain ⟨L, ha, hL⟩ := A.binop t op x y
  have hm : floatV t z ∈ L := (hL _).2 ⟨z, h, rfl⟩
  have hs : SPure env [constV (numTypeV (.float t)) (floatV t x),
      constV (numTypeV (.float t)) (floatV t y),
      .case "BINOP" (.tuple [numTypeV (.float t), fBinOpV op])]
      [constV (numTypeV (.float t)) (floatV t z)] :=
    spure_binopVal N.binopVal (Ty.numtype _) (Ty.num "nt" ⟨.float t, x⟩)
      (Ty.num "nt" ⟨.float t, y⟩) (Ty.binop t op) (Ty.num "nt" ⟨.float t, z⟩) ha hm
  have e₁ : adminsToV [.plain (.floatConst t x), .plain (.floatConst t y),
      .plain (.floatBinOp t op)] =
      [constV (numTypeV (.float t)) (floatV t x), constV (numTypeV (.float t)) (floatV t y),
        .case "BINOP" (.tuple [numTypeV (.float t), fBinOpV op])] := by
    simp only [adminsToV, adminToV, instrToV_floatConst, instrToV_floatBinOp]
  have e₂ : adminsToV [.plain (.floatConst t z)] = [constV (numTypeV (.float t)) (floatV t z)] := by
    simp only [adminsToV, adminToV, instrToV_floatConst]
  exact fwd_of_spure T hr (e₁ ▸ e₂ ▸ hs)

/-- `NumericStep.floatRelOp`, forward (`Step_pure/relop`). -/
theorem fwd_floatRelOp {t : FloatType} {op : FloatRelOp} {x y : BitVec t.width} :
    FwdP env hn ⟨s, f, [.plain (.floatConst t x), .plain (.floatConst t y),
      .plain (.floatRelOp t op)]⟩ ⟨s, f, [constI32 (floatRelOp t op x y)]⟩ := by
  have hs : SPure env [constV (numTypeV (.float t)) (floatV t x),
      constV (numTypeV (.float t)) (floatV t y),
      .case "RELOP" (.tuple [numTypeV (.float t), vFloatRelOpV op])]
      [constV i32V (i32NV (floatRelOp t op x y))] :=
    spure_relop N.relop (Ty.numtype _) (Ty.num "nt" ⟨.float t, x⟩) (Ty.num "nt" ⟨.float t, y⟩)
      (Ty.relop t op) (Ty.i32 _) (A.relop t op x y)
  have e₁ : adminsToV [.plain (.floatConst t x), .plain (.floatConst t y),
      .plain (.floatRelOp t op)] =
      [constV (numTypeV (.float t)) (floatV t x), constV (numTypeV (.float t)) (floatV t y),
        .case "RELOP" (.tuple [numTypeV (.float t), vFloatRelOpV op])] := by
    simp only [adminsToV, adminToV, instrToV_floatConst, instrToV_floatRelOp]
  exact fwd_of_spure T hr (e₁ ▸ hs)

/-- `NumericStep.convert`, forward (`Step_pure/cvtop-val`), for every `ConvertOp`. -/
theorem fwd_convert {op : ConvertOp} {x : BitVec op.source.width}
    {z : BitVec op.target.width} (h : convertP P op x (.ok z)) :
    FwdP env hn ⟨s, f, [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)]⟩
      ⟨s, f, [(Val.num ⟨op.target, z⟩).toAdmin]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.convert op) := typed_last2 T (typed_code T hc)
  obtain ⟨L, ha, hL, -⟩ := A.cvtop op x
  have hm : numV ⟨op.target, z⟩ ∈ L := (hL _).2 ⟨z, h, rfl⟩
  have hs : SPure env [constV (numTypeV op.source) (numV ⟨op.source, x⟩),
      .case "CVTOP" (.tuple [numTypeV op.target, numTypeV op.source, cvtOpV op])]
      [constV (numTypeV op.target) (numV ⟨op.target, z⟩)] :=
    spure_cvtopVal N.cvtopVal (Ty.numtype _) (Ty.numtype _) (Ty.num "nt_1" ⟨op.source, x⟩)
      (Ty.cvtop op hi) (Ty.num "nt_2" ⟨op.target, z⟩) ha hm
  have e₁ : adminsToV [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)] =
      [constV (numTypeV op.source) (numV ⟨op.source, x⟩),
        .case "CVTOP" (.tuple [numTypeV op.target, numTypeV op.source, cvtOpV op])] := by
    simp only [adminsToV, adminToV_valNum]
    rfl
  have e₂ : adminsToV [(Val.num ⟨op.target, z⟩).toAdmin] =
      [constV (numTypeV op.target) (numV ⟨op.target, z⟩)] := by
    simp only [adminsToV, adminToV_valNum]
  exact fwd_of_spure T hr (e₁ ▸ e₂ ▸ hs) hc hc'

/-- `NumericStep.convertTrap`, forward (`Step_pure/cvtop-trap`), for every `ConvertOp`. -/
theorem fwd_convertTrap {op : ConvertOp} {x : BitVec op.source.width} {e : FloatTrap}
    (h : convertP P op x (.error e)) :
    FwdP env hn ⟨s, f, [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)]⟩
      ⟨s, f, [.trap]⟩ := by
  intro hc hc'
  have hi : InstrTyped env (.convert op) := typed_last2 T (typed_code T hc)
  obtain ⟨L, ha, -, hnil⟩ := A.cvtop op x
  have hL : L = [] := hnil.2 ⟨e, h⟩
  have ha' : Applies env "cvtop__" [.val (numTypeV op.source), .val (numTypeV op.target),
      .val (cvtOpV op), .val (numV ⟨op.source, x⟩)] (.list []) := hL ▸ ha
  have hs : SPure env [constV (numTypeV op.source) (numV ⟨op.source, x⟩),
      .case "CVTOP" (.tuple [numTypeV op.target, numTypeV op.source, cvtOpV op])] [trapV] :=
    spure_cvtopTrap N.cvtopTrap (Ty.numtype _) (Ty.numtype _) (Ty.num "nt_1" ⟨op.source, x⟩)
      (Ty.cvtop op hi) ha'
  have e₁ : adminsToV [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)] =
      [constV (numTypeV op.source) (numV ⟨op.source, x⟩),
        .case "CVTOP" (.tuple [numTypeV op.target, numTypeV op.source, cvtOpV op])] := by
    simp only [adminsToV, adminToV_valNum]
    rfl
  exact fwd_of_spure T hr (e₁ ▸ hs) hc hc'

end

end Silmaril.Wasm.SpecTec.Sim.Vec
