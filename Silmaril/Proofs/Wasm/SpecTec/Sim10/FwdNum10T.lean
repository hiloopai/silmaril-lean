module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdBlock10T

/-!
# The 1.0 numeric rules forward in `simEnv10T`

Round 4's numeric leaves (`unop`, `binop`, `testop`, `relop`, `cvtop`, values and traps) at
`FwdAt10T`, from `NumAgree10` at `simEnv10` (the premises are evaluations, read in `simEnv10`
and moved by `fires_of_ruleAtT`). The quantifiers are typed from the code in `simEnv10T`
(`fam_of_admin10T`, `op_of_admin10T`, `val_of_admin10T`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef evalArgs_three evalArgs_four)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk TypedV evalExp_case evalExp_tup2 evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase)
open Silmaril.Wasm.SpecTec.Sim20 (numTypeV)
open Silmaril.Wasm.SpecTec.Sim20.Pure (fires_of_ruleAt prems_one evalExp_pair evalExp_list2
  memValue_list_iff evalExp_caseNil evalExp_list0)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
set_option maxRecDepth 100000
open Silmaril.Wasm.SpecTec.Sim20 (intBinOpV floatUnOpV floatBinOpV intTestOpV intRelOpV
  floatRelOpV)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)

variable {B : Builtins} {H : Type} {hn : H → String}

/-- `admininstr` at its numeric cases, in `simEnv10T`. -/
theorem findTyp_admininstr10_numT : ∃ cs, (simEnv10T B).findTyp? "admininstr" =
      some ([], [.instD [] [] (.variantT cs)]) ∧ findCase cs "CONST" = some (famT10 "val_", []) ∧
    findCase cs "UNOP" = some (famT10 "unop_", []) ∧
    findCase cs "BINOP" = some (famT10 "binop_", []) ∧
    findCase cs "TESTOP" = some (famT10 "testop_", []) ∧
    findCase cs "RELOP" = some (famT10 "relop_", []) ∧
    ∃ ps, findCase cs "CVTOP" = some (.tupT [.mk "valtype_1" (.varT "valtype" []),
      .mk "valtype_2" (.varT "valtype" []), .mk "cvtop" (.varT "cvtop" [])], ps) :=
  let ⟨_, h, h₁, h₂, h₃, h₄, h₅, ps, h₆⟩ := findTyp_admininstr10_num (B := B)
  ⟨_, adminT_lift h, findCaseT h₁ (by decide), findCaseT h₂ (by decide), findCaseT h₃ (by decide),
    findCaseT h₄ (by decide), findCaseT h₅ (by decide), ps, findCaseT h₆ (by decide)⟩

/-- Every V1 value type is a typed `valtype` in `simEnv10T`. -/
theorem typedV_valtype10T (t : V1.ValType) :
    TypedV (simEnv10T B) (.varT "valtype" []) (valTypeV t) :=
  typedV10T (typedV_valtype10 t)

/-- A pure step from both typings, in `simEnv10T`. -/
theorem fwdAt10T_of_spure2 {s : Store H} {f : Frame} {code code' : List Admin}
    (hp : TypedV (simEnv10T B) adminsT (.list (adminsToV code)) →
      TypedV (simEnv10T B) adminsT (.list (adminsToV code')) →
      Sim.SPure (simEnv10T B) (adminsToV code) (adminsToV code')) :
    FwdAt10T B hn ⟨s, f, code⟩ ⟨s, f, code'⟩ :=
  fun hz _ hc hc' => (StoreFix.sstepB10T_iff B).2 (sstep10_pureT hz hc hc' (hp hc hc'))

/-- **The payload of a typed `OP (n, w)` with an `(valtype, X_(valtype))` case is an `X_(x)`**,
in any scope binding `x` to `n`. -/
theorem fam_of_admin10T {cs : List TypCase} {op : MixopS} {X x : IL.Id} {n w : Value}
    (htd : (simEnv10T B).findTyp? "admininstr" = some ([], [.instD [] [] (.variantT cs)]))
    (hc : findCase cs op = some (famT10 X, []))
    (h : TypedV (simEnv10T B) adminT10 (.case op (.tuple [n, w]))) {ρ : VarEnv}
    (hρ : ρ.findVal? x = some n) : HasTyp (simEnv10T B) ρ (.varT X [.expA (.varE x)]) w := by
  have hp := hasTyp_closedVariant_inv valsOnly_empty htd (h _ valsOnly_empty) hc
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 hp
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨y, ys, hys, -, htup'⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨rfl, rfl⟩ := List.cons.inj hys
  obtain ⟨y', ys', hys', hy', -⟩ := hasTypTup_cons_iff.1 htup'
  obtain ⟨rfl, -⟩ := List.cons.inj hys'
  exact hasTyp_fam_rebind hy' (by simp) hρ

/-- The payload of a typed value is a `val_(x)`. -/
theorem val_of_admin10T {v : Execution.Runtime.Value} {x : IL.Id}
    (h : TypedV (simEnv10T B) adminT10 (adminToV (value v))) {ρ : VarEnv}
    (hρ : ρ.findVal? x = some (valTypeV v.type)) :
    HasTyp (simEnv10T B) ρ (.varT "val_" [.expA (.varE x)]) (numV v) := by
  obtain ⟨cs, htd, hc, -⟩ := findTyp_admininstr10_numT (B := B)
  rw [adminToV_value] at h
  exact fam_of_admin10T htd hc h hρ

/-- The operator of a typed `OP (n, opv)` instruction is an `X_(x)`. -/
theorem op_of_admin10T {op : MixopS} {X x : IL.Id} {i : V1.Instr} {n opv : Value}
    (hcs : ∃ cs, (simEnv10T B).findTyp? "admininstr" = some ([], [.instD [] [] (.variantT cs)]) ∧
      findCase cs op = some (famT10 X, []))
    (hi : instrToV i = .case op (.tuple [n, opv]))
    (h : TypedV (simEnv10T B) adminT10 (adminToV (.source i))) {ρ : VarEnv}
    (hρ : ρ.findVal? x = some n) : HasTyp (simEnv10T B) ρ (.varT X [.expA (.varE x)]) opv := by
  obtain ⟨cs, htd, hc⟩ := hcs
  have h' : TypedV (simEnv10T B) adminT10 (.case op (.tuple [n, opv])) := hi ▸ h
  exact fam_of_admin10T htd hc h' hρ

/-- The second of three typed elements. -/
theorem typedV_third10T {a b c : Admin} {l : List Admin}
    (h : TypedV (simEnv10T B) adminsT (.list (adminsToV (a :: b :: c :: l)))) :
    TypedV (simEnv10T B) adminT10 (adminToV c) :=
  Sim.typedV_list_iff.1 h _ (.tail _ (.tail _ (.head _)))

theorem unopCase10T : ∃ cs, (simEnv10T B).findTyp? "admininstr" =
    some ([], [.instD [] [] (.variantT cs)]) ∧ findCase cs "UNOP" = some (famT10 "unop_", []) := by
  obtain ⟨cs, htd, -, h, -⟩ := findTyp_admininstr10_numT (B := B)
  exact ⟨cs, htd, h⟩

theorem binopCase10T : ∃ cs, (simEnv10T B).findTyp? "admininstr" =
    some ([], [.instD [] [] (.variantT cs)]) ∧ findCase cs "BINOP" = some (famT10 "binop_", []) := by
  obtain ⟨cs, htd, -, -, h, -⟩ := findTyp_admininstr10_numT (B := B)
  exact ⟨cs, htd, h⟩

theorem testopCase10T : ∃ cs, (simEnv10T B).findTyp? "admininstr" =
    some ([], [.instD [] [] (.variantT cs)]) ∧ findCase cs "TESTOP" = some (famT10 "testop_", []) := by
  obtain ⟨cs, htd, -, -, -, h, -⟩ := findTyp_admininstr10_numT (B := B)
  exact ⟨cs, htd, h⟩

theorem relopCase10T : ∃ cs, (simEnv10T B).findTyp? "admininstr" =
    some ([], [.instD [] [] (.variantT cs)]) ∧ findCase cs "RELOP" = some (famT10 "relop_", []) := by
  obtain ⟨cs, htd, -, -, -, -, h, -⟩ := findTyp_admininstr10_numT (B := B)
  exact ⟨cs, htd, h⟩

/-- **`unop-val` (20) forward**: `CONST t c_1; UNOP t op` to `CONST t c`, `c ∈ $unop_(t, op, c_1)`. -/
theorem fwdAt10T_unopVal (s : Store H) (f : Frame) (v u : Execution.Runtime.Value) (i : V1.Instr)
    (opv : Value) (vs : List Value) (hty : u.type = v.type)
    (hi : instrToV i = .case "UNOP" (.tuple [valTypeV v.type, opv]))
    (happ : Applies (simEnv10 B) "unop_" [.val (valTypeV v.type), .val opv, .val (numV v)]
      (.list vs)) (hm : numV u ∈ vs) :
    FwdAt10T B hn ⟨s, f, [value v, .source i]⟩ ⟨s, f, [value u]⟩ := by
  refine fwdAt10T_of_spure2 fun hc hc' => spure10T_of_fires (k := 20) ?_
  let σ : List (IL.Id × Value) :=
    [("t", valTypeV v.type), ("c_1", numV v), ("unop", opv), ("c", numV u)]
  have ft : (VarEnv.empty.bindVals σ).findVal? "t" = some (valTypeV v.type) := rfl
  have f₁ : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (numV v) := rfl
  have fo : (VarEnv.empty.bindVals σ).findVal? "unop" = some opv := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (numV u) := rfl
  have ho := op_of_admin10T unopCase10T hi (typedV_second10T hc) ft
  have hcode : adminsToV [value v, .source i] = [.case "CONST" (.tuple [valTypeV v.type, numV v]),
      .case "UNOP" (.tuple [valTypeV v.type, opv])] := by
    rw [adminsToV_vi, ← hi]
    rfl
  have hout : adminsToV [value u] = [.case "CONST" (.tuple [valTypeV v.type, numV u])] := by
    rw [adminsToV_v, ← hty]
    rfl
  rw [hcode, hout]
  exact fires_of_ruleAtT (hasRuleAt10_unopVal B) σ
    (QuantsOk.cons ft (typedV_valtype10T v.type _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons f₁ (val_of_admin10T (typedV_head10T hc) ft) (QuantsOk.cons fo ho
        (QuantsOk.cons fc (val_of_admin10T (typedV_head10T hc') (hty ▸ ft)) QuantsOk.nil))))
    (evalExp_tup2 (evalExp_list2 (evalExp_pair ft f₁) (evalExp_pair ft fo))
      (evalExp_list1 (evalExp_pair ft fc)))
    (prems_one (.ifPr (evalExp_memE_iff.2 ⟨_, _, evalExp_var fc, evalExp_callE_iff.2
      ((applies_iff_callDef rfl (evalArgs_three ft fo f₁)).1 happ), memValue_list_iff.2 hm⟩)))

/-- **`binop-val` (22) forward.** -/
theorem fwdAt10T_binopVal (s : Store H) (f : Frame) (v₁ v₂ u : Execution.Runtime.Value)
    (i : V1.Instr) (opv : Value) (vs : List Value) (hty₂ : v₂.type = v₁.type)
    (hty : u.type = v₁.type) (hi : instrToV i = .case "BINOP" (.tuple [valTypeV v₁.type, opv]))
    (happ : Applies (simEnv10 B) "binop_" [.val (valTypeV v₁.type), .val opv, .val (numV v₁),
      .val (numV v₂)] (.list vs)) (hm : numV u ∈ vs) :
    FwdAt10T B hn ⟨s, f, [value v₁, value v₂, .source i]⟩ ⟨s, f, [value u]⟩ := by
  refine fwdAt10T_of_spure2 fun hc hc' => spure10T_of_fires (k := 22) ?_
  let σ : List (IL.Id × Value) := [("t", valTypeV v₁.type), ("c_1", numV v₁), ("c_2", numV v₂),
    ("binop", opv), ("c", numV u)]
  have ft : (VarEnv.empty.bindVals σ).findVal? "t" = some (valTypeV v₁.type) := rfl
  have f₁ : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (numV v₁) := rfl
  have f₂ : (VarEnv.empty.bindVals σ).findVal? "c_2" = some (numV v₂) := rfl
  have fo : (VarEnv.empty.bindVals σ).findVal? "binop" = some opv := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (numV u) := rfl
  have ho := op_of_admin10T binopCase10T hi (typedV_third10T hc) ft
  have hout : adminsToV [value u] = [.case "CONST" (.tuple [valTypeV v₁.type, numV u])] := by
    rw [adminsToV_v, ← hty]
    rfl
  rw [adminsToV_vvo hty₂ hi, hout]
  exact fires_of_ruleAtT (hasRuleAt10_binopVal B) σ
    (QuantsOk.cons ft (typedV_valtype10T v₁.type _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons f₁ (val_of_admin10T (typedV_head10T hc) ft)
        (QuantsOk.cons f₂ (val_of_admin10T (typedV_second10T hc) (hty₂ ▸ ft))
          (QuantsOk.cons fo ho
            (QuantsOk.cons fc (val_of_admin10T (typedV_head10T hc') (hty ▸ ft)) QuantsOk.nil)))))
    (evalExp_tup2 (Sim20.Pure.evalExp_list3 (evalExp_pair ft f₁) (evalExp_pair ft f₂)
      (evalExp_pair ft fo)) (evalExp_list1 (evalExp_pair ft fc)))
    (prems_one (.ifPr (evalExp_memE_iff.2 ⟨_, _, evalExp_var fc, evalExp_callE_iff.2
      ((applies_iff_callDef rfl (evalArgs_four ft fo f₁ f₂)).1 happ), memValue_list_iff.2 hm⟩)))

/-- **`binop-trap` (23) forward.** -/
theorem fwdAt10T_binopTrap (s : Store H) (f : Frame) (v₁ v₂ : Execution.Runtime.Value)
    (i : V1.Instr) (opv : Value) (hty₂ : v₂.type = v₁.type)
    (hi : instrToV i = .case "BINOP" (.tuple [valTypeV v₁.type, opv]))
    (happ : Applies (simEnv10 B) "binop_" [.val (valTypeV v₁.type), .val opv, .val (numV v₁),
      .val (numV v₂)] (.list [])) :
    FwdAt10T B hn ⟨s, f, [value v₁, value v₂, .source i]⟩ ⟨s, f, [.trap]⟩ := by
  refine fwdAt10T_of_spure2 fun hc _ => spure10T_of_fires (k := 23) ?_
  let σ : List (IL.Id × Value) := [("t", valTypeV v₁.type), ("c_1", numV v₁), ("c_2", numV v₂),
    ("binop", opv)]
  have ft : (VarEnv.empty.bindVals σ).findVal? "t" = some (valTypeV v₁.type) := rfl
  have f₁ : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (numV v₁) := rfl
  have f₂ : (VarEnv.empty.bindVals σ).findVal? "c_2" = some (numV v₂) := rfl
  have fo : (VarEnv.empty.bindVals σ).findVal? "binop" = some opv := rfl
  have ho := op_of_admin10T binopCase10T hi (typedV_third10T hc) ft
  rw [adminsToV_vvo hty₂ hi]
  exact fires_of_ruleAtT (hasRuleAt10_binopTrap B) σ
    (QuantsOk.cons ft (typedV_valtype10T v₁.type _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons f₁ (val_of_admin10T (typedV_head10T hc) ft)
        (QuantsOk.cons f₂ (val_of_admin10T (typedV_second10T hc) (hty₂ ▸ ft))
          (QuantsOk.cons fo ho QuantsOk.nil))))
    (evalExp_tup2 (Sim20.Pure.evalExp_list3 (evalExp_pair ft f₁) (evalExp_pair ft f₂)
      (evalExp_pair ft fo)) (evalExp_list1 evalExp_caseNil))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_callE_iff.2
      ((applies_iff_callDef rfl (evalArgs_four ft fo f₁ f₂)).1 happ), evalExp_list0,
      cmpValues_eq_self _⟩)))

/-- The `val_(I32)` payload of a typed `i32` result. -/
theorem typedV_i32Res10T {r : BitVec 32}
    (h : TypedV (simEnv10T B) adminsT (.list (adminsToV [value (.int .i32 r)]))) :
    TypedV (simEnv10T B) valI32T (pctV r.toNat) :=
  typedV_valI32_of_const10T (by
    have h' := typedV_head10T h
    rwa [adminToV_value] at h')

/-- **`testop` (24) forward.** -/
theorem fwdAt10T_testop (s : Store H) (f : Frame) (v : Execution.Runtime.Value) (i : V1.Instr)
    (opv : Value) (r : BitVec 32)
    (hi : instrToV i = .case "TESTOP" (.tuple [valTypeV v.type, opv]))
    (happ : Applies (simEnv10 B) "testop_" [.val (valTypeV v.type), .val opv, .val (numV v)]
      (pctV r.toNat)) :
    FwdAt10T B hn ⟨s, f, [value v, .source i]⟩ ⟨s, f, [value (.int .i32 r)]⟩ := by
  refine fwdAt10T_of_spure2 fun hc hc' => spure10T_of_fires (k := 24) ?_
  let σ : List (IL.Id × Value) := [("t", valTypeV v.type), ("c_1", numV v), ("testop", opv),
    ("c", pctV r.toNat)]
  have ft : (VarEnv.empty.bindVals σ).findVal? "t" = some (valTypeV v.type) := rfl
  have f₁ : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (numV v) := rfl
  have fo : (VarEnv.empty.bindVals σ).findVal? "testop" = some opv := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV r.toNat) := rfl
  have ho := op_of_admin10T testopCase10T hi (typedV_second10T hc)
    ft
  rw [adminsToV_vo hi, adminsToV_i32]
  exact fires_of_ruleAtT (hasRuleAt10_testop B) σ
    (QuantsOk.cons ft (typedV_valtype10T v.type _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons f₁ (val_of_admin10T (typedV_head10T hc) ft) (QuantsOk.cons fo ho
        (QuantsOk.cons fc (typedV_i32Res10T hc' _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))))
    (evalExp_tup2 (evalExp_list2 (evalExp_pair ft f₁) (evalExp_pair ft fo))
      (evalExp_list1 (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var fc)))))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_var fc, evalExp_callE_iff.2
      ((applies_iff_callDef rfl (evalArgs_three ft fo f₁)).1 happ), cmpValues_eq_self _⟩)))

/-- **`relop` (25) forward.** -/
theorem fwdAt10T_relop (s : Store H) (f : Frame) (v₁ v₂ : Execution.Runtime.Value) (i : V1.Instr)
    (opv : Value) (r : BitVec 32) (hty₂ : v₂.type = v₁.type)
    (hi : instrToV i = .case "RELOP" (.tuple [valTypeV v₁.type, opv]))
    (happ : Applies (simEnv10 B) "relop_" [.val (valTypeV v₁.type), .val opv, .val (numV v₁),
      .val (numV v₂)] (pctV r.toNat)) :
    FwdAt10T B hn ⟨s, f, [value v₁, value v₂, .source i]⟩ ⟨s, f, [value (.int .i32 r)]⟩ := by
  refine fwdAt10T_of_spure2 fun hc hc' => spure10T_of_fires (k := 25) ?_
  let σ : List (IL.Id × Value) := [("t", valTypeV v₁.type), ("c_1", numV v₁), ("c_2", numV v₂),
    ("relop", opv), ("c", pctV r.toNat)]
  have ft : (VarEnv.empty.bindVals σ).findVal? "t" = some (valTypeV v₁.type) := rfl
  have f₁ : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (numV v₁) := rfl
  have f₂ : (VarEnv.empty.bindVals σ).findVal? "c_2" = some (numV v₂) := rfl
  have fo : (VarEnv.empty.bindVals σ).findVal? "relop" = some opv := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV r.toNat) := rfl
  have ho := op_of_admin10T relopCase10T hi (typedV_third10T hc) ft
  rw [adminsToV_vvo hty₂ hi, adminsToV_i32]
  exact fires_of_ruleAtT (hasRuleAt10_relop B) σ
    (QuantsOk.cons ft (typedV_valtype10T v₁.type _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons f₁ (val_of_admin10T (typedV_head10T hc) ft)
        (QuantsOk.cons f₂ (val_of_admin10T (typedV_second10T hc) (hty₂ ▸ ft))
          (QuantsOk.cons fo ho
            (QuantsOk.cons fc (typedV_i32Res10T hc' _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))))
    (evalExp_tup2 (Sim20.Pure.evalExp_list3 (evalExp_pair ft f₁) (evalExp_pair ft f₂)
      (evalExp_pair ft fo))
      (evalExp_list1 (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var fc)))))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_var fc, evalExp_callE_iff.2
      ((applies_iff_callDef rfl (evalArgs_four ft fo f₁ f₂)).1 happ), cmpValues_eq_self _⟩)))

/-- The `cvtop` of a typed `CVTOP` instruction is a typed `cvtop`. -/
theorem typedV_cvtop10T {op : V1.ConvertOp}
    (h : TypedV (simEnv10T B) adminT10 (adminToV (.source (.convert op)))) :
    TypedV (simEnv10T B) (.varT "cvtop" []) (cvtOpV op) := by
  obtain ⟨cs, htd, -, -, -, -, -, ps, hc⟩ := findTyp_admininstr10_numT (B := B)
  have hp := hasTyp_closedVariant_inv valsOnly_empty htd (h _ valsOnly_empty) hc
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 hp
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨y, ys, hys, -, htup₁⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨rfl, rfl⟩ := List.cons.inj hys
  obtain ⟨y', ys', hys', -, htup₂⟩ := hasTypTup_cons_iff.1 htup₁
  obtain ⟨rfl, rfl⟩ := List.cons.inj hys'
  obtain ⟨y'', ys'', hys'', hy'', -⟩ := hasTypTup_cons_iff.1 htup₂
  obtain ⟨rfl, -⟩ := List.cons.inj hys''
  exact typedV_of_scope ⟨rfl, rfl, rfl⟩ hy''

/-- **`cvtop-val` (26) forward.** -/
theorem fwdAt10T_cvtopVal (s : Store H) (f : Frame) (op : V1.ConvertOp)
    (x : BitVec op.toCore.source.width) (y : BitVec op.toCore.target.width) (vs : List Value)
    (happ : Applies (simEnv10 B) "cvtop__" (cvtArgsV1 op x) (.list vs))
    (hm : numV ⟨op.toCore.target, y⟩ ∈ vs) :
    FwdAt10T B hn ⟨s, f, [value ⟨op.toCore.source, x⟩, .source (.convert op)]⟩
      ⟨s, f, [value ⟨op.toCore.target, y⟩]⟩ := by
  refine fwdAt10T_of_spure2 fun hc hc' => spure10T_of_fires (k := 26) ?_
  let σ : List (IL.Id × Value) := [("t_1", valTypeV op.toCore.source),
    ("c_1", numV ⟨op.toCore.source, x⟩), ("t_2", valTypeV op.toCore.target), ("cvtop", cvtOpV op),
    ("c", numV ⟨op.toCore.target, y⟩)]
  have ft₁ : (VarEnv.empty.bindVals σ).findVal? "t_1" = some (valTypeV op.toCore.source) := rfl
  have f₁ : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (numV ⟨op.toCore.source, x⟩) := rfl
  have ft₂ : (VarEnv.empty.bindVals σ).findVal? "t_2" = some (valTypeV op.toCore.target) := rfl
  have fo : (VarEnv.empty.bindVals σ).findVal? "cvtop" = some (cvtOpV op) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (numV ⟨op.toCore.target, y⟩) := rfl
  have hout : adminsToV [value ⟨op.toCore.target, y⟩] =
      [.case "CONST" (.tuple [valTypeV op.toCore.target, numV ⟨op.toCore.target, y⟩])] := by
    rw [adminsToV_v]
    rfl
  rw [adminsToV_cvt10, hout]
  exact fires_of_ruleAtT (hasRuleAt10_cvtopVal B) σ
    (QuantsOk.cons ft₁ (typedV_valtype10T _ _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons f₁ (val_of_admin10T (typedV_head10T hc) ft₁)
        (QuantsOk.cons ft₂ (typedV_valtype10T _ _ ⟨rfl, rfl, rfl⟩)
          (QuantsOk.cons fo (typedV_cvtop10T (typedV_second10T hc) _ ⟨rfl, rfl, rfl⟩)
            (QuantsOk.cons fc (val_of_admin10T (typedV_head10T hc') ft₂) QuantsOk.nil)))))
    (evalExp_tup2 (evalExp_list2 (evalExp_pair ft₁ f₁) (evalExp_case (Sim.evalExp_tup3
      (evalExp_var ft₂) (evalExp_var ft₁) (evalExp_var fo)))) (evalExp_list1 (evalExp_pair ft₂ fc)))
    (prems_one (.ifPr (evalExp_memE_iff.2 ⟨_, _, evalExp_var fc, evalExp_callE_iff.2
      ((applies_iff_callDef rfl (evalArgs_four ft₁ ft₂ fo f₁)).1 happ), memValue_list_iff.2 hm⟩)))

/-- **`cvtop-trap` (27) forward.** -/
theorem fwdAt10T_cvtopTrap (s : Store H) (f : Frame) (op : V1.ConvertOp)
    (x : BitVec op.toCore.source.width)
    (happ : Applies (simEnv10 B) "cvtop__" (cvtArgsV1 op x) (.list [])) :
    FwdAt10T B hn ⟨s, f, [value ⟨op.toCore.source, x⟩, .source (.convert op)]⟩ ⟨s, f, [.trap]⟩ := by
  refine fwdAt10T_of_spure2 fun hc _ => spure10T_of_fires (k := 27) ?_
  let σ : List (IL.Id × Value) := [("t_1", valTypeV op.toCore.source),
    ("c_1", numV ⟨op.toCore.source, x⟩), ("t_2", valTypeV op.toCore.target), ("cvtop", cvtOpV op)]
  have ft₁ : (VarEnv.empty.bindVals σ).findVal? "t_1" = some (valTypeV op.toCore.source) := rfl
  have f₁ : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (numV ⟨op.toCore.source, x⟩) := rfl
  have ft₂ : (VarEnv.empty.bindVals σ).findVal? "t_2" = some (valTypeV op.toCore.target) := rfl
  have fo : (VarEnv.empty.bindVals σ).findVal? "cvtop" = some (cvtOpV op) := rfl
  rw [adminsToV_cvt10]
  exact fires_of_ruleAtT (hasRuleAt10_cvtopTrap B) σ
    (QuantsOk.cons ft₁ (typedV_valtype10T _ _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons f₁ (val_of_admin10T (typedV_head10T hc) ft₁)
        (QuantsOk.cons ft₂ (typedV_valtype10T _ _ ⟨rfl, rfl, rfl⟩)
          (QuantsOk.cons fo (typedV_cvtop10T (typedV_second10T hc) _ ⟨rfl, rfl, rfl⟩)
            QuantsOk.nil))))
    (evalExp_tup2 (evalExp_list2 (evalExp_pair ft₁ f₁) (evalExp_case (Sim.evalExp_tup3
      (evalExp_var ft₂) (evalExp_var ft₁) (evalExp_var fo)))) (evalExp_list1 evalExp_caseNil))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_callE_iff.2
      ((applies_iff_callDef rfl (evalArgs_four ft₁ ft₂ fo f₁)).1 happ), evalExp_list0,
      cmpValues_eq_self _⟩)))

/-- V1's `intBinaryTrap` forward. -/
theorem fwdAt10T_intBinaryTrap {nd : Bool} {r : RelaxedChoice}
    (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) (s : Store H) (f : Frame) (t : IntType)
    (op : IntBinOp) (x y : BitVec t.width) (err : IntTrap) (h : intBinOp t op x y = .error err) :
    FwdAt10T B hn ⟨s, f, [value (.int t x), value (.int t y), .source (.intBinOp t op)]⟩
      ⟨s, f, [.trap]⟩ := by
  obtain ⟨vs, happ, hmem⟩ := A.intBinOp t op x y
  have hvs : vs = [] := nil_of_no_mem fun c hc => by
    obtain ⟨z, hz, -⟩ := (hmem c).1 hc
    rw [h] at hz
    cases hz
  exact fwdAt10T_binopTrap s f (.int t x) (.int t y) (.intBinOp t op) (intBinOpV op) rfl rfl
    (hvs ▸ happ)

/-- V1's `convertTrap` forward. -/
theorem fwdAt10T_convertTrap {nd : Bool} {r : RelaxedChoice}
    (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) (s : Store H) (f : Frame)
    (op : V1.ConvertOp) (x : BitVec op.toCore.source.width) (err : FloatTrap)
    (h : convertRel op.toCore x (.error err)) :
    FwdAt10T B hn ⟨s, f, [value ⟨op.toCore.source, x⟩, .source (.convert op)]⟩ ⟨s, f, [.trap]⟩ := by
  obtain ⟨vs, happ, -, hnil⟩ := A.cvtOp op x
  have hvs : vs = [] := hnil.2 ⟨err, h⟩
  exact fwdAt10T_cvtopTrap s f op x (hvs ▸ happ)

/-- **The numeric rules forward**: under `NumAgree10` at the spec profile, every numeric V1 step
satisfies `FwdAt10`. -/
theorem fwdAt10T_num {nd : Bool} {r : RelaxedChoice}
    (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) (s : Store H) (f : Frame)
    {before after : List Admin} (hn' : NumStep10 before after) :
    FwdAt10T B hn ⟨s, f, before⟩ ⟨s, f, after⟩ := by
  cases hn' with
  | intUnary t op x =>
    exact fwdAt10T_unopVal s f (.int t x) _ (.intUnOp t op) (intUnOpV op) _ rfl rfl
      (A.intUnOp t op x) (List.mem_singleton_self _)
  | intBinary t op x y z h =>
    obtain ⟨vs, happ, hmem⟩ := A.intBinOp t op x y
    exact fwdAt10T_binopVal s f (.int t x) (.int t y) (.int t z) (.intBinOp t op) (intBinOpV op) vs
      rfl rfl rfl happ ((hmem _).2 ⟨z, h, rfl⟩)
  | intBinaryTrap t op x y err h => exact fwdAt10T_intBinaryTrap A s f t op x y err h
  | intTest t op x =>
    exact fwdAt10T_testop s f (.int t x) (.intTestOp t op) (intTestOpV op) _ rfl
      (A.intTestOp t op x)
  | intRel t op x y =>
    exact fwdAt10T_relop s f (.int t x) (.int t y) (.intRelOp t op) (intRelOpV op) _ rfl rfl
      (A.intRelOp t op x y)
  | floatUnary t op x y h =>
    obtain ⟨vs, happ, hmem⟩ := A.floatUnOp t op x
    exact fwdAt10T_unopVal s f (.float t x) (.float t y) (.floatUnOp t op) (floatUnOpV op) vs rfl
      rfl happ ((hmem _).2 ⟨y, h, rfl⟩)
  | floatBinary t op x y z h =>
    obtain ⟨vs, happ, hmem⟩ := A.floatBinOp t op x y
    exact fwdAt10T_binopVal s f (.float t x) (.float t y) (.float t z) (.floatBinOp t op)
      (floatBinOpV op) vs rfl rfl rfl happ ((hmem _).2 ⟨z, h, rfl⟩)
  | floatRel t op x y =>
    exact fwdAt10T_relop s f (.float t x) (.float t y) (.floatRelOp t op) (floatRelOpV op) _ rfl rfl
      (A.floatRelOp t op x y)
  | convert op x y h =>
    obtain ⟨vs, happ, hmem, -⟩ := A.cvtOp op x
    exact fwdAt10T_cvtopVal s f op x y vs happ ((hmem _).2 ⟨y, h, rfl⟩)
  | convertTrap op x err h => exact fwdAt10T_convertTrap A s f op x err h

/-- **The numeric obligation of `FwdRestP10` at the spec's builtins.** -/
theorem fwdAt10T_num_floatIntB {nd : Bool} {r : RelaxedChoice} (s : Store H) (f : Frame)
    {before after : List Admin} (h : NumStep10 before after) :
    FwdAt10T (Sim.Floats.floatIntB (Profile.spec nd r)) hn ⟨s, f, before⟩ ⟨s, f, after⟩ :=
  fwdAt10T_num numAgree10_floatIntB s f h


end Silmaril.Wasm.SpecTec.Sim10.Whole
