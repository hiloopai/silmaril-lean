module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Decode
public import Silmaril.Wasm.SpecTec.Sim20.State.Defs

/-!
# The control rules of 1.0 `Step_pure`, backwards, transferred from 2.0 where the census allows

**Transfer.** The census `Sim20.Census.census_pure_10_20` finds 13 of 1.0's 29 `Step_pure` rules
byte-identical to 2.0 rules. For those, the 2.0 rule constants of `Sim20.Pure` and
`Sim20.State` *are* the 1.0 rules: their provenance in `simEnv10 B` is a kernel `rfl` at the 1.0
index (`hasRuleAt10_unreachable` … `hasRuleAt10_localTee`, `hasRuleAt10_trapLabel`, …). The
inversions below are stated for an arbitrary environment wherever only the rule term matters, so
the same lemma reads a rule back in either script. The rules the census marks `changed` differ
from 2.0's only in their quantifier types (`val_(I32)` for `num_(I32)`, `t?` for a `blocktype`)
and `SELECT`'s annotation; they are transcribed here (`selectTrueRule10`, `ifTrueRule10`, …).

**Backwards.** For each rule, a firing at the image of any V1 code sequence is the image of a V1
`PureStep`: `unreachable` 0, `nop` 1, `drop` 2, `select-*` 3–4 (given `SelOk`, as V1 checks the
operand types), `if-*` 5–6, `label-vals` 7, `br_if-*` 10–11, `trap-label` 18, `trap-frame` 19,
`local.tee` 28. The code is read back with `Sim10.Decode`; the right-hand side is evaluated
forwards from the pieces of the left-hand side (same scope) and compared by `EvalExp.unique`.
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
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV iterPat)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk evalExp_case evalExp_tup2 evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim20.Pure (evalExp_caseNil evalExp_list0 evalExp_list2 evalExp_sub
  immCmp_of_eval ne_zero_of_cmp eq_zero_of_cmp ifPrem)

variable (B : Builtins)

set_option maxRecDepth 100000

/-! ## Provenance: the rules shared with 2.0, and the changed ones transcribed -/

theorem hasRuleAt10_unreachable :
    HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 0 Sim20.Pure.unreachableRule := ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_nop : HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 1 Sim20.Pure.nopRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_drop : HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 2 Sim20.Pure.dropRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_labelVals :
    HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 7 Sim20.Pure.labelValsRule := ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_brZero : HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 8 Sim20.Pure.brZeroRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_brSucc : HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 9 Sim20.Pure.brSuccRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_frameVals :
    HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 14 Sim20.Pure.frameValsRule := ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_returnFrame :
    HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 15 Sim20.Pure.returnFrameRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_returnLabel :
    HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 16 Sim20.Pure.returnLabelRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_trapVals :
    HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 17 Sim20.Pure.trapValsRule := ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_trapLabel :
    HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 18 Sim20.Pure.trapLabelRule := ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_trapFrame :
    HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 19 Sim20.Pure.trapFrameRule := ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_localTee :
    HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 28 Sim20.State.localTeeRule := ⟨_, _, _, rfl, rfl, rfl⟩

/-- `val_(I32)`, the type 1.0 gives an `i32` immediate. -/
abbrev valI32T : Typ := .varT "val_" [.expA (.caseE "I32" (.tupE []))]

/-- `CONST I32 c`. -/
abbrev constI32E (c : IL.Id) : Exp := .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE c])

/-- `c!%.0 op 0`. -/
abbrev immCmpE (op : CmpOp) (c : IL.Id) : Exp :=
  .cmpE op .boolT (.projE (.uncaseE (.varE c) "%") 0) (.numE (.natN 0))

/-- `(x : val <: admininstr)`. -/
abbrev valSubE (x : IL.Id) : Exp := .subE (.varE x) (.varT "val" []) (.varT "admininstr" [])

/-- `Step_pure/select-true` or `-false` of 1.0 (`SELECT` has no annotation). -/
def selectRule10 (nm : IL.Id) (res : IL.Id) (op : CmpOp) : Rule :=
  .ruleD nm [.expP "val_1" (.varT "val" []), .expP "val_2" (.varT "val" []), .expP "c" valI32T]
    "%~>%" (.tupE [.listE [valSubE "val_1", valSubE "val_2", constI32E "c",
      .caseE "SELECT" (.tupE [])], .listE [valSubE res]]) [.ifPr (immCmpE op "c")]

/-- `t?`. -/
abbrev optT : Exp := .iterE (.varE "t") (.mk .opt [.mk "t" (.varE "t?")])

/-- `Step_pure/if-true` or `-false` of 1.0 (`t?` for a block type). -/
def ifRule10 (nm : IL.Id) (branch : IL.Id) (op : CmpOp) : Rule :=
  .ruleD nm [.expP "c" valI32T, .expP "t?" (.iterT (.varT "valtype" []) .opt),
      .expP "instr_1*" (.iterT (.varT "instr" []) .list),
      .expP "instr_2*" (.iterT (.varT "instr" []) .list)] "%~>%"
    (.tupE [.listE [constI32E "c", .caseE "IF%%ELSE%" (.tupE [optT, iterPat "instr_1" "instr_1*",
        iterPat "instr_2" "instr_2*"])],
      .listE [.caseE "BLOCK" (.tupE [optT, iterPat branch (branch ++ "*")])]])
    [.ifPr (immCmpE op "c")]

/-- `Step_pure/br_if-true` of 1.0. -/
def brIfTrueRule10 : Rule :=
  .ruleD "br_if-true" [.expP "c" valI32T, .expP "l" (.varT "labelidx" [])] "%~>%"
    (.tupE [.listE [constI32E "c", .caseE "BR_IF" (.varE "l")], .listE [.caseE "BR" (.varE "l")]])
    [.ifPr (immCmpE .neOp "c")]

/-- `Step_pure/br_if-false` of 1.0. -/
def brIfFalseRule10 : Rule :=
  .ruleD "br_if-false" [.expP "c" valI32T, .expP "l" (.varT "labelidx" [])] "%~>%"
    (.tupE [.listE [constI32E "c", .caseE "BR_IF" (.varE "l")], .listE []])
    [.ifPr (immCmpE .eqOp "c")]

theorem hasRuleAt10_selectTrue :
    HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 3 (selectRule10 "select-true" "val_1" .neOp) :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_selectFalse :
    HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 4 (selectRule10 "select-false" "val_2" .eqOp) :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_ifTrue :
    HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 5 (ifRule10 "if-true" "instr_1" .neOp) :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_ifFalse :
    HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 6 (ifRule10 "if-false" "instr_2" .eqOp) :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_brIfTrue : HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 10 brIfTrueRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_brIfFalse : HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 11 brIfFalseRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## Backwards -/

variable {B}

/-- The conclusion of a `Step_pure` obligation. -/
def PureBwd10 (code : List Admin) (w : List Value) : Prop :=
  ∃ code', w = adminsToV code' ∧ PureStep code code'

theorem pureBwd10_of {code code' : List Admin} {w : List Value}
    (hw : Value.list w = .list (adminsToV code')) (hs : PureStep code code') : PureBwd10 code w :=
  ⟨code', Value.list.inj hw, hs⟩

/-- `Step_pure/unreachable` at any code. -/
theorem bwd10_unreachable {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 0 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, -, hes, hrh, -⟩ := firesPure10_inv (hasRuleAt10_unreachable B) hf
  obtain ⟨a, rfl, ha⟩ := codes10_one hes
  obtain rfl := head10_unreachable (head10_of_caseE ha)
  exact pureBwd10_of (EvalExp.unique hrh (evalExp_list1 evalExp_caseNil)) .unreachable

/-- `Step_pure/nop` at any code. -/
theorem bwd10_nop {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 1 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, -, hes, hrh, -⟩ := firesPure10_inv (hasRuleAt10_nop B) hf
  obtain ⟨a, rfl, ha⟩ := codes10_one hes
  obtain rfl := head10_nop (head10_of_caseE ha)
  exact pureBwd10_of (EvalExp.unique hrh evalExp_list0) .nop

/-- `Step_pure/drop` at any code. -/
theorem bwd10_drop {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 2 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, hq, hes, hrh, -⟩ := firesPure10_inv (hasRuleAt10_drop B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨v, rfl, -⟩ := val10_of_var hq (by simp) h₁
  obtain rfl := head10_drop (head10_of_caseE h₂)
  exact pureBwd10_of (EvalExp.unique hrh evalExp_list0) (.drop v)

/-- `Step_pure/local.tee` at any code. -/
theorem bwd10_localTee {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 28 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, hq, hes, hrh, -⟩ := firesPure10_inv (hasRuleAt10_localTee B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨v, rfl, fv⟩ := val10_of_var hq (by simp) h₁
  obtain ⟨x, rfl⟩ := head10_localTee (head10_of_caseE h₂)
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 h₂
  have ex : u = idxV x := (Value.case.inj hcu.symm).2
  subst ex
  have hr : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) (.listE [valSubE "val", valSubE "val",
      .caseE "LOCAL.SET" (.varE "x")]) (.list (adminsToV [value v, value v, .source (.localSet x)])) := by
    rw [adminsToV_map10]
    simp only [List.map_cons, List.map_nil, adminToV_value]
    exact evalExp_listE_iff.2 ⟨_, evalExps_cons (evalExp_sub (evalExp_var fv))
      (evalExps_cons (evalExp_sub (evalExp_var fv)) (evalExps_cons (evalExp_case hu) evalExps_nil)),
      rfl⟩
  exact pureBwd10_of (EvalExp.unique hrh hr) (.localTee x v)

/-- `Step_pure/trap-label` at any code. -/
theorem bwd10_trapLabel {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 18 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, -, hes, hrh, -⟩ := firesPure10_inv (hasRuleAt10_trapLabel B) hf
  obtain ⟨a, rfl, ha⟩ := codes10_one hes
  obtain ⟨n, cont, body, rfl⟩ := head10_label (head10_of_caseE ha)
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 ha
  obtain ⟨us, hus, rfl⟩ := evalExp_tupE_iff.1 hu
  obtain ⟨u₁, us₁, -, hus₁, rfl⟩ := evalExps_cons_iff.1 hus
  obtain ⟨u₂, us₂, -, hus₂, rfl⟩ := evalExps_cons_iff.1 hus₁
  obtain ⟨u₃, us₃, h₃, hus₃, rfl⟩ := evalExps_cons_iff.1 hus₂
  obtain rfl := evalExps_nil_iff.1 hus₃
  have hb : Value.list (adminsToV body) = u₃ := by
    simp only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and] at hcu
    exact hcu.2.2.1
  have hb' : Value.list (adminsToV body) = .list [caseNilV "TRAP"] :=
    hb.trans (EvalExp.unique h₃ (evalExp_list1 evalExp_caseNil))
  obtain ⟨t, rfl, ht⟩ := adminsToV_eq_single10 (Value.list.inj hb')
  obtain rfl := head10_trap (adminToV_case10 ht)
  exact pureBwd10_of (EvalExp.unique hrh (evalExp_list1 evalExp_caseNil)) (.labelTrap n cont)

/-- `Step_pure/trap-frame` at any code. -/
theorem bwd10_trapFrame {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 19 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, -, hes, hrh, -⟩ := firesPure10_inv (hasRuleAt10_trapFrame B) hf
  obtain ⟨a, rfl, ha⟩ := codes10_one hes
  obtain ⟨n, fi, body, rfl⟩ := head10_frame (head10_of_caseE ha)
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 ha
  obtain ⟨us, hus, rfl⟩ := evalExp_tupE_iff.1 hu
  obtain ⟨u₁, us₁, -, hus₁, rfl⟩ := evalExps_cons_iff.1 hus
  obtain ⟨u₂, us₂, -, hus₂, rfl⟩ := evalExps_cons_iff.1 hus₁
  obtain ⟨u₃, us₃, h₃, hus₃, rfl⟩ := evalExps_cons_iff.1 hus₂
  obtain rfl := evalExps_nil_iff.1 hus₃
  have hb : Value.list (adminsToV body) = u₃ := by
    simp only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and] at hcu
    exact hcu.2.2.1
  have hb' : Value.list (adminsToV body) = .list [caseNilV "TRAP"] :=
    hb.trans (EvalExp.unique h₃ (evalExp_list1 evalExp_caseNil))
  obtain ⟨t, rfl, ht⟩ := adminsToV_eq_single10 (Value.list.inj hb')
  obtain rfl := head10_trap (adminToV_case10 ht)
  exact pureBwd10_of (EvalExp.unique hrh (evalExp_list1 evalExp_caseNil)) (.frameTrap n fi)

/-- The `if` immediate `CONST I32 c`, its comparison with `0`, read back. -/
theorem immCmp10 {ρ : VarEnv} {a : Admin} {op : CmpOp}
    (ha : EvalExp (simEnv10 B) ρ (constI32E "c") (adminToV a))
    (hp : EvalExp (simEnv10 B) ρ (immCmpE op "c") (.bool true)) :
    ∃ c : BitVec 32, a = value ⟨.int .i32, c⟩ ∧
      cmpValues op (.num (.natN c.toNat)) (.num (.natN 0)) = .ok (.bool true) := by
  obtain ⟨c, rfl, hc⟩ := constI32_of_lhs10 ha
  exact ⟨c, rfl, immCmp_of_eval (evalExp_varE_iff.1 hc) hp⟩

/-- `Step_pure/br_if-true` at any code. -/
theorem bwd10_brIfTrue {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 10 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, -, hes, hrh, hp⟩ := firesPure10_inv (hasRuleAt10_brIfTrue B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨c, rfl, hc⟩ := immCmp10 h₁ (ifPrem (hp _ (.head _)))
  obtain ⟨l, rfl⟩ := head10_brIf (head10_of_caseE h₂)
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 h₂
  obtain rfl : u = idxV l := (Value.case.inj hcu.symm).2
  exact pureBwd10_of (EvalExp.unique hrh (evalExp_list1 (evalExp_case hu)))
    (.brIfNonzero l c (ne_zero_of_cmp hc))

/-- `Step_pure/br_if-false` at any code. -/
theorem bwd10_brIfFalse {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 11 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, -, hes, hrh, hp⟩ := firesPure10_inv (hasRuleAt10_brIfFalse B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨c, rfl, hc⟩ := immCmp10 h₁ (ifPrem (hp _ (.head _)))
  obtain ⟨l, rfl⟩ := head10_brIf (head10_of_caseE h₂)
  obtain rfl := eq_zero_of_cmp hc
  exact pureBwd10_of (EvalExp.unique hrh evalExp_list0) (.brIfZero l)

/-- The pieces of an `IF%%ELSE%` left-hand side, read back. -/
theorem if_parts10 {ρ : VarEnv} {a : Admin}
    (h : EvalExp (simEnv10 B) ρ (.caseE "IF%%ELSE%" (.tupE [optT, iterPat "instr_1" "instr_1*",
      iterPat "instr_2" "instr_2*"])) (adminToV a)) :
    ∃ bt b₁ b₂, a = .source (.if_ bt b₁ b₂) ∧ EvalExp (simEnv10 B) ρ optT (blockTypeV bt) ∧
      EvalExp (simEnv10 B) ρ (iterPat "instr_1" "instr_1*") (.list (instrsToV b₁)) ∧
      EvalExp (simEnv10 B) ρ (iterPat "instr_2" "instr_2*") (.list (instrsToV b₂)) := by
  obtain ⟨bt, b₁, b₂, rfl⟩ := head10_if (head10_of_caseE h)
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 h
  obtain ⟨us, hus, rfl⟩ := evalExp_tupE_iff.1 hu
  obtain ⟨u₁, us₁, h₁, hus₁, rfl⟩ := evalExps_cons_iff.1 hus
  obtain ⟨u₂, us₂, h₂, hus₂, rfl⟩ := evalExps_cons_iff.1 hus₁
  obtain ⟨u₃, us₃, h₃, hus₃, rfl⟩ := evalExps_cons_iff.1 hus₂
  obtain rfl := evalExps_nil_iff.1 hus₃
  simp only [adminToV, instrToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
    true_and, and_true] at hcu
  obtain ⟨rfl, rfl, rfl⟩ := hcu
  exact ⟨bt, b₁, b₂, rfl, h₁, h₂, h₃⟩

/-- `Step_pure/if-true` at any code. -/
theorem bwd10_ifTrue {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 5 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, -, hes, hrh, hp⟩ := firesPure10_inv (hasRuleAt10_ifTrue B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨c, rfl, hc⟩ := immCmp10 h₁ (ifPrem (hp _ (.head _)))
  obtain ⟨bt, b₁, b₂, rfl, ht, hb₁, -⟩ := if_parts10 h₂
  exact pureBwd10_of (EvalExp.unique hrh (evalExp_list1 (evalExp_case (evalExp_tup2 ht hb₁))))
    (.ifNonzero bt b₁ b₂ c (ne_zero_of_cmp hc))

/-- `Step_pure/if-false` at any code. -/
theorem bwd10_ifFalse {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 6 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, -, hes, hrh, hp⟩ := firesPure10_inv (hasRuleAt10_ifFalse B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨c, rfl, hc⟩ := immCmp10 h₁ (ifPrem (hp _ (.head _)))
  obtain ⟨bt, b₁, b₂, rfl, ht, -, hb₂⟩ := if_parts10 h₂
  obtain rfl := eq_zero_of_cmp hc
  exact pureBwd10_of (EvalExp.unique hrh (evalExp_list1 (evalExp_case (evalExp_tup2 ht hb₂))))
    (.ifZero bt b₁ b₂)

/-- The left-hand side `val_1 val_2 (CONST I32 c) SELECT`, read back. -/
theorem select_lhs10 {σ : List (IL.Id × Value)} {op : CmpOp} {code : List Admin}
    (hq : QuantsOk (simEnv10 B) (VarEnv.empty.bindVals σ)
      [.expP "val_1" (.varT "val" []), .expP "val_2" (.varT "val" []), .expP "c" valI32T])
    (hes : EvalExps (simEnv10 B) (VarEnv.empty.bindVals σ) [valSubE "val_1", valSubE "val_2",
      constI32E "c", .caseE "SELECT" (.tupE [])] (adminsToV code))
    (hp : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) (immCmpE op "c") (.bool true)) :
    ∃ (v₁ v₂ : Execution.Runtime.Value) (c : BitVec 32), code = [value v₁, value v₂, value ⟨.int .i32, c⟩, .source .select] ∧
      (VarEnv.empty.bindVals σ).findVal? "val_1" = some (valV v₁) ∧
      (VarEnv.empty.bindVals σ).findVal? "val_2" = some (valV v₂) ∧
      cmpValues op (.num (.natN c.toNat)) (.num (.natN 0)) = .ok (.bool true) := by
  obtain ⟨a₁, a₂, a₃, a₄, rfl, h₁, h₂, h₃, h₄⟩ := codes10_four hes
  obtain ⟨v₁, rfl, f₁⟩ := val10_of_var hq (by simp) h₁
  obtain ⟨v₂, rfl, f₂⟩ := val10_of_var hq (by simp) h₂
  obtain ⟨c, rfl, hc⟩ := immCmp10 h₃ hp
  obtain rfl := head10_select (head10_of_caseE h₄)
  exact ⟨v₁, v₂, c, rfl, f₁, f₂, hc⟩

/-- An exact select redex is active in itself. -/
theorem active_self (l : List Admin) : Active l l := by
  have h : Active ([] ++ l ++ []) l := .piece
  simpa using h

/-- `Step_pure/select-true` at code whose `select` operands have one type. -/
theorem bwd10_selectTrue {code : List Admin} {w : List Value} (hs : SelOk code)
    (hf : Fires (simEnv10 B) "Step_pure" 3 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, hq, hes, hrh, hp⟩ := firesPure10_inv (hasRuleAt10_selectTrue B) hf
  obtain ⟨v₁, v₂, c, rfl, f₁, -, hc⟩ := select_lhs10 hq hes (ifPrem (hp _ (.head _)))
  have hty : v₁.type = v₂.type := hs v₁ v₂ c (active_self _)
  have hr : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) (.listE [valSubE "val_1"]) (.list (adminsToV [value v₁])) := by
    rw [adminsToV_map10]
    simp only [List.map_cons, List.map_nil, adminToV_value]
    exact evalExp_list1 (evalExp_sub (evalExp_var f₁))
  exact pureBwd10_of (EvalExp.unique hrh hr) (.selectNonzero v₁ v₂ hty c (ne_zero_of_cmp hc))

/-- `Step_pure/select-false` at code whose `select` operands have one type. -/
theorem bwd10_selectFalse {code : List Admin} {w : List Value} (hs : SelOk code)
    (hf : Fires (simEnv10 B) "Step_pure" 4 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, hq, hes, hrh, hp⟩ := firesPure10_inv (hasRuleAt10_selectFalse B) hf
  obtain ⟨v₁, v₂, c, rfl, -, f₂, hc⟩ := select_lhs10 hq hes (ifPrem (hp _ (.head _)))
  have hty : v₁.type = v₂.type := hs v₁ v₂ c (active_self _)
  obtain rfl := eq_zero_of_cmp hc
  have hr : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) (.listE [valSubE "val_2"]) (.list (adminsToV [value v₂])) := by
    rw [adminsToV_map10]
    simp only [List.map_cons, List.map_nil, adminToV_value]
    exact evalExp_list1 (evalExp_sub (evalExp_var f₂))
  exact pureBwd10_of (EvalExp.unique hrh hr) (.selectZero v₁ v₂ hty)

end Silmaril.Wasm.SpecTec.Sim10.Whole
