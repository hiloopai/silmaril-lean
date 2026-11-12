module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Assemble3
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureControl

/-!
# `br_table` of 1.0, backwards: 2.0's rules with 1.0's quantifiers

The census marks 1.0's `br_table-lt` and `br_table-ge` `changed` from 2.0. The change is in the
quantifier types only: 1.0's `i : val_(I32)` for 2.0's `i : num_(I32)`. So the 1.0 rules are the
2.0 rule constants with 1.0's quantifiers (`withQs`, checked by kernel `rfl`:
`hasRuleAt10_brTableLt`, `hasRuleAt10_brTableGe`), and 2.0's environment-generic lemmas about
their bodies (`Sim20.Pure.ge_of_cmp`) apply to `simEnv10 B`.

Backwards, both rules are V1's single `PureStep.brTable`, whose target
`ls[c]?.getD default` is the `-lt` or the `-ge` branch.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin PureStep value)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV evalExp_imm_iff iterPat evalExp_iterPat)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk quant_list evalExp_case evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim20.Pure (quant_val ifPrem ge_of_cmp)

set_option maxRecDepth 100000

/-- A rule with its quantifiers replaced. -/
def withQs (qs : List Param) : Rule → Rule
  | .ruleD nm _ op e prems => .ruleD nm qs op e prems

/-- The quantifiers of 1.0's `br_table` rules. -/
abbrev brTableQs10 : List Param :=
  [.expP "i" valI32T, .expP "l*" (.iterT (.varT "labelidx" []) .list),
    .expP "l'" (.varT "labelidx" [])]

variable (B : Builtins)

theorem hasRuleAt10_brTableLt :
    HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 12 (withQs brTableQs10 Sim20.Pure.brTableLtRule) :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_brTableGe :
    HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 13 (withQs brTableQs10 Sim20.Pure.brTableGeRule) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

variable {B}

/-- The left-hand side `CONST I32 i; BR_TABLE l* l'`, read back. -/
theorem brTable_lhs10 {σ : List (IL.Id × Value)} {code : List Admin}
    (hq : QuantsOk (simEnv10 B) (VarEnv.empty.bindVals σ) brTableQs10)
    (hes : EvalExps (simEnv10 B) (VarEnv.empty.bindVals σ) [constI32E "i",
      .caseE "BR_TABLE" (.tupE [iterPat "l" "l*", .varE "l'"])] (adminsToV code)) :
    ∃ (c : BitVec 32) (ls : List LabelIdx) (l' : LabelIdx), code = [value ⟨.int .i32, c⟩, .source (.brTable ls l')] ∧
      (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV c.toNat) ∧
      (VarEnv.empty.bindVals σ).findVal? "l*" = some (.list (ls.map idxV)) ∧
      EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) (.varE "l'") (idxV l') := by
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨c, rfl, hc⟩ := constI32_of_lhs10 h₁
  obtain ⟨ls, l', rfl⟩ := head10_brTable (head10_of_caseE h₂)
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 h₂
  obtain rfl : u = .tuple [.list (ls.map idxV), idxV l'] := (Value.case.inj hcu.symm).2
  obtain ⟨u₁, u₂, hl, hl', he⟩ := Sim.State.evalExp_tup2_inv hu
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨xs, fxs, -⟩ := quant_list (x := "l*") (t := .varT "labelidx" []) hq (by simp)
  have ex : Value.list xs = .list (ls.map idxV) :=
    EvalExp.unique (evalExp_iterPat (by decide) fxs) hl
  exact ⟨c, ls, l', rfl, evalExp_varE_iff.1 hc, ex ▸ fxs, hl'⟩

/-- **`Step_pure/br_table-lt` backwards**: V1's `brTable`, in range. -/
theorem bwd10_brTableLt {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 12 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, hq, hes, hrh, -⟩ := firesPure10_inv (hasRuleAt10_brTableLt B) hf
  obtain ⟨c, ls, l', rfl, fi, fls, -⟩ := brTable_lhs10 hq hes
  obtain ⟨ws, hws, hw⟩ := evalExp_listE_iff.1 hrh
  obtain ⟨u, us, hu, hus, hl⟩ := evalExps_cons_iff.1 hws
  have hnil : us = [] := evalExps_nil_iff.1 hus
  obtain ⟨u', hu', rfl⟩ := evalExp_caseE_iff.1 hu
  obtain ⟨xs, k, hxs, hk, hidx⟩ := evalExp_idxE_iff.1 hu'
  have ek : Value.num (.natN k) = .num (.natN c.toNat) :=
    EvalExp.unique hk ((evalExp_imm_iff fi).2 ⟨[], rfl⟩)
  have exs : xs = .list (ls.map idxV) := EvalExp.unique hxs (evalExp_iterPat (by decide) fls)
  obtain ⟨l, hl', rfl⟩ : ∃ l, ls[c.toNat]? = some l ∧ idxV l = u' := by
    rw [Sim.Bwd.natN_inj ek, exs] at hidx
    simpa [Value.idx?, List.getElem?_map] using hidx
  have hw' : Value.list w = .list (adminsToV [.source (.br (ls[c.toNat]?.getD l'))]) := by
    rw [hw, hl, hnil, hl']
    rfl
  exact pureBwd10_of hw' (.brTable ls l' c)

/-- **`Step_pure/br_table-ge` backwards**: V1's `brTable`, out of range. -/
theorem bwd10_brTableGe {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 13 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, hq, hes, hrh, hp⟩ := firesPure10_inv (hasRuleAt10_brTableGe B) hf
  obtain ⟨c, ls, l', rfl, fi, fls, hl'⟩ := brTable_lhs10 hq hes
  have hge : (ls.map idxV).length ≤ c.toNat := ge_of_cmp fi fls (ifPrem (hp _ (.head _)))
  have hnone : ls[c.toNat]? = none := List.getElem?_eq_none (by simpa using hge)
  have hw' : Value.list w = .list (adminsToV [.source (.br (ls[c.toNat]?.getD l'))]) := by
    rw [hnone]
    exact EvalExp.unique hrh (evalExp_list1 (evalExp_case hl'))
  exact pureBwd10_of hw' (.brTable ls l' c)

end Silmaril.Wasm.SpecTec.Sim10.Whole
