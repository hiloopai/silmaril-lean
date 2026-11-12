module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.State.Common

/-!
# Family M: tables and element segments, Core → SpecTec

`Step_read/table.get-oob` (25), `table.get-val` (26), `Step/table.set-oob` (13), `table.set-val`
(14) and `elem.drop` (17), constructed for arbitrary state values (`sread_tableGetOob`, …) and
instantiated at the Core encoding (`fwd_tableGetOob`, …).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.State

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.RuntimeBridge

/-! ## Comparisons on naturals -/

theorem cmpValues_geOp_nat {p q : Nat} (h : q ≤ p) :
    cmpValues .geOp (.num (.natN p)) (.num (.natN q)) = .ok (.bool true) := by
  simp [cmpValues, Num.cmp, Res.ofOption, h]

theorem cmpValues_ltOp_nat {p q : Nat} (h : p < q) :
    cmpValues .ltOp (.num (.natN p)) (.num (.natN q)) = .ok (.bool true) := by
  simp [cmpValues, Num.cmp, Res.ofOption, h]

theorem cmpValues_gtOp_nat {p q : Nat} (h : q < p) :
    cmpValues .gtOp (.num (.natN p)) (.num (.natN q)) = .ok (.bool true) := by
  simp [cmpValues, Num.cmp, Res.ofOption, h]

/-- `e₁ + e₂` on naturals. -/
theorem evalExp_addNat {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {p q : Nat}
    (h₁ : EvalExp env ρ e₁ (.num (.natN p))) (h₂ : EvalExp env ρ e₂ (.num (.natN q))) :
    EvalExp env ρ (.binE .addOp (.numT .natT) e₁ e₂) (.num (.natN (p + q))) :=
  evalExp_binE_iff.2 ⟨_, h₁, .inr ⟨rfl, _, h₂, by simp [binValues, Num.bin, Res.ofOption]⟩⟩

/-! ## Where a table lives in a state value -/

/-- The table the frame's module lists at index `n` is `t`, in the store `S`. -/
def TableAt (S F : Value) (n : Nat) (t : Value) : Prop :=
  ∃ M Ls As a, S.field? "TABLES" = some (.list Ls) ∧ F.field? "MODULE" = some M ∧
    M.field? "TABLES" = some (.list As) ∧ As[n]? = some (.num (.natN a)) ∧ Ls[a]? = some t

/-- `$table(z, x)` on a state whose table at `n` is `t`. -/
theorem evalExp_table_of {env : Env} (D : StateDefs env) {ρ : VarEnv} {ez ex : Exp}
    {S F t : Value} {n : Nat} (hρ : ρ.findDef? "table" = none)
    (hz : EvalExp env ρ ez (stV S F)) (hx : EvalExp env ρ ex (idxV n)) (ht : TableAt S F n t) :
    EvalExp env ρ (.callE "table" [.expA ez, .expA ex]) t := by
  obtain ⟨M, Ls, As, a, hS, hM, hA, ha, hr⟩ := ht
  exact evalExp_table D hρ hz hx hS hM hA ha hr

/-- `|$table(z, x).REFS|`. -/
theorem evalExp_tableLen {env : Env} (D : StateDefs env) {ρ : VarEnv} {S F t : Value}
    {rs : List Value} {n : Nat} (hz : ρ.findVal? "z" = some (stV S F))
    (hx : ρ.findVal? "x" = some (idxV n)) (hd : ρ.findDef? "table" = none)
    (ht : TableAt S F n t) (hR : t.field? "REFS" = some (.list rs)) :
    EvalExp env ρ (.lenE (.dotE (.callE "table" [.expA (.varE "z"), .expA (.varE "x")]) "REFS"))
      (.num (.natN rs.length)) :=
  evalExp_lenE_iff.2 ⟨rs, evalExp_dotE_iff.2 ⟨t,
    evalExp_table_of D hd (evalExp_var hz) (evalExp_var hx) ht, hR⟩, rfl⟩

/-! ## The rules, for arbitrary values -/

section Rules

variable {env : Env} (D : StateDefs env) (St : StateTyping env)
include D St

/-- The `CONST at i` operand. -/
abbrev aconstV (A : Value) (i : Nat) : Value := .case "CONST" (.tuple [A, idxV i])

/-- `Step_read/table.get-oob`: `z; (CONST at i) (TABLE.GET x) ~> TRAP` when
`i ≥ |$table(z, x).REFS|`. -/
theorem sread_tableGetOob (h : HasRuleAt env "Step_read" "%~>%" 25 Equiv.ExecRead.tableGetOobRule)
    {S F t : Value} {rs : List Value} {a : Silmaril.Wasm.AddrType}
    {i : BitVec a.intType.width} {n : Nat} (hz : TypedV env stateT (stV S F)) (hn : n < 2 ^ 32)
    (ht : TableAt S F n t) (hR : t.field? "REFS" = some (.list rs)) (hi : rs.length ≤ i.toNat) :
    SRead env (cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat, .case "TABLE.GET" (idxV n)])
      [.case "TRAP" (.tuple [])] := by
  let ρ := VarEnv.empty.bindVals [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("x", idxV n)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stV S F) := rfl
  have fa : ρ.findVal? "at" = some (Encode.toValue a) := rfl
  have fi : ρ.findVal? "i" = some (idxV i.toNat) := rfl
  have fx : ρ.findVal? "x" = some (idxV n) := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fa (St.addr a ρ hρ)
      (QuantsOk.cons fi (St.num "at" a i ρ hρ fa) (QuantsOk.cons fx (St.idx n hn ρ hρ)
        QuantsOk.nil))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_listE_iff.2 ⟨_, evalExps_cons (evalExp_case (evalExp_tup2
          (evalExp_subE_iff.2 (evalExp_var fa)) (evalExp_var fi)))
          (evalExps_cons (evalExp_case (evalExp_var fx)) evalExps_nil), rfl⟩)))
      (evalExp_list1 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _,
      evalExp_projE_iff.2 ⟨_, evalExp_uncaseE_iff.2 (evalExp_var fi), Int.le_refl 0, rfl⟩,
      evalExp_tableLen D fz fx rfl ht hR, cmpValues_geOp_nat hi⟩)))

/-- `Step_read/table.get-val`: `z; (CONST at i) (TABLE.GET x) ~> $table(z, x).REFS[i]` when
`i < |$table(z, x).REFS|`. -/
theorem sread_tableGetVal (h : HasRuleAt env "Step_read" "%~>%" 26 Equiv.ExecRead.tableGetValRule)
    {S F t R : Value} {rs : List Value} {a : Silmaril.Wasm.AddrType}
    {i : BitVec a.intType.width} {n : Nat} (hz : TypedV env stateT (stV S F)) (hn : n < 2 ^ 32)
    (ht : TableAt S F n t) (hR : t.field? "REFS" = some (.list rs)) (hr : rs[i.toNat]? = some R) :
    SRead env (cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat, .case "TABLE.GET" (idxV n)])
      [R] := by
  let ρ := VarEnv.empty.bindVals [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("x", idxV n)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stV S F) := rfl
  have fa : ρ.findVal? "at" = some (Encode.toValue a) := rfl
  have fi : ρ.findVal? "i" = some (idxV i.toNat) := rfl
  have fx : ρ.findVal? "x" = some (idxV n) := rfl
  have ep : EvalExp env ρ (.projE (.uncaseE (.varE "i") "%") 0) (.num (.natN i.toNat)) :=
    evalExp_projE_iff.2 ⟨_, evalExp_uncaseE_iff.2 (evalExp_var fi), Int.le_refl 0, rfl⟩
  have er : EvalExp env ρ (.dotE (.callE "table" [.expA (.varE "z"), .expA (.varE "x")]) "REFS")
      (.list rs) := evalExp_dotE_iff.2 ⟨t, evalExp_table_of D rfl (evalExp_var fz) (evalExp_var fx) ht, hR⟩
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fa (St.addr a ρ hρ)
      (QuantsOk.cons fi (St.num "at" a i ρ hρ fa) (QuantsOk.cons fx (St.idx n hn ρ hρ)
        QuantsOk.nil))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_listE_iff.2 ⟨_, evalExps_cons (evalExp_case (evalExp_tup2
          (evalExp_subE_iff.2 (evalExp_var fa)) (evalExp_var fi)))
          (evalExps_cons (evalExp_case (evalExp_var fx)) evalExps_nil), rfl⟩)))
      (evalExp_list1 (evalExp_subE_iff.2 (evalExp_idxE_iff.2 ⟨_, _, er, ep, hr⟩))))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, ep, evalExp_lenE_iff.2 ⟨rs, er, rfl⟩,
      cmpValues_ltOp_nat (List.getElem?_eq_some_iff.1 hr).1⟩)))

/-- `Step_read/table.fill-oob`: `z; (CONST at i) val (CONST at (% n)) (TABLE.FILL x) ~> TRAP` when
`i + n > |$table(z, x).REFS|`. -/
theorem sread_tableFillOob
    (h : HasRuleAt env "Step_read" "%~>%" 28 Equiv.ExecRead.tableFillOobRule)
    {S F t V : Value} {rs : List Value} {a : Silmaril.Wasm.AddrType}
    {i : BitVec a.intType.width} {k n : Nat} (hz : TypedV env stateT (stV S F)) (hn : n < 2 ^ 32)
    (hV : TypedV env valT V) (ht : TableAt S F n t) (hR : t.field? "REFS" = some (.list rs))
    (hi : rs.length < i.toNat + k) :
    SRead env (cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat, V,
        aconstV (Encode.toValue a) k, .case "TABLE.FILL" (idxV n)])
      [.case "TRAP" (.tuple [])] := by
  let ρ := VarEnv.empty.bindVals [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("val", V), ("n", .num (.natN k)), ("x", idxV n)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stV S F) := rfl
  have fa : ρ.findVal? "at" = some (Encode.toValue a) := rfl
  have fi : ρ.findVal? "i" = some (idxV i.toNat) := rfl
  have fv : ρ.findVal? "val" = some V := rfl
  have fk : ρ.findVal? "n" = some (.num (.natN k)) := rfl
  have fx : ρ.findVal? "x" = some (idxV n) := rfl
  have ea : EvalExp env ρ (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []))
      (Encode.toValue a) := evalExp_subE_iff.2 (evalExp_var fa)
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fa (St.addr a ρ hρ)
      (QuantsOk.cons fi (St.num "at" a i ρ hρ fa) (QuantsOk.cons fv (hV ρ hρ)
        (QuantsOk.cons fk (St.nat k ρ hρ) (QuantsOk.cons fx (St.idx n hn ρ hρ) QuantsOk.nil))))))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_listE_iff.2 ⟨_, evalExps_cons (evalExp_case (evalExp_tup2 ea (evalExp_var fi)))
          (evalExps_cons (evalExp_subE_iff.2 (evalExp_var fv))
          (evalExps_cons (evalExp_case (evalExp_tup2 ea (evalExp_case (evalExp_tupE_iff.2
            ⟨_, evalExps_cons (evalExp_var fk) evalExps_nil, rfl⟩))))
          (evalExps_cons (evalExp_case (evalExp_var fx)) evalExps_nil))), rfl⟩)))
      (evalExp_list1 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _,
      evalExp_addNat (evalExp_projE_iff.2 ⟨_, evalExp_uncaseE_iff.2 (evalExp_var fi),
        Int.le_refl 0, rfl⟩) (evalExp_var fk),
      evalExp_tableLen D fz fx rfl ht hR, cmpValues_gtOp_nat hi⟩)))

omit D St in
/-- The shared conclusion shape of `table.set-oob`/`table.set-val`: the left-hand side. -/
theorem evalExp_tableSetLhs {ρ : VarEnv} {Z A I R X : Value} (fz : ρ.findVal? "z" = some Z)
    (fa : ρ.findVal? "at" = some A) (fi : ρ.findVal? "i" = some I) (fr : ρ.findVal? "ref" = some R)
    (fx : ρ.findVal? "x" = some X) :
    EvalExp env ρ (.caseE "%;%" (.tupE [.varE "z", .listE [
      .caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []), .varE "i"]),
      .subE (.varE "ref") (.varT "ref" []) (.varT "instr" []), .caseE "TABLE.SET" (.varE "x")]]))
      (cfgV Z [.case "CONST" (.tuple [A, I]), R, .case "TABLE.SET" X]) :=
  evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_listE_iff.2 ⟨_,
    evalExps_cons (evalExp_case (evalExp_tup2 (evalExp_subE_iff.2 (evalExp_var fa))
      (evalExp_var fi))) (evalExps_cons (evalExp_subE_iff.2 (evalExp_var fr))
      (evalExps_cons (evalExp_case (evalExp_var fx)) evalExps_nil)), rfl⟩))

/-- `Step/table.set-oob`: `z; (CONST at i) ref (TABLE.SET x) ~> z; TRAP` when
`i ≥ |$table(z, x).REFS|`. -/
theorem sstep_tableSetOob (h : HasRuleAt env "Step" "%~>%" 13 Equiv.ExecStepRules.tableSetOobRule)
    {S F t R : Value} {rs : List Value} {a : Silmaril.Wasm.AddrType}
    {i : BitVec a.intType.width} {n : Nat} (hz : TypedV env stateT (stV S F)) (hn : n < 2 ^ 32)
    (hR' : TypedV env refT R) (ht : TableAt S F n t) (hR : t.field? "REFS" = some (.list rs))
    (hi : rs.length ≤ i.toNat) :
    SStep env (cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat, R, .case "TABLE.SET" (idxV n)])
      (cfgV (stV S F) [.case "TRAP" (.tuple [])]) := by
  let ρ := VarEnv.empty.bindVals [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("ref", R), ("x", idxV n)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stV S F) := rfl
  have fa : ρ.findVal? "at" = some (Encode.toValue a) := rfl
  have fi : ρ.findVal? "i" = some (idxV i.toNat) := rfl
  have fr : ρ.findVal? "ref" = some R := rfl
  have fx : ρ.findVal? "x" = some (idxV n) := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fa (St.addr a ρ hρ)
      (QuantsOk.cons fi (St.num "at" a i ρ hρ fa) (QuantsOk.cons fr (hR' ρ hρ)
        (QuantsOk.cons fx (St.idx n hn ρ hρ) QuantsOk.nil)))))
    (evalExp_tup2 (evalExp_tableSetLhs fz fa fi fr fx)
      (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))))))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _,
      evalExp_projE_iff.2 ⟨_, evalExp_uncaseE_iff.2 (evalExp_var fi), Int.le_refl 0, rfl⟩,
      evalExp_tableLen D fz fx rfl ht hR, cmpValues_geOp_nat hi⟩)))

/-- `Step/table.set-val`: `z; (CONST at i) ref (TABLE.SET x) ~> $with_table(z, x, i, ref); ε`
when `i < |$table(z, x).REFS|`. -/
theorem sstep_tableSetVal (h : HasRuleAt env "Step" "%~>%" 14 Equiv.ExecStepRules.tableSetValRule)
    {S S' F M t t' R : Value} {Ls As rs : List Value} {a : Silmaril.Wasm.AddrType}
    {i : BitVec a.intType.width} {n ta : Nat} (hz : TypedV env stateT (stV S F))
    (hn : n < 2 ^ 32) (hR' : TypedV env refT R)
    (hS : S.field? "TABLES" = some (.list Ls)) (hM : F.field? "MODULE" = some M)
    (hA : M.field? "TABLES" = some (.list As)) (ha : As[n]? = some (.num (.natN ta)))
    (ht : Ls[ta]? = some t) (hR : t.field? "REFS" = some (.list rs)) (hi : i.toNat < rs.length)
    (ht' : t.setField "REFS" (.list (rs.set i.toNat R)) = some t')
    (hS' : S.setField "TABLES" (.list (Ls.set ta t')) = some S') :
    SStep env (cfgV (stV S F) [aconstV (Encode.toValue a) i.toNat, R, .case "TABLE.SET" (idxV n)])
      (cfgV (stV S' F) []) := by
  let ρ := VarEnv.empty.bindVals [("z", stV S F), ("at", Encode.toValue a),
    ("i", idxV i.toNat), ("ref", R), ("x", idxV n)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stV S F) := rfl
  have fa : ρ.findVal? "at" = some (Encode.toValue a) := rfl
  have fi : ρ.findVal? "i" = some (idxV i.toNat) := rfl
  have fr : ρ.findVal? "ref" = some R := rfl
  have fx : ρ.findVal? "x" = some (idxV n) := rfl
  have ep : EvalExp env ρ (.projE (.uncaseE (.varE "i") "%") 0) (.num (.natN i.toNat)) :=
    evalExp_projE_iff.2 ⟨_, evalExp_uncaseE_iff.2 (evalExp_var fi), Int.le_refl 0, rfl⟩
  have hT : TableAt S F n t := ⟨M, Ls, As, ta, hS, hM, hA, ha, ht⟩
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fa (St.addr a ρ hρ)
      (QuantsOk.cons fi (St.num "at" a i ρ hρ fa) (QuantsOk.cons fr (hR' ρ hρ)
        (QuantsOk.cons fx (St.idx n hn ρ hρ) QuantsOk.nil)))))
    (evalExp_tup2 (evalExp_tableSetLhs fz fa fi fr fx)
      (evalExp_case (evalExp_tup2
        (evalExp_withTable D rfl (evalExp_var fz) (evalExp_var fx) ep (evalExp_var fr) hS hM hA ha
          ht hR hi ht' hS')
        (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩))))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, ep, evalExp_tableLen D fz fx rfl hT hR,
      cmpValues_ltOp_nat hi⟩)))

/-- `Step/elem.drop`: `z; (ELEM.DROP x) ~> $with_elem(z, x, ε); ε`. -/
theorem sstep_elemDrop (h : HasRuleAt env "Step" "%~>%" 17 Equiv.ExecStepRules.elemDropRule)
    {S S' F M t t' : Value} {Ls As : List Value} {n ea : Nat} (hz : TypedV env stateT (stV S F))
    (hn : n < 2 ^ 32)
    (hS : S.field? "ELEMS" = some (.list Ls)) (hM : F.field? "MODULE" = some M)
    (hA : M.field? "ELEMS" = some (.list As)) (ha : As[n]? = some (.num (.natN ea)))
    (ht : Ls[ea]? = some t) (ht' : t.setField "REFS" (.list []) = some t')
    (hS' : S.setField "ELEMS" (.list (Ls.set ea t')) = some S') :
    SStep env (cfgV (stV S F) [.case "ELEM.DROP" (idxV n)]) (cfgV (stV S' F) []) := by
  let ρ := VarEnv.empty.bindVals [("z", stV S F), ("x", idxV n)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stV S F) := rfl
  have fx : ρ.findVal? "x" = some (idxV n) := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fx (St.idx n hn ρ hρ) QuantsOk.nil))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_var fx)))))
      (evalExp_case (evalExp_tup2
        (evalExp_withElem D rfl (evalExp_var fz) (evalExp_var fx)
          (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩) hS hM hA ha ht ht' hS')
        (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩))))
    (fun _ h => by cases h)

end Rules

/-! ## Forward, at the Core encoding -/

section Forward

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- `Store.table?` unfolded. -/
theorem Store.table?_eq_some {s : Store H} {f : Frame} {x : TableIdx} {a : Nat}
    {t : TableInst} (h : s.table? f x = some (a, t)) :
    f.module.tables[x.toNat]? = some a ∧ s.tables[a]? = some t := by
  simp only [Store.table?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨a', ha, t', ht, rfl, rfl⟩ := h
  exact ⟨ha, ht⟩

/-- `Store.elem?` unfolded. -/
theorem Store.elem?_eq_some {s : Store H} {f : Frame} {x : ElemIdx} {a : Nat}
    {e : ElemInst} (h : s.elem? f x = some (a, e)) :
    f.module.elems[x.toNat]? = some a ∧ s.elems[a]? = some e := by
  simp only [Store.elem?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨a', ha, e', he, rfl, rfl⟩ := h
  exact ⟨ha, he⟩

/-- The encoded table the module lists at `x`. -/
theorem tableAt_of_table? (hn : H → String) {s : Store H} {f : Frame} {x : TableIdx} {a : Nat}
    {t : TableInst} (h : s.table? f x = some (a, t)) :
    TableAt (storeV hn s) (frameV f) x.toNat (tableInstToValue CT t) := by
  obtain ⟨ha, ht⟩ := Store.table?_eq_some h
  exact ⟨_, _, _, a, storeV_TABLES hn s, frameV_MODULE f, moduleV_TABLES _, getElem?_map_natN ha,
    by simp [ht]⟩

@[simp] theorem tableInstV_REFS (t : TableInst) :
    (tableInstToValue CT t).field? "REFS" = some (.list (t.refs.map refToValue)) := rfl

/-- An address-typed constant encodes as `CONST at i`. -/
theorem adminToV_aconst (a : AddrType) (i : BitVec a.intType.width) :
    adminToV (aconst a i) = aconstV (Encode.toValue a) i.toNat := by
  cases a <;> rfl

/-- A reference encodes as itself. -/
theorem adminToV_ref (r : Ref) : adminToV (.ref r) = refToValue r := rfl

/-- The trap encodes as `TRAP`. -/
theorem adminToV_trap : adminToV (.trap : Admin) = .case "TRAP" (.tuple []) := rfl

/-- Writing a reference into an encoded table. -/
theorem tableInstV_setRef (t : TableInst) (i : Nat) (r : Ref) :
    (tableInstToValue CT t).setField "REFS" (.list ((t.refs.map refToValue).set i (refToValue r))) =
      some (tableInstToValue CT { t with refs := t.refs.set i r }) := by
  simp [tableInstToValue, List.map_set]

/-- Replacing a table of an encoded store encodes `Store.setTable`. -/
theorem storeV_setTable (hn : H → String) (s : Store H) (a : Nat) (t : TableInst) :
    (storeV hn s).setField "TABLES" (.list ((s.tables.map (tableInstToValue CT)).set a
      (tableInstToValue CT t))) = some (storeV hn (s.setTable a t)) := by
  simp [storeV, Store.setTable, List.map_set]

/-- Emptying an encoded element segment. -/
theorem elemInstV_drop (e : ElemInst) :
    (elemInstToValue CT e).setField "REFS" (.list []) =
      some (elemInstToValue CT { e with refs := [] }) := by
  simp [elemInstToValue]

/-- Dropping an element segment of an encoded store encodes `Store.setElem`. -/
theorem storeV_setElem (hn : H → String) (s : Store H) {a : Nat} {e : ElemInst}
    (he : s.elems[a]? = some e) :
    (storeV hn s).setField "ELEMS" (.list ((s.elems.map (elemInstToValue CT)).set a
      (elemInstToValue CT { e with refs := [] }))) = some (storeV hn (s.setElem a [])) := by
  simp [storeV, Store.setElem, List.modify_eq_set_of_getElem? he, List.map_set]

variable (B : Builtins) {hn : H → String} (T : TypingFacts (simEnv B) hn)
  (St : StateTyping (simEnv B))
include T St

/-- A reference in the code of a typed configuration is a typed `ref`. -/
theorem typedV_ref_of_mem {s : Store H} {f : Frame} {is : List Admin}
    (hc : Typed (simEnv B) hn ⟨s, f, is⟩) {r : Ref} (hr : Admin.ref r ∈ is) :
    TypedV (simEnv B) refT (refToValue r) :=
  St.ref r (typedV_val_of_mem T hc (v := .ref r) hr)

/-- `TableStep.getOob`, forward. -/
theorem fwd_tableGetOob {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType}
    {i : BitVec a.intType.width} {ta : Nat} {ti : TableInst} (ht : s.table? f x = some (ta, ti))
    (h : ti.refs.length ≤ i.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, .plain (.tableGet x)]⟩ ⟨s, f, [.trap]⟩ := by
  intro hc hc'
  show SStep _ (cfgV _ [adminToV (aconst a i), _]) (cfgV _ [adminToV .trap])
  rw [adminToV_aconst, adminToV_trap]
  have hcode : TypedV (simEnv B) instrsT
      (.list [aconstV (Encode.toValue a) i.toNat, adminToV (.plain (.tableGet x))]) := by
    simpa only [adminsToV_cons, adminsToV_nil, adminToV_aconst] using typedV_code T hc
  exact sstep_read (hasStepRules_simEnv B).read (typedV_state T hc) hcode (typedV_code T hc')
    (sread_tableGetOob (stateDefs_simEnv B) St (hasReadRules_simEnv B).tableGetOob
      (typedV_state T hc) x.value.isLt (tableAt_of_table? hn ht) (tableInstV_REFS ti)
      (by simpa using h))

/-- `TableStep.getVal`, forward. -/
theorem fwd_tableGetVal {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType}
    {i : BitVec a.intType.width} {ta : Nat} {ti : TableInst} {r : Ref}
    (ht : s.table? f x = some (ta, ti)) (h : ti.refs[i.toNat]? = some r) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, .plain (.tableGet x)]⟩ ⟨s, f, [.ref r]⟩ := by
  intro hc hc'
  show SStep _ (cfgV _ [adminToV (aconst a i), _]) (cfgV _ [adminToV (.ref r)])
  rw [adminToV_aconst, adminToV_ref]
  have hcode : TypedV (simEnv B) instrsT
      (.list [aconstV (Encode.toValue a) i.toNat, adminToV (.plain (.tableGet x))]) := by
    simpa only [adminsToV_cons, adminsToV_nil, adminToV_aconst] using typedV_code T hc
  exact sstep_read (hasStepRules_simEnv B).read (typedV_state T hc) hcode (typedV_code T hc')
    (sread_tableGetVal (stateDefs_simEnv B) St (hasReadRules_simEnv B).tableGetVal
      (typedV_state T hc) x.value.isLt (tableAt_of_table? hn ht) (tableInstV_REFS ti)
      (by simp [h]))

/-- `TableStep.fillOob`, forward. -/
theorem fwd_tableFillOob {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType}
    {i n : BitVec a.intType.width} {v : Val} {ta : Nat} {ti : TableInst}
    (ht : s.table? f x = some (ta, ti)) (h : ti.refs.length < i.toNat + n.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, v.toAdmin, aconst a n, .plain (.tableFill x)]⟩
      ⟨s, f, [.trap]⟩ := by
  intro hc hc'
  have hv : TypedV (simEnv B) valT (valV v) := typedV_val_of_mem T hc (by simp)
  show SStep _ (cfgV _ [adminToV (aconst a i), adminToV v.toAdmin, adminToV (aconst a n), _])
    (cfgV _ [adminToV .trap])
  rw [adminToV_aconst, adminToV_aconst, adminToV_toAdmin, adminToV_trap]
  have hcode : TypedV (simEnv B) instrsT (.list [aconstV (Encode.toValue a) i.toNat, valV v,
      aconstV (Encode.toValue a) n.toNat, adminToV (.plain (.tableFill x))]) := by
    simpa only [adminsToV_cons, adminsToV_nil, adminToV_aconst, adminToV_toAdmin]
      using typedV_code T hc
  exact sstep_read (hasStepRules_simEnv B).read (typedV_state T hc) hcode (typedV_code T hc')
    (sread_tableFillOob (stateDefs_simEnv B) St (hasReadRules_simEnv B).tableFillOob
      (typedV_state T hc) x.value.isLt hv (tableAt_of_table? hn ht) (tableInstV_REFS ti)
      (by simpa using h))

/-- `TableStep.setOob`, forward. -/
theorem fwd_tableSetOob {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType}
    {i : BitVec a.intType.width} {r : Ref} {ta : Nat} {ti : TableInst}
    (ht : s.table? f x = some (ta, ti)) (h : ti.refs.length ≤ i.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, .ref r, .plain (.tableSet x)]⟩ ⟨s, f, [.trap]⟩ := by
  intro hc _
  show SStep _ (cfgV _ [adminToV (aconst a i), adminToV (.ref r), _]) (cfgV _ [adminToV .trap])
  rw [adminToV_aconst, adminToV_ref, adminToV_trap]
  exact sstep_tableSetOob (stateDefs_simEnv B) St (hasStepRules_simEnv B).tableSetOob
    (typedV_state T hc) x.value.isLt (typedV_ref_of_mem B T St hc (by simp))
    (tableAt_of_table? hn ht) (tableInstV_REFS ti) (by simpa using h)

/-- `TableStep.setVal`, forward. -/
theorem fwd_tableSetVal {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType}
    {i : BitVec a.intType.width} {r : Ref} {ta : Nat} {ti : TableInst}
    (ht : s.table? f x = some (ta, ti)) (h : i.toNat < ti.refs.length) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, .ref r, .plain (.tableSet x)]⟩
      ⟨s.setTable ta { ti with refs := ti.refs.set i.toNat r }, f, []⟩ := by
  intro hc _
  obtain ⟨hta, hti⟩ := Store.table?_eq_some ht
  show SStep _ (cfgV _ [adminToV (aconst a i), adminToV (.ref r), _]) (cfgV _ [])
  rw [adminToV_aconst, adminToV_ref]
  exact sstep_tableSetVal (stateDefs_simEnv B) St (hasStepRules_simEnv B).tableSetVal
    (typedV_state T hc) x.value.isLt (typedV_ref_of_mem B T St hc (by simp))
    (storeV_TABLES hn s) (frameV_MODULE f) (moduleV_TABLES _) (getElem?_map_natN hta)
    (by simp [hti]) (tableInstV_REFS ti) (by simpa using h) (tableInstV_setRef ti i.toNat r)
    (storeV_setTable hn s ta _)

/-- `TableStep.elemDrop`, forward. -/
theorem fwd_elemDrop {s : Store H} {f : Frame} {y : ElemIdx} {ea : Nat} {ei : ElemInst}
    (he : s.elem? f y = some (ea, ei)) :
    FwdP (simEnv B) hn ⟨s, f, [.plain (.elemDrop y)]⟩ ⟨s.setElem ea [], f, []⟩ := by
  intro hc _
  obtain ⟨hea, hei⟩ := Store.elem?_eq_some he
  exact sstep_elemDrop (stateDefs_simEnv B) St (hasStepRules_simEnv B).elemDrop
    (typedV_state T hc) y.value.isLt (storeV_ELEMS hn s) (frameV_MODULE f) (moduleV_ELEMS _)
    (getElem?_map_natN hea) (by simp [hei]) (elemInstV_drop ei) (storeV_setElem hn s hei)

end Forward

end Silmaril.Wasm.SpecTec.Sim.State
