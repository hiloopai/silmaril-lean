module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkTCopy

/-!
# `table.init`, `elem.drop` and `data.drop` forward in `simEnv20T`

`Step_read` 19–21 of the 2.0 script are `table.init-trap`, `-zero` and `-succ`. `-succ` reads one
reference of the element segment and writes it with `table.set`:

* `firesT_tableInitTrap` (19);
* `firesT_tableInitZero` (20, `-- otherwise`): rule 19's body is refuted where both bounds hold
  (`otherwise20T`);
* `firesT_tableInitSucc` (21, `-- otherwise`): rules 19 and 20 are refuted (`otherwise21T`).

`elem.drop` and `data.drop` are `Step` 10 and 21 of the 2.0 script, rules 11 and 22 of
`simEnv20T`; they have no premise. Round 3 fires them in `simEnv20` (`Whole.fires_elemDrop`,
`fires_dataDrop`); here they fire in `simEnv20T` from a state typed only there
(`firesT_elemDrop`, `firesT_dataDrop`), through round 5's `StoreFn.firesT_step_of20`.

**Restatement.** V2 computes `j + 1` and `i + 1` in `i32`; the script does not. `-succ` asks for
both below `2 ^ 32`. They hold when the table and the element segment have fewer than `2 ^ 32`
entries, since the bounds give `j + n ≤ |table|` and `i + n ≤ |elem|`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreBulk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecNumeric (cmpValues_eq_true_iff)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV ValsOnly stateT QuantsOk RuleBody PremW otherwiseAt
  evalExp_tup2 evalExp_case evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (otherwiseAt_of_table tags_of_take LhsIn)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Whole (copyQs tableInitLhs tableInitE tableInitTrapRule
  tableInitZeroRule tableInitSuccRule elemRefsE tableLenE constJE constIE constNE jPay iPay predE
  constSuccE constPE trapRhs evalExp_constIE evalExp_constNE evalExp_trapRhs evalExp_iPay
  evalExp_jPay evalExp_addNat20 evalExp_tableLen20 evalExp_elem20 evalExp_constVar
  evalExp_constPE evalExp_pred evalExp_gtNat hasRuleAt_tableInitTrap hasRuleAt_tableInitZero
  hasRuleAt_tableInitSucc const3_of_lhs initIdx_of_lhs constI32_inj zero_of_prem not_or_true
  adminsToV_tableInitSucc hasRuleAt_elemDrop hasRuleAt_dataDrop evalExp_withElem20
  evalExp_withData20)
open Silmaril.Wasm.SpecTec.Sim20.StoreFn (firesT_read_of20 firesT_step_of20 hasRuleAtT_read
  readGood evalBack20 quantsOkT_z ifBack readTagsT)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evRule evExp evPrems)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-! ## The left-hand side -/

/-- The code of the three rules. -/
abbrev tinitCode (j i n : BitVec 32) (x : TableIdx) (y : ElemIdx) : List Admin :=
  [constI32 j, constI32 i, constI32 n, .plain (.tableInit x y)]

/-- The scope of the three rules. -/
abbrev tableInitScope (s : Store H) (f : Frame) (j i n : BitVec 32) (x : TableIdx) (y : ElemIdx) :
    List (IL.Id × Value) :=
  [("z", stateV hn s f), ("j", pctV j.toNat), ("i", pctV i.toNat), ("n", .num (.natN n.toNat)),
    ("x", idxV x), ("y", idxV y)]

/-- The left-hand side, evaluated in `simEnv20`. -/
theorem evalExp_tableInitLhs {s : Store H} {f : Frame} {j i n : BitVec 32} {x : TableIdx}
    {y : ElemIdx} :
    EvalExp (E20 B) (VarEnv.empty.bindVals (tableInitScope (hn := hn) s f j i n x y)) tableInitLhs
      (configV hn ⟨s, f, tinitCode j i n x y⟩) :=
  evalExp_case (evalExp_tup2 (evalExp_var rfl) (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_constJE rfl) (evalExps_cons (evalExp_constIE rfl) (evalExps_cons (evalExp_constNE rfl)
      (evalExps_cons (evalExp_case (evalExp_tup2 (evalExp_var rfl) (evalExp_var rfl)))
        evalExps_nil))), rfl⟩))

/-- The quantifiers, typed in `simEnv20T`. -/
theorem quantsOkT_tableInit {s : Store H} {f : Frame} {j i n : BitVec 32} {x : TableIdx}
    {y : ElemIdx} (hz : TypedV (simEnv20T B) stateT (stateV hn s f)) :
    QuantsOk (simEnv20T B) (VarEnv.empty.bindVals (tableInitScope (hn := hn) s f j i n x y))
      copyQs :=
  have hρ := Pure.valsOnly_bindVals (tableInitScope (hn := hn) s f j i n x y)
  quantsOkT_z hρ rfl hz (by decide) (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 j _ hρ)
    (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons rfl (Whole.typedV_n20 _ _ hρ)
        (QuantsOk.cons rfl (Whole.typedV_idx20 x _ hρ)
          (QuantsOk.cons rfl (Whole.typedV_idx20 y _ hρ) QuantsOk.nil)))))

/-- The tags of a `table.init` left-hand side. -/
theorem lhsIn_tinitCode (s : Store H) (f : Frame) (j i n : BitVec 32) (x : TableIdx)
    (y : ElemIdx) :
    LhsIn ["CONST", "TABLE.INIT"] (configV hn ⟨s, f, tinitCode j i n x y⟩) := by
  refine Or.inr ⟨_, _, rfl, ?_⟩
  intro u hu op w hw
  simp only [adminsToV, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl <;>
  · rw [← Whole.adminToV_case20 hw]
    simp [Whole.adminHead20, Whole.instrHead20]

/-- The scope of a `table.init` rule body, read back. -/
structure InitScopeT (σ : List (IL.Id × Value)) (j i n : BitVec 32) (x : TableIdx) (y : ElemIdx) :
    Prop where
  fj : (VarEnv.empty.bindVals σ).findVal? "j" = some (pctV j.toNat)
  fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat)
  fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat))
  fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x)
  fy : (VarEnv.empty.bindVals σ).findVal? "y" = some (idxV y)

/-- A `table.init` left-hand side at a known code binds the code's operands. -/
theorem initScopeT_of {σ : List (IL.Id × Value)} {j i n : BitVec 32} {x : TableIdx}
    {y : ElemIdx}
    (hes : EvalExps (E20 B) (VarEnv.empty.bindVals σ) [constJE, constIE, constNE, tableInitE]
      (adminsToV (tinitCode j i n x y))) :
    InitScopeT σ j i n x y := by
  obtain ⟨j', i', n', a₄, hc, fj, fi, fn, h₄⟩ := const3_of_lhs hes
  obtain ⟨x', y', rfl, fx, fy⟩ := initIdx_of_lhs h₄
  have hc' : constI32 j = constI32 j' ∧ constI32 i = constI32 i' ∧ constI32 n = constI32 n' ∧
      (Admin.plain (.tableInit x y) : Admin) = .plain (.tableInit x' y') := by
    simpa only [List.cons.injEq, and_true] using hc
  obtain ⟨hj, hi, hn, hxy⟩ := hc'
  cases hxy
  rw [constI32_inj hj, constI32_inj hi, constI32_inj hn]
  exact ⟨fj, fi, fn, fx, fy⟩

/-! ## Rule bodies in `simEnv20T`, read back -/

/-- A `table.init` rule body in `simEnv20T` at a `table.init` left-hand side binds the state
and the operands, and its premises hold in `simEnv20T`. -/
theorem tableInitBodyT_parts {D : Sim.Interp} {els : Prop} {nm : IL.Id} {rhs : Exp}
    {prems : List Prem} {k : Nat}
    (hR : HasRuleAt (E20 B) "Step_read" "%~>%" k
      (.ruleD nm copyQs "%~>%" (.tupE [tableInitLhs, rhs]) prems))
    {s : Store H} {f : Frame} {j i n : BitVec 32} {x : TableIdx} {y : ElemIdx} {w : Value}
    (hbody : RuleBody (simEnv20T B) D els [] [] "%~>%"
      (.ruleD nm copyQs "%~>%" (.tupE [tableInitLhs, rhs]) prems)
      (.tuple [configV hn ⟨s, f, tinitCode j i n x y⟩, w])) :
    ∃ σ : List (IL.Id × Value), (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) ∧
      InitScopeT σ j i n x y ∧ RelFree.GoodEvs RelFree.bad20 (evPrems prems) ∧
      ∀ pr ∈ prems, PremW (simEnv20T B) D els (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨-, ρ₀, σ, hps, -, he, hp⟩ := hbody
  obtain rfl : ρ₀ = VarEnv.empty := (Option.some.inj hps).symm
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have hG' : (RelFree.GoodEvs RelFree.bad20 (Sim.Round7.Script.evParams copyQs) ∧
      RelFree.GoodEvs RelFree.bad20 (evExp (.tupE [tableInitLhs, rhs]))) ∧
      RelFree.GoodEvs RelFree.bad20 (evPrems prems) := by
    simpa only [evRule, RelFree.goodEvs_append] using RelFree.goodEvs_of_all (readGood hR)
  have hl := Sim.RefsGC.lhs_of_concl (evalBack20 hρ hG'.1.2 he)
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 hl
  have hu' : u = .tuple [stateV hn s f, .list (adminsToV (tinitCode j i n x y))] :=
    (Value.case.inj hcu.symm).2
  obtain ⟨hZ, hL⟩ := Pure.evalExp_tup2_inv (hu' ▸ hu)
  exact ⟨σ, evalExp_varE_iff.1 hZ, initScopeT_of (Sim.RefsGC.elems_of_list hL), hG'.2, hp⟩

/-- `|$elem(z, y).REFS|`. -/
theorem evalExp_elemLen20 {ρ : VarEnv} {s : Store H} {f : Frame} {y : ElemIdx} {a : Nat}
    {ei : ElemInst} (hρ : ρ.findDef? "elem" = none)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fy : ρ.findVal? "y" = some (idxV y))
    (ha : f.module.elems[y.toNat]? = some a) (he : s.elems[a]? = some ei) :
    EvalExp (E20 B) ρ (.lenE elemRefsE) (.num (.natN ei.refs.length)) := by
  refine evalExp_lenE_iff.2 ⟨ei.refs.map refV, evalExp_dotE_iff.2 ⟨elemInstV ei,
    evalExp_elem20 hρ (evalExp_var fz) (evalExp_var fy) ha he, rfl⟩, ?_⟩
  simp

/-- **Rule 19's body is refuted in `simEnv20T`** where both bounds hold. -/
theorem not_tableInitTrapBodyT {D : Sim.Interp} {els : Prop} {s : Store H} {f : Frame}
    {j i n : BitVec 32} {x : TableIdx} {y : ElemIdx} {ax ay : Nat} {ti : TableInst}
    {ei : ElemInst}
    (hax : f.module.tables[x.toNat]? = some ax) (htx : s.tables[ax]? = some ti)
    (hay : f.module.elems[y.toNat]? = some ay) (hey : s.elems[ay]? = some ei)
    (hb : i.toNat + n.toNat ≤ ei.refs.length ∧ j.toNat + n.toNat ≤ ti.refs.length) (w : Value) :
    ¬ RuleBody (simEnv20T B) D els [] [] "%~>%" tableInitTrapRule
      (.tuple [configV hn ⟨s, f, tinitCode j i n x y⟩, w]) := by
  intro hbody
  obtain ⟨σ, fz, S, hG, hp⟩ := tableInitBodyT_parts hasRuleAt_tableInitTrap hbody
  have hpr := ifBack (Pure.valsOnly_bindVals σ) hG hp (List.mem_singleton_self _)
  have h₁ : EvalExp (E20 B) (VarEnv.empty.bindVals σ) (.cmpE .gtOp (.numT .natT)
      (.binE .addOp (.numT .natT) iPay (.varE "n")) (.lenE elemRefsE)) (.bool false) := by
    have h := evalExp_gtNat (evalExp_addNat20 (evalExp_iPay S.fi) (evalExp_var S.fn))
      (evalExp_elemLen20 (B := B) rfl fz S.fy hay hey)
    rwa [show decide (ei.refs.length < i.toNat + n.toNat) = false by simp; omega] at h
  have h₂ : EvalExp (E20 B) (VarEnv.empty.bindVals σ) (.cmpE .gtOp (.numT .natT)
      (.binE .addOp (.numT .natT) jPay (.varE "n")) tableLenE) (.bool false) := by
    have h := evalExp_gtNat (evalExp_addNat20 (evalExp_jPay S.fj) (evalExp_var S.fn))
      (evalExp_tableLen20 (B := B) rfl fz S.fx hax htx)
    rwa [show decide (ti.refs.length < j.toNat + n.toNat) = false by simp; omega] at h
  exact not_or_true h₁ h₂ hpr

/-- **Rule 20's body is refuted in `simEnv20T`** at a nonzero count. -/
theorem not_tableInitZeroBodyT {D : Sim.Interp} {els : Prop} {s : Store H} {f : Frame}
    {j i n : BitVec 32} {x : TableIdx} {y : ElemIdx} (hn0 : n ≠ 0) (w : Value) :
    ¬ RuleBody (simEnv20T B) D els [] [] "%~>%" tableInitZeroRule
      (.tuple [configV hn ⟨s, f, tinitCode j i n x y⟩, w]) := by
  intro hbody
  obtain ⟨σ, -, S, hG, hp⟩ := tableInitBodyT_parts hasRuleAt_tableInitZero hbody
  exact hn0 (zero_of_prem S.fn (ifBack (Pure.valsOnly_bindVals σ) hG hp
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))))

/-! ## `otherwise` in `simEnv20T` -/

/-- **`otherwise` for rule 20 in `simEnv20T`**, where both bounds hold. -/
theorem otherwise20T {s : Store H} {f : Frame} {j i n : BitVec 32} {x : TableIdx} {y : ElemIdx}
    {ax ay : Nat} {ti : TableInst} {ei : ElemInst}
    (hax : f.module.tables[x.toNat]? = some ax) (htx : s.tables[ax]? = some ti)
    (hay : f.module.elems[y.toNat]? = some ay) (hey : s.elems[ay]? = some ei)
    (hb : i.toNat + n.toNat ≤ ei.refs.length ∧ j.toNat + n.toNat ≤ ti.refs.length) (w : Value) :
    otherwiseAt (simEnv20T B) "Step_read" [] 20
      (.tuple [configV hn ⟨s, f, tinitCode j i n x y⟩, w]) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAtT_read (hasRuleAt_tableInitTrap (B := B))
  refine otherwiseAt_of_table hrel (tags_of_take hrel readTagsT) (by decide)
    (lhsIn_tinitCode s f j i n x y) (exc := [19]) (by decide) ?_
  intro k hk _ r hr w' hw
  obtain ⟨c', rfl⟩ := Whole.sameLhs_inv hw
  obtain rfl := List.mem_singleton.1 hk
  rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_tableInitTrap) hr]
  exact not_tableInitTrapBodyT hax htx hay hey hb c'

/-- **`otherwise` for rule 21 in `simEnv20T`**, where both bounds hold and `n ≠ 0`. -/
theorem otherwise21T {s : Store H} {f : Frame} {j i n : BitVec 32} {x : TableIdx} {y : ElemIdx}
    {ax ay : Nat} {ti : TableInst} {ei : ElemInst}
    (hax : f.module.tables[x.toNat]? = some ax) (htx : s.tables[ax]? = some ti)
    (hay : f.module.elems[y.toNat]? = some ay) (hey : s.elems[ay]? = some ei)
    (hb : i.toNat + n.toNat ≤ ei.refs.length ∧ j.toNat + n.toNat ≤ ti.refs.length) (hn0 : n ≠ 0)
    (w : Value) :
    otherwiseAt (simEnv20T B) "Step_read" [] 21
      (.tuple [configV hn ⟨s, f, tinitCode j i n x y⟩, w]) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAtT_read (hasRuleAt_tableInitTrap (B := B))
  refine otherwiseAt_of_table hrel (tags_of_take hrel readTagsT) (by decide)
    (lhsIn_tinitCode s f j i n x y) (exc := [19, 20]) (by decide) ?_
  intro k hk _ r hr w' hw
  obtain ⟨c', rfl⟩ := Whole.sameLhs_inv hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_tableInitTrap) hr]
    exact not_tableInitTrapBodyT hax htx hay hey hb c'
  · rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_tableInitZero) hr]
    exact not_tableInitZeroBodyT hn0 c'

/-! ## The three rules fire -/

/-- A `table.init` rule fires in `simEnv20T` from its right-hand side evaluated in `simEnv20`
and its premises in `simEnv20T`. -/
theorem firesT_tableInit_of {k : Nat} {nm : IL.Id} {rhs : Exp} {prems : List Prem}
    (hR : HasRuleAt (E20 B) "Step_read" "%~>%" k
      (.ruleD nm copyQs "%~>%" (.tupE [tableInitLhs, rhs]) prems))
    {s : Store H} {f : Frame} {j i n : BitVec 32} {x : TableIdx} {y : ElemIdx} {W : Value}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (hr : EvalExp (E20 B) (VarEnv.empty.bindVals (tableInitScope (hn := hn) s f j i n x y)) rhs W)
    (hp : ∀ pr ∈ prems, PremW (simEnv20T B) (Sim.DDerives (simEnv20T B) (Sim.otherwise (simEnv20T B)))
      (Sim.otherwise (simEnv20T B) "Step_read" [] k
        (.tuple [configV hn ⟨s, f, tinitCode j i n x y⟩, W]))
      (VarEnv.empty.bindVals (tableInitScope (hn := hn) s f j i n x y)) pr) :
    Fires (simEnv20T B) "Step_read" k (.tuple [configV hn ⟨s, f, tinitCode j i n x y⟩, W]) := by
  have hρ := Pure.valsOnly_bindVals (tableInitScope (hn := hn) s f j i n x y)
  have hGe : RelFree.GoodEvs RelFree.bad20 (evExp (.tupE [tableInitLhs, rhs])) := by
    have hG := RelFree.goodEvs_of_all (readGood hR)
    simp only [evRule, RelFree.goodEvs_append] at hG
    exact hG.1.2
  exact Pure.fires_of_ruleAt (hasRuleAtT_read hR) _ (quantsOkT_tableInit hz)
    (StoreDeep.evalT_of_20 hρ hGe (evalExp_tup2 evalExp_tableInitLhs hr)) hp

/-- **`Step_read/table.init-trap` in `simEnv20T`.** -/
theorem firesT_tableInitTrap {s : Store H} {f : Frame} {j i n : BitVec 32} {x : TableIdx}
    {y : ElemIdx} {ax ay : Nat} {ti : TableInst} {ei : ElemInst}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (hax : f.module.tables[x.toNat]? = some ax) (htx : s.tables[ax]? = some ti)
    (hay : f.module.elems[y.toNat]? = some ay) (hey : s.elems[ay]? = some ei)
    (hlt : ei.refs.length < i.toNat + n.toNat ∨ ti.refs.length < j.toNat + n.toNat) :
    Fires (simEnv20T B) "Step_read" 19
      (.tuple [configV hn ⟨s, f, tinitCode j i n x y⟩, .list (adminsToV [.trap])]) := by
  refine firesT_read_of20 (D := fun _ _ _ _ => True) (els := True) hasRuleAt_tableInitTrap rfl
    (tableInitScope (hn := hn) s f j i n x y) (quantsOkT_tableInit hz)
    (evalExp_tup2 evalExp_tableInitLhs evalExp_trapRhs) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (Whole.evalExp_or
    (evalExp_gtNat (evalExp_addNat20 (evalExp_iPay rfl) (evalExp_var rfl))
      (evalExp_elemLen20 rfl rfl rfl hay hey))
    (evalExp_gtNat (evalExp_addNat20 (evalExp_jPay rfl) (evalExp_var rfl))
      (evalExp_tableLen20 rfl rfl rfl hax htx))
    (by simpa using hlt))

/-- **`Step_read/table.init-zero` in `simEnv20T`.** -/
theorem firesT_tableInitZero {s : Store H} {f : Frame} {j i : BitVec 32} {x : TableIdx}
    {y : ElemIdx} {ax ay : Nat} {ti : TableInst} {ei : ElemInst}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (hax : f.module.tables[x.toNat]? = some ax) (htx : s.tables[ax]? = some ti)
    (hay : f.module.elems[y.toNat]? = some ay) (hey : s.elems[ay]? = some ei)
    (hb : i.toNat ≤ ei.refs.length ∧ j.toNat ≤ ti.refs.length) :
    Fires (simEnv20T B) "Step_read" 20
      (.tuple [configV hn ⟨s, f, tinitCode j i 0 x y⟩, .list (adminsToV [])]) := by
  refine firesT_tableInit_of hasRuleAt_tableInitZero hz Pure.evalExp_list0 ?_
  intro pr hpr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
  rcases hpr with rfl | rfl
  · exact .elsePr (otherwise20T hax htx hay hey (by simpa using hb) _)
  · refine .ifPr (StoreDeep.evalT_of_20 (Pure.valsOnly_bindVals _)
      (RelFree.goodEvs_of_all (by decide)) ?_)
    exact evalExp_cmpE_iff.2 ⟨_, _, evalExp_var rfl, evalExp_numE_iff.2 rfl,
      cmpValues_eq_true_iff.2 rfl⟩

/-- **`Step_read/table.init-succ` in `simEnv20T`**, where `j + 1` and `i + 1` do not wrap. -/
theorem firesT_tableInitSucc {s : Store H} {f : Frame} {j i n : BitVec 32} {x : TableIdx}
    {y : ElemIdx} {ax ay : Nat} {ti : TableInst} {ei : ElemInst} {r : Ref}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (hax : f.module.tables[x.toNat]? = some ax) (htx : s.tables[ax]? = some ti)
    (hay : f.module.elems[y.toNat]? = some ay) (hey : s.elems[ay]? = some ei)
    (hb : i.toNat + n.toNat ≤ ei.refs.length ∧ j.toNat + n.toNat ≤ ti.refs.length) (hn0 : n ≠ 0)
    (hr : ei.refs[i.toNat]? = some r) (hj1 : j.toNat + 1 < 2 ^ 32) (hi1 : i.toNat + 1 < 2 ^ 32) :
    Fires (simEnv20T B) "Step_read" 21 (.tuple [configV hn ⟨s, f, tinitCode j i n x y⟩,
      .list (adminsToV [constI32 j, aref r, .plain (.tableSet x), constI32 (j + 1),
        constI32 (i + 1), constI32 (n - 1), .plain (.tableInit x y)])]) := by
  have hn1 : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
  have hel : EvalExp (E20 B) (VarEnv.empty.bindVals (tableInitScope (hn := hn) s f j i n x y))
      (.subE (.idxE elemRefsE iPay) (.varT "ref" []) (.varT "admininstr" [])) (refV r) :=
    evalExp_subE_iff.2 (evalExp_idxE_iff.2 ⟨_, i.toNat, evalExp_dotE_iff.2 ⟨elemInstV ei,
      evalExp_elem20 rfl (evalExp_var rfl) (evalExp_var rfl) hay hey, rfl⟩, evalExp_iPay rfl,
      by simp [Value.idx?, List.getElem?_map, hr]⟩)
  rw [adminsToV_tableInitSucc j i n r x y hj1 hi1 hn0]
  refine firesT_tableInit_of hasRuleAt_tableInitSucc hz (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_constVar rfl) (evalExps_cons hel (evalExps_cons (evalExp_case (evalExp_var rfl))
    (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_jPay rfl) (evalExp_numE_iff.2 rfl)))
    (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_iPay rfl) (evalExp_numE_iff.2 rfl)))
    (evalExps_cons (evalExp_constPE (evalExp_pred hn1 rfl))
    (evalExps_cons (evalExp_case (evalExp_tup2 (evalExp_var rfl) (evalExp_var rfl)))
      evalExps_nil)))))), rfl⟩) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .elsePr (otherwise21T hax htx hay hey hb hn0 _)

/-! ## `elem.drop` and `data.drop` -/

/-- **`Step/elem.drop` in `simEnv20T`** (rule 11 there). -/
theorem firesT_elemDrop {s : Store H} {f : Frame} {x : ElemIdx} {a : Nat} {ei : ElemInst}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.elems[x.toNat]? = some a) (he : s.elems[a]? = some ei) :
    Fires (simEnv20T B) "Step" 11 (.tuple [configV hn ⟨s, f, [.plain (.elemDrop x)]⟩,
      configV hn ⟨s.setElemInst a { ei with refs := [] }, f, []⟩]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("x", idxV x)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  exact firesT_step_of20 (by decide) hasRuleAt_elemDrop rfl σ
    (quantsOkT_z hρ rfl hz (by decide) (QuantsOk.cons rfl (Whole.typedV_idx20 x _ hρ)
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var rfl)
      (evalExp_list1 (evalExp_case (evalExp_var rfl)))))
      (evalExp_case (evalExp_tup2 (evalExp_withElem20 rfl (evalExp_var rfl) (evalExp_var rfl) ha he)
        Pure.evalExp_list0))) (by simp) (D := fun _ _ _ _ => True) (els := True)

/-- **`Step/data.drop` in `simEnv20T`** (rule 22 there). -/
theorem firesT_dataDrop {s : Store H} {f : Frame} {x : DataIdx} {a : Nat} {di : DataInst}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.datas[x.toNat]? = some a) (hd : s.datas[a]? = some di) :
    Fires (simEnv20T B) "Step" 22 (.tuple [configV hn ⟨s, f, [.plain (.dataDrop x)]⟩,
      configV hn ⟨s.setDataInst a ⟨ByteArray.empty⟩, f, []⟩]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("x", idxV x)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  exact firesT_step_of20 (by decide) hasRuleAt_dataDrop rfl σ
    (quantsOkT_z hρ rfl hz (by decide) (QuantsOk.cons rfl (Whole.typedV_idx20 x _ hρ)
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var rfl)
      (evalExp_list1 (evalExp_case (evalExp_var rfl)))))
      (evalExp_case (evalExp_tup2 (evalExp_withData20 rfl (evalExp_var rfl) (evalExp_var rfl) ha hd)
        Pure.evalExp_list0))) (by simp) (D := fun _ _ _ _ => True) (els := True)

end Silmaril.Wasm.SpecTec.Sim20.StoreBulk
