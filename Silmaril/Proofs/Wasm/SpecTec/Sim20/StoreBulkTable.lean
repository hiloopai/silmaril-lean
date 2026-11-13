module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkInit

/-!
# `table.set` and `table.fill` forward in `simEnv20T`

* `table.set` is `Step` 6 (`-trap`) and 7 (`-val`) of the 2.0 script, rules 7 and 8 of
  `simEnv20T`. Round 3 fires them in `simEnv20` from a state typed there
  (`Whole.fires_tableSetTrap`, `fires_tableSetVal`); here they fire in `simEnv20T` from a state
  typed only there (`firesT_tableSetTrap`, `firesT_tableSetVal`), through round 5's
  `StoreFn.firesT_step_of20`.
* `table.fill` is `Step_read` 12–14. `-succ` rewrites to code with `table.set`:
  `firesT_tableFillTrap`, `firesT_tableFillZero` (`otherwise13T`), `firesT_tableFillSucc`
  (`otherwise14T`), as round 5's `memory.fill`.

**Restatement.** `-succ` computes `i + 1` in `i32` in V2 and over the naturals in the script;
`firesT_tableFillSucc` asks for `i + 1 < 2 ^ 32`, which holds when the table has fewer than
`2 ^ 32` entries.
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
open Silmaril.Wasm.SpecTec.Sim20.Whole (fillQs tableFillLhs tableFillSuccRhs tableFillTrapRule
  tableFillZeroRule tableFillSuccRule valE constIE constNE iPay predE tableLenE constPE trapRhs
  evalExp_constIE evalExp_constNE evalExp_trapRhs evalExp_iPay evalExp_addNat20 evalExp_pred
  evalExp_constPE evalExp_tableLen20 cmpValues_gtOp_nat20 hasRuleAt_tableFillTrap
  hasRuleAt_tableFillZero hasRuleAt_tableFillSucc hasRuleAt_tableSetTrap hasRuleAt_tableSetVal
  codes20_four constI_of_lhs constN_of_lhs constI32_inj adminsToV_tableFillSucc
  evalExp_tableSetLhs tableSetScope evalExp_withTable20)
open Silmaril.Wasm.SpecTec.Sim20.StoreFn (firesT_read_of20 firesT_step_of20 hasRuleAtT_read
  readGood evalBack20 quantsOkT_z ifBack readTagsT)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evRule evExp evPrems)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-- A table of the frame's module, from V2's `table?`. -/
theorem table?_some {s : Store H} {f : Frame} {x : TableIdx} {ti : TableInst}
    (h : (⟨s, f⟩ : State H).table? x = some ti) :
    ∃ a, f.module.tables[x.toNat]? = some a ∧ s.tables[a]? = some ti := by
  simp only [State.table?, ModuleInst.tableAddr?, Store.tableInst?, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at h
  exact h

/-! ## `table.set` -/

/-- The quantifiers of `table.set`, typed in `simEnv20T`. -/
theorem quantsOkT_tableSet {s : Store H} {f : Frame} {c : BitVec 32} {r : Ref} {x : TableIdx}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f)) :
    QuantsOk (simEnv20T B) (VarEnv.empty.bindVals (tableSetScope (hn := hn) s f c r x))
      [.expP "z" (.varT "state" []), .expP "i" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]),
        .expP "ref" (.varT "ref" []), .expP "x" (.varT "idx" [])] :=
  have hρ := Pure.valsOnly_bindVals (tableSetScope (hn := hn) s f c r x)
  quantsOkT_z hρ rfl hz (by decide) (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 c _ hρ)
    (QuantsOk.cons rfl (Whole.typedV_ref20 r _ hρ) (QuantsOk.cons rfl (Whole.typedV_idx20 x _ hρ)
      QuantsOk.nil)))

/-- **`Step/table.set-trap` in `simEnv20T`** (rule 7 there). -/
theorem firesT_tableSetTrap {s : Store H} {f : Frame} {x : TableIdx} {c : BitVec 32} {r : Ref}
    {a : Nat} {ti : TableInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.tables[x.toNat]? = some a) (ht : s.tables[a]? = some ti)
    (hge : ti.refs.length ≤ c.toNat) :
    Fires (simEnv20T B) "Step" 7 (.tuple [
      configV hn ⟨s, f, [constI32 c, aref r, .plain (.tableSet x)]⟩, configV hn ⟨s, f, [.trap]⟩]) :=
  firesT_step_of20 (by decide) hasRuleAt_tableSetTrap rfl (tableSetScope (hn := hn) s f c r x)
    (quantsOkT_tableSet hz)
    (evalExp_tup2 (evalExp_tableSetLhs rfl rfl rfl rfl) (evalExp_case (evalExp_tup2
      (evalExp_var rfl) (evalExp_list1 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))))))
    (fun pr hpr => by
      obtain rfl := List.mem_singleton.1 hpr
      exact .ifPr (evalExp_cmpNum (evalExp_iPay rfl) (evalExp_tableLen20 rfl rfl rfl ha ht)
        (by simpa [Num.cmp] using hge)))
    (D := fun _ _ _ _ => True) (els := True)

/-- **`Step/table.set-val` in `simEnv20T`** (rule 8 there). -/
theorem firesT_tableSetVal {s : Store H} {f : Frame} {x : TableIdx} {c : BitVec 32} {r : Ref}
    {a : Nat} {ti : TableInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.tables[x.toNat]? = some a) (ht : s.tables[a]? = some ti)
    (hlt : c.toNat < ti.refs.length) :
    Fires (simEnv20T B) "Step" 8 (.tuple [
      configV hn ⟨s, f, [constI32 c, aref r, .plain (.tableSet x)]⟩,
      configV hn ⟨s.setTableInst a (ti.setRef c.toNat r), f, []⟩]) :=
  firesT_step_of20 (by decide) hasRuleAt_tableSetVal rfl (tableSetScope (hn := hn) s f c r x)
    (quantsOkT_tableSet hz)
    (evalExp_tup2 (evalExp_tableSetLhs rfl rfl rfl rfl) (evalExp_case (evalExp_tup2
      (evalExp_withTable20 rfl (evalExp_var rfl) (evalExp_var rfl) (evalExp_iPay rfl)
        (evalExp_var rfl) ha ht hlt) Pure.evalExp_list0)))
    (fun pr hpr => by
      obtain rfl := List.mem_singleton.1 hpr
      exact .ifPr (evalExp_cmpNum (evalExp_iPay rfl) (evalExp_tableLen20 rfl rfl rfl ha ht)
        (by simpa [Num.cmp] using hlt)))
    (D := fun _ _ _ _ => True) (els := True)

/-! ## `table.fill`: the left-hand side -/

/-- The code of the three rules. -/
abbrev tfillCode (i : BitVec 32) (v : Val) (n : BitVec 32) (x : TableIdx) : List Admin :=
  [constI32 i, v.toAdmin, constI32 n, .plain (.tableFill x)]

/-- The scope of the three rules. -/
abbrev tableFillScope (s : Store H) (f : Frame) (i : BitVec 32) (v : Val) (n : BitVec 32)
    (x : TableIdx) : List (IL.Id × Value) :=
  [("z", stateV hn s f), ("i", pctV i.toNat), ("val", valV v), ("n", .num (.natN n.toNat)),
    ("x", idxV x)]

/-- The left-hand side, evaluated in `simEnv20`. -/
theorem evalExp_tableFillLhs {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val}
    {x : TableIdx} :
    EvalExp (E20 B) (VarEnv.empty.bindVals (tableFillScope (hn := hn) s f i v n x)) tableFillLhs
      (configV hn ⟨s, f, tfillCode i v n x⟩) := by
  have hv : EvalExp (E20 B) (VarEnv.empty.bindVals (tableFillScope (hn := hn) s f i v n x)) valE
      (adminToV v.toAdmin) := by
    rw [Pure.adminToV_toAdmin]
    exact evalExp_subE_iff.2 (evalExp_var rfl)
  exact evalExp_case (evalExp_tup2 (evalExp_var rfl) (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_constIE rfl) (evalExps_cons hv (evalExps_cons (evalExp_constNE rfl)
      (evalExps_cons (evalExp_case (evalExp_var rfl)) evalExps_nil))), rfl⟩))

/-- The quantifiers, typed in `simEnv20T`. -/
theorem quantsOkT_tableFill {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val} {x : TableIdx}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f)) :
    QuantsOk (simEnv20T B) (VarEnv.empty.bindVals (tableFillScope (hn := hn) s f i v n x))
      fillQs :=
  have hρ := Pure.valsOnly_bindVals (tableFillScope (hn := hn) s f i v n x)
  quantsOkT_z hρ rfl hz (by decide) (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
    (QuantsOk.cons rfl (Whole.typedV_val20 v _ hρ)
      (QuantsOk.cons rfl (Whole.typedV_n20 _ _ hρ)
        (QuantsOk.cons rfl (Whole.typedV_idx20 x _ hρ) QuantsOk.nil))))

/-- The tags of a `table.fill` left-hand side. -/
theorem lhsIn_tfillCode (s : Store H) (f : Frame) (i n : BitVec 32) (v : Val) (x : TableIdx) :
    LhsIn ["CONST", "VCONST", "REF.NULL", "REF.FUNC_ADDR", "REF.HOST_ADDR", "TABLE.FILL"]
      (configV hn ⟨s, f, tfillCode i v n x⟩) := by
  refine Or.inr ⟨_, _, rfl, ?_⟩
  intro u hu op w hw
  simp only [adminsToV, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · rw [← Whole.adminToV_case20 hw]; simp [Whole.adminHead20, Whole.instrHead20]
  · rw [← Whole.adminToV_case20 hw]
    rcases v with ⟨⟨_ | _⟩, _⟩ | _ | (_ | _ | _) <;>
      simp [Val.toAdmin, Whole.adminHead20, Whole.instrHead20]
  · rw [← Whole.adminToV_case20 hw]; simp [Whole.adminHead20, Whole.instrHead20]
  · rw [← Whole.adminToV_case20 hw]; simp [Whole.adminHead20, Whole.instrHead20]

/-! ## Rule bodies in `simEnv20T`, read back -/

/-- A `table.fill` rule body in `simEnv20T` at a `table.fill` left-hand side binds the state
and the operands, and its premises hold in `simEnv20T`. -/
theorem tableFillBodyT_parts {D : Sim.Interp} {els : Prop} {nm : IL.Id} {rhs : Exp}
    {prems : List Prem} {k : Nat}
    (hR : HasRuleAt (E20 B) "Step_read" "%~>%" k
      (.ruleD nm fillQs "%~>%" (.tupE [tableFillLhs, rhs]) prems))
    {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val} {x : TableIdx} {w : Value}
    (hbody : RuleBody (simEnv20T B) D els [] [] "%~>%"
      (.ruleD nm fillQs "%~>%" (.tupE [tableFillLhs, rhs]) prems)
      (.tuple [configV hn ⟨s, f, tfillCode i v n x⟩, w])) :
    ∃ ρ : VarEnv, ValsOnly ρ ∧ ρ.findVal? "z" = some (stateV hn s f) ∧
      ρ.findVal? "i" = some (pctV i.toNat) ∧ ρ.findVal? "n" = some (.num (.natN n.toNat)) ∧
      ρ.findVal? "x" = some (idxV x) ∧ ρ.findDef? "table" = none ∧
      RelFree.GoodEvs RelFree.bad20 (evPrems prems) ∧
      ∀ pr ∈ prems, PremW (simEnv20T B) D els ρ pr := by
  obtain ⟨-, ρ₀, σ, hps, -, he, hp⟩ := hbody
  obtain rfl : ρ₀ = VarEnv.empty := (Option.some.inj hps).symm
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have hG' : (RelFree.GoodEvs RelFree.bad20 (Sim.Round7.Script.evParams fillQs) ∧
      RelFree.GoodEvs RelFree.bad20 (evExp (.tupE [tableFillLhs, rhs]))) ∧
      RelFree.GoodEvs RelFree.bad20 (evPrems prems) := by
    simpa only [evRule, RelFree.goodEvs_append] using RelFree.goodEvs_of_all (readGood hR)
  have hl : EvalExp (E20 B) (VarEnv.empty.bindVals σ) tableFillLhs
      (configV hn ⟨s, f, tfillCode i v n x⟩) :=
    Sim.RefsGC.lhs_of_concl (evalBack20 hρ hG'.1.2 he)
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 hl
  have hu' : u = .tuple [stateV hn s f, .list (adminsToV (tfillCode i v n x))] :=
    (Value.case.inj hcu.symm).2
  obtain ⟨hZ, hL⟩ := Pure.evalExp_tup2_inv (hu' ▸ hu)
  obtain ⟨a₁, a₂, a₃, a₄, he4, h₁, -, h₃, h₄⟩ := codes20_four (Sim.RefsGC.elems_of_list hL)
  obtain ⟨rfl, -, rfl, rfl⟩ : constI32 i = a₁ ∧ v.toAdmin = a₂ ∧ constI32 n = a₃ ∧
      Admin.plain (.tableFill x) = a₄ := by simpa using he4
  obtain ⟨i', hi', fi⟩ := constI_of_lhs h₁
  obtain ⟨n', hn', fn⟩ := constN_of_lhs h₃
  obtain rfl := constI32_inj hi'
  obtain rfl := constI32_inj hn'
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) :=
    Whole.idx_of_caseE (X := idxV x) h₄ rfl
  exact ⟨_, hρ, evalExp_varE_iff.1 hZ, fi, fn, fx, rfl, hG'.2, hp⟩

/-- **Rule 12's body is refuted in `simEnv20T`** where the fill is in bounds. -/
theorem not_tableFillTrapBodyT {D : Sim.Interp} {els : Prop} {s : Store H} {f : Frame}
    {i n : BitVec 32} {v : Val} {x : TableIdx} {a : Nat} {ti : TableInst}
    (ha : f.module.tables[x.toNat]? = some a) (ht : s.tables[a]? = some ti)
    (hb : i.toNat + n.toNat ≤ ti.refs.length) (w : Value) :
    ¬ RuleBody (simEnv20T B) D els [] [] "%~>%" tableFillTrapRule
      (.tuple [configV hn ⟨s, f, tfillCode i v n x⟩, w]) := by
  intro hbody
  obtain ⟨ρ, hρ, fz, fi, fn, fx, hd, hG, hp⟩ := tableFillBodyT_parts hasRuleAt_tableFillTrap hbody
  have hpr := ifBack hρ hG hp (List.mem_singleton_self _)
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 hpr
  rw [EvalExp.unique e₁ (evalExp_addNat20 (evalExp_iPay fi) (evalExp_var fn)),
    EvalExp.unique e₂ (evalExp_tableLen20 hd fz fx ha ht)] at hcmp
  simp [cmpValues, Num.cmp, Res.ofOption] at hcmp
  omega

/-- **Rule 13's body is refuted in `simEnv20T`** at a nonzero count. -/
theorem not_tableFillZeroBodyT {D : Sim.Interp} {els : Prop} {s : Store H} {f : Frame}
    {i n : BitVec 32} {v : Val} {x : TableIdx} (hn0 : n ≠ 0) (w : Value) :
    ¬ RuleBody (simEnv20T B) D els [] [] "%~>%" tableFillZeroRule
      (.tuple [configV hn ⟨s, f, tfillCode i v n x⟩, w]) := by
  intro hbody
  obtain ⟨ρ, hρ, -, -, fn, -, -, hG, hp⟩ := tableFillBodyT_parts hasRuleAt_tableFillZero hbody
  exact hn0 (Whole.zero_of_prem fn
    (ifBack hρ hG hp (List.mem_cons_of_mem _ (List.mem_singleton_self _))))

/-! ## `otherwise` in `simEnv20T` -/

/-- **`otherwise` for rule 13 in `simEnv20T`**, where the fill is in bounds. -/
theorem otherwise13T {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val} {x : TableIdx}
    {a : Nat} {ti : TableInst} (ha : f.module.tables[x.toNat]? = some a)
    (ht : s.tables[a]? = some ti) (hb : i.toNat + n.toNat ≤ ti.refs.length) (w : Value) :
    otherwiseAt (simEnv20T B) "Step_read" [] 13
      (.tuple [configV hn ⟨s, f, tfillCode i v n x⟩, w]) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAtT_read (hasRuleAt_tableFillTrap (B := B))
  refine otherwiseAt_of_table hrel (tags_of_take hrel readTagsT) (by decide)
    (lhsIn_tfillCode s f i n v x) (exc := [12]) (by decide) ?_
  intro k hk _ r hr w' hw
  obtain ⟨c', rfl⟩ := Whole.sameLhs_inv hw
  obtain rfl := List.mem_singleton.1 hk
  rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_tableFillTrap) hr]
  exact not_tableFillTrapBodyT ha ht hb c'

/-- **`otherwise` for rule 14 in `simEnv20T`**, where the fill is in bounds and `n ≠ 0`. -/
theorem otherwise14T {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val} {x : TableIdx}
    {a : Nat} {ti : TableInst} (ha : f.module.tables[x.toNat]? = some a)
    (ht : s.tables[a]? = some ti) (hb : i.toNat + n.toNat ≤ ti.refs.length) (hn0 : n ≠ 0)
    (w : Value) :
    otherwiseAt (simEnv20T B) "Step_read" [] 14
      (.tuple [configV hn ⟨s, f, tfillCode i v n x⟩, w]) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAtT_read (hasRuleAt_tableFillTrap (B := B))
  refine otherwiseAt_of_table hrel (tags_of_take hrel readTagsT) (by decide)
    (lhsIn_tfillCode s f i n v x) (exc := [12, 13]) (by decide) ?_
  intro k hk _ r hr w' hw
  obtain ⟨c', rfl⟩ := Whole.sameLhs_inv hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_tableFillTrap) hr]
    exact not_tableFillTrapBodyT ha ht hb c'
  · rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_tableFillZero) hr]
    exact not_tableFillZeroBodyT hn0 c'

/-! ## The three rules fire -/

/-- A `table.fill` rule fires in `simEnv20T` from its right-hand side evaluated in `simEnv20`
and its premises in `simEnv20T`. -/
theorem firesT_tableFill_of {k : Nat} {nm : IL.Id} {rhs : Exp} {prems : List Prem}
    (hR : HasRuleAt (E20 B) "Step_read" "%~>%" k
      (.ruleD nm fillQs "%~>%" (.tupE [tableFillLhs, rhs]) prems))
    {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val} {x : TableIdx} {W : Value}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (hr : EvalExp (E20 B) (VarEnv.empty.bindVals (tableFillScope (hn := hn) s f i v n x)) rhs W)
    (hp : ∀ pr ∈ prems, PremW (simEnv20T B) (Sim.DDerives (simEnv20T B) (Sim.otherwise (simEnv20T B)))
      (Sim.otherwise (simEnv20T B) "Step_read" [] k
        (.tuple [configV hn ⟨s, f, tfillCode i v n x⟩, W]))
      (VarEnv.empty.bindVals (tableFillScope (hn := hn) s f i v n x)) pr) :
    Fires (simEnv20T B) "Step_read" k (.tuple [configV hn ⟨s, f, tfillCode i v n x⟩, W]) := by
  have hρ := Pure.valsOnly_bindVals (tableFillScope (hn := hn) s f i v n x)
  have hGe : RelFree.GoodEvs RelFree.bad20 (evExp (.tupE [tableFillLhs, rhs])) := by
    have hG := RelFree.goodEvs_of_all (readGood hR)
    simp only [evRule, RelFree.goodEvs_append] at hG
    exact hG.1.2
  exact Pure.fires_of_ruleAt (hasRuleAtT_read hR) _ (quantsOkT_tableFill hz)
    (StoreDeep.evalT_of_20 hρ hGe (evalExp_tup2 evalExp_tableFillLhs hr)) hp

/-- **`Step_read/table.fill-trap` in `simEnv20T`.** -/
theorem firesT_tableFillTrap {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val} {x : TableIdx}
    {a : Nat} {ti : TableInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.tables[x.toNat]? = some a) (ht : s.tables[a]? = some ti)
    (hlt : ti.refs.length < i.toNat + n.toNat) :
    Fires (simEnv20T B) "Step_read" 12
      (.tuple [configV hn ⟨s, f, tfillCode i v n x⟩, .list (adminsToV [.trap])]) := by
  refine firesT_read_of20 (D := fun _ _ _ _ => True) (els := True) hasRuleAt_tableFillTrap rfl
    (tableFillScope (hn := hn) s f i v n x) (quantsOkT_tableFill hz)
    (evalExp_tup2 evalExp_tableFillLhs evalExp_trapRhs) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_addNat20 (evalExp_iPay rfl) (evalExp_var rfl),
    evalExp_tableLen20 rfl rfl rfl ha ht, cmpValues_gtOp_nat20 hlt⟩)

/-- **`Step_read/table.fill-zero` in `simEnv20T`.** -/
theorem firesT_tableFillZero {s : Store H} {f : Frame} {i : BitVec 32} {v : Val} {x : TableIdx}
    {a : Nat} {ti : TableInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.tables[x.toNat]? = some a) (ht : s.tables[a]? = some ti)
    (hb : i.toNat ≤ ti.refs.length) :
    Fires (simEnv20T B) "Step_read" 13
      (.tuple [configV hn ⟨s, f, tfillCode i v 0 x⟩, .list (adminsToV [])]) := by
  refine firesT_tableFill_of hasRuleAt_tableFillZero hz Pure.evalExp_list0 ?_
  intro pr hpr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
  rcases hpr with rfl | rfl
  · exact .elsePr (otherwise13T ha ht (by simpa using hb) _)
  · refine .ifPr (StoreDeep.evalT_of_20 (Pure.valsOnly_bindVals _)
      (RelFree.goodEvs_of_all (by decide)) ?_)
    exact evalExp_cmpE_iff.2 ⟨_, _, evalExp_var rfl, evalExp_numE_iff.2 rfl,
      cmpValues_eq_true_iff.2 rfl⟩

/-- **`Step_read/table.fill-succ` in `simEnv20T`**, where `i + 1` does not wrap. -/
theorem firesT_tableFillSucc {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val} {x : TableIdx}
    {a : Nat} {ti : TableInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.tables[x.toNat]? = some a) (ht : s.tables[a]? = some ti)
    (hb : i.toNat + n.toNat ≤ ti.refs.length) (hn0 : n ≠ 0) (hi1 : i.toNat + 1 < 2 ^ 32) :
    Fires (simEnv20T B) "Step_read" 14 (.tuple [configV hn ⟨s, f, tfillCode i v n x⟩,
      .list (adminsToV [constI32 i, v.toAdmin, .plain (.tableSet x), constI32 (i + 1), v.toAdmin,
        constI32 (n - 1), .plain (.tableFill x)])]) := by
  have hn1 : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
  have hv : EvalExp (E20 B) (VarEnv.empty.bindVals (tableFillScope (hn := hn) s f i v n x)) valE
      (valV v) := evalExp_subE_iff.2 (evalExp_var rfl)
  rw [adminsToV_tableFillSucc i n v x hi1 hn0]
  refine firesT_tableFill_of hasRuleAt_tableFillSucc hz (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
      (evalExp_var rfl))) (evalExps_cons hv (evalExps_cons (evalExp_case (evalExp_var rfl))
    (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_iPay rfl) (evalExp_numE_iff.2 rfl)))
    (evalExps_cons hv (evalExps_cons (evalExp_constPE (evalExp_pred hn1 rfl))
    (evalExps_cons (evalExp_case (evalExp_var rfl)) evalExps_nil)))))), rfl⟩) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .elsePr (otherwise14T ha ht hb hn0 _)

end Silmaril.Wasm.SpecTec.Sim20.StoreBulk
