module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkTable

/-!
# `table.copy` forward in `simEnv20T`

`Step_read` 15–18 of the 2.0 script are `table.copy-trap`, `-zero`, `-le` and `-gt`. The `-le`
and `-gt` successors hold `table.get y` and `table.set x`; the rules are fired in `simEnv20T`
from a state typed there:

* `firesT_tableCopyTrap` (15);
* `firesT_tableCopyZero` (16, `-- otherwise`): rule 15's body is refuted where both bounds hold
  (`otherwise16T`);
* `firesT_tableCopyLe` (17, `-- otherwise`): rules 15 and 16 are refuted (`otherwise17T`);
* `firesT_tableCopyGt` (18, `-- otherwise`): rules 15–17 are refuted (`otherwise18T`); rule 17's
  body is refuted through its `if j ≤ i` premise, without its own `otherwise`.

Each body is read back by moving its evaluations from `simEnv20T` to `simEnv20`
(`tableCopyBodyT_parts`, through `StoreFn.evalBack20`), as for `memory.copy`.

**Restatements.** V2 computes `j + 1`, `i + 1` (`-le`) and `j + n - 1`, `i + n - 1` (`-gt`) in
`i32`; the script computes them over the naturals. The firing lemmas ask for these sums below
`2 ^ 32`; all hold when both tables have fewer than `2 ^ 32` entries, since the bounds give
`i + n ≤ |y|` and `j + n ≤ |x|`.
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
  evalExp_tup2 evalExp_case)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (otherwiseAt_of_table tags_of_take)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Whole (copyQs tableCopyLhs tableCopyE tableCopyTrapRule
  tableCopyZeroRule tableCopyLeRule tableCopyGtRule tableLenYE tableLenE constJE constIE constNE
  jPay iPay predE constSuccE constPE sumPredE trapRhs evalExp_constIE evalExp_constNE
  evalExp_trapRhs evalExp_iPay evalExp_jPay evalExp_addNat20 evalExp_tableLen20
  evalExp_tableLenVar20 evalExp_constVar evalExp_constPE evalExp_pred evalExp_sumPred
  evalExp_gtNat hasRuleAt_tableCopyTrap hasRuleAt_tableCopyZero hasRuleAt_tableCopyLe
  hasRuleAt_tableCopyGt CopyScope copyScope_of zero_of_prem le_of_prem not_or_true
  lhsIn_tableCopy adminsToV_tableCopyLe adminsToV_tableCopyGt)
open Silmaril.Wasm.SpecTec.Sim20.StoreFn (firesT_read_of20 hasRuleAtT_read readGood evalBack20
  quantsOkT_z ifBack readTagsT)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evRule evExp evPrems)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-! ## The left-hand side -/

/-- The code of the four rules. -/
abbrev tcopyCode (j i n : BitVec 32) (x y : TableIdx) : List Admin :=
  [constI32 j, constI32 i, constI32 n, .plain (.tableCopy x y)]

/-- The scope of the four rules. -/
abbrev tableCopyScope (s : Store H) (f : Frame) (j i n : BitVec 32) (x y : TableIdx) :
    List (IL.Id × Value) :=
  [("z", stateV hn s f), ("j", pctV j.toNat), ("i", pctV i.toNat), ("n", .num (.natN n.toNat)),
    ("x", idxV x), ("y", idxV y)]

/-- The left-hand side, evaluated in `simEnv20`. -/
theorem evalExp_tableCopyLhs {s : Store H} {f : Frame} {j i n : BitVec 32} {x y : TableIdx} :
    EvalExp (E20 B) (VarEnv.empty.bindVals (tableCopyScope (hn := hn) s f j i n x y)) tableCopyLhs
      (configV hn ⟨s, f, tcopyCode j i n x y⟩) :=
  evalExp_case (evalExp_tup2 (evalExp_var rfl) (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_constJE rfl) (evalExps_cons (evalExp_constIE rfl) (evalExps_cons (evalExp_constNE rfl)
      (evalExps_cons (evalExp_case (evalExp_tup2 (evalExp_var rfl) (evalExp_var rfl)))
        evalExps_nil))), rfl⟩))

/-- The quantifiers, typed in `simEnv20T`. -/
theorem quantsOkT_tableCopy {s : Store H} {f : Frame} {j i n : BitVec 32} {x y : TableIdx}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f)) :
    QuantsOk (simEnv20T B) (VarEnv.empty.bindVals (tableCopyScope (hn := hn) s f j i n x y))
      copyQs :=
  have hρ := Pure.valsOnly_bindVals (tableCopyScope (hn := hn) s f j i n x y)
  quantsOkT_z hρ rfl hz (by decide) (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 j _ hρ)
    (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons rfl (Whole.typedV_n20 _ _ hρ)
        (QuantsOk.cons rfl (Whole.typedV_idx20 x _ hρ)
          (QuantsOk.cons rfl (Whole.typedV_idx20 y _ hρ) QuantsOk.nil)))))

/-! ## Rule bodies in `simEnv20T`, read back -/

/-- A `table.copy` rule body in `simEnv20T` at a `table.copy` left-hand side binds the state and
the operands, and its premises hold in `simEnv20T`. -/
theorem tableCopyBodyT_parts {D : Sim.Interp} {els : Prop} {nm : IL.Id} {rhs : Exp}
    {prems : List Prem} {k : Nat}
    (hR : HasRuleAt (E20 B) "Step_read" "%~>%" k
      (.ruleD nm copyQs "%~>%" (.tupE [tableCopyLhs, rhs]) prems))
    {s : Store H} {f : Frame} {j i n : BitVec 32} {x y : TableIdx} {w : Value}
    (hbody : RuleBody (simEnv20T B) D els [] [] "%~>%"
      (.ruleD nm copyQs "%~>%" (.tupE [tableCopyLhs, rhs]) prems)
      (.tuple [configV hn ⟨s, f, tcopyCode j i n x y⟩, w])) :
    ∃ σ : List (IL.Id × Value), (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) ∧
      CopyScope σ j i n x y ∧ RelFree.GoodEvs RelFree.bad20 (evPrems prems) ∧
      ∀ pr ∈ prems, PremW (simEnv20T B) D els (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨-, ρ₀, σ, hps, -, he, hp⟩ := hbody
  obtain rfl : ρ₀ = VarEnv.empty := (Option.some.inj hps).symm
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have hG' : (RelFree.GoodEvs RelFree.bad20 (Sim.Round7.Script.evParams copyQs) ∧
      RelFree.GoodEvs RelFree.bad20 (evExp (.tupE [tableCopyLhs, rhs]))) ∧
      RelFree.GoodEvs RelFree.bad20 (evPrems prems) := by
    simpa only [evRule, RelFree.goodEvs_append] using RelFree.goodEvs_of_all (readGood hR)
  have hl := Sim.RefsGC.lhs_of_concl (evalBack20 hρ hG'.1.2 he)
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 hl
  have hu' : u = .tuple [stateV hn s f, .list (adminsToV (tcopyCode j i n x y))] :=
    (Value.case.inj hcu.symm).2
  obtain ⟨hZ, hL⟩ := Pure.evalExp_tup2_inv (hu' ▸ hu)
  exact ⟨σ, evalExp_varE_iff.1 hZ, copyScope_of (Sim.RefsGC.elems_of_list hL), hG'.2, hp⟩

/-- **Rule 15's body is refuted in `simEnv20T`** where both bounds hold. -/
theorem not_tableCopyTrapBodyT {D : Sim.Interp} {els : Prop} {s : Store H} {f : Frame}
    {j i n : BitVec 32} {x y : TableIdx} {ax ay : Nat} {tx ty : TableInst}
    (hax : f.module.tables[x.toNat]? = some ax) (htx : s.tables[ax]? = some tx)
    (hay : f.module.tables[y.toNat]? = some ay) (hty : s.tables[ay]? = some ty)
    (hb : i.toNat + n.toNat ≤ ty.refs.length ∧ j.toNat + n.toNat ≤ tx.refs.length) (w : Value) :
    ¬ RuleBody (simEnv20T B) D els [] [] "%~>%" tableCopyTrapRule
      (.tuple [configV hn ⟨s, f, tcopyCode j i n x y⟩, w]) := by
  intro hbody
  obtain ⟨σ, fz, S, hG, hp⟩ := tableCopyBodyT_parts hasRuleAt_tableCopyTrap hbody
  have hpr := ifBack (Pure.valsOnly_bindVals σ) hG hp (List.mem_singleton_self _)
  have h₁ : EvalExp (E20 B) (VarEnv.empty.bindVals σ) (.cmpE .gtOp (.numT .natT)
      (.binE .addOp (.numT .natT) iPay (.varE "n")) tableLenYE) (.bool false) := by
    have h := evalExp_gtNat (evalExp_addNat20 (evalExp_iPay S.fi) (evalExp_var S.fn))
      (evalExp_tableLenVar20 (B := B) rfl fz S.fy hay hty)
    rwa [show decide (ty.refs.length < i.toNat + n.toNat) = false by simp; omega] at h
  have h₂ : EvalExp (E20 B) (VarEnv.empty.bindVals σ) (.cmpE .gtOp (.numT .natT)
      (.binE .addOp (.numT .natT) jPay (.varE "n")) tableLenE) (.bool false) := by
    have h := evalExp_gtNat (evalExp_addNat20 (evalExp_jPay S.fj) (evalExp_var S.fn))
      (evalExp_tableLen20 (B := B) rfl fz S.fx hax htx)
    rwa [show decide (tx.refs.length < j.toNat + n.toNat) = false by simp; omega] at h
  exact not_or_true h₁ h₂ hpr

/-- **Rule 16's body is refuted in `simEnv20T`** at a nonzero count. -/
theorem not_tableCopyZeroBodyT {D : Sim.Interp} {els : Prop} {s : Store H} {f : Frame}
    {j i n : BitVec 32} {x y : TableIdx} (hn0 : n ≠ 0) (w : Value) :
    ¬ RuleBody (simEnv20T B) D els [] [] "%~>%" tableCopyZeroRule
      (.tuple [configV hn ⟨s, f, tcopyCode j i n x y⟩, w]) := by
  intro hbody
  obtain ⟨σ, -, S, hG, hp⟩ := tableCopyBodyT_parts hasRuleAt_tableCopyZero hbody
  exact hn0 (zero_of_prem S.fn (ifBack (Pure.valsOnly_bindVals σ) hG hp
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))))

/-- **Rule 17's body is refuted in `simEnv20T`** where `i < j`: its `if j ≤ i` fails. -/
theorem not_tableCopyLeBodyT {D : Sim.Interp} {els : Prop} {s : Store H} {f : Frame}
    {j i n : BitVec 32} {x y : TableIdx} (hgt : i.toNat < j.toNat) (w : Value) :
    ¬ RuleBody (simEnv20T B) D els [] [] "%~>%" tableCopyLeRule
      (.tuple [configV hn ⟨s, f, tcopyCode j i n x y⟩, w]) := by
  intro hbody
  obtain ⟨σ, -, S, hG, hp⟩ := tableCopyBodyT_parts hasRuleAt_tableCopyLe hbody
  have hle := le_of_prem S.fj S.fi (ifBack (Pure.valsOnly_bindVals σ) hG hp
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  omega

/-! ## `otherwise` in `simEnv20T` -/

/-- **`otherwise` for rule 16 in `simEnv20T`**, where both bounds hold. -/
theorem otherwise16T {s : Store H} {f : Frame} {j i n : BitVec 32} {x y : TableIdx}
    {ax ay : Nat} {tx ty : TableInst}
    (hax : f.module.tables[x.toNat]? = some ax) (htx : s.tables[ax]? = some tx)
    (hay : f.module.tables[y.toNat]? = some ay) (hty : s.tables[ay]? = some ty)
    (hb : i.toNat + n.toNat ≤ ty.refs.length ∧ j.toNat + n.toNat ≤ tx.refs.length) (w : Value) :
    otherwiseAt (simEnv20T B) "Step_read" [] 16
      (.tuple [configV hn ⟨s, f, tcopyCode j i n x y⟩, w]) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAtT_read (hasRuleAt_tableCopyTrap (B := B))
  refine otherwiseAt_of_table hrel (tags_of_take hrel readTagsT) (by decide)
    (lhsIn_tableCopy s f j i n x y) (exc := [15]) (by decide) ?_
  intro k hk _ r hr w' hw
  obtain ⟨c', rfl⟩ := Whole.sameLhs_inv hw
  obtain rfl := List.mem_singleton.1 hk
  rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_tableCopyTrap) hr]
  exact not_tableCopyTrapBodyT hax htx hay hty hb c'

/-- **`otherwise` for rule 17 in `simEnv20T`**, where both bounds hold and `n ≠ 0`. -/
theorem otherwise17T {s : Store H} {f : Frame} {j i n : BitVec 32} {x y : TableIdx}
    {ax ay : Nat} {tx ty : TableInst}
    (hax : f.module.tables[x.toNat]? = some ax) (htx : s.tables[ax]? = some tx)
    (hay : f.module.tables[y.toNat]? = some ay) (hty : s.tables[ay]? = some ty)
    (hb : i.toNat + n.toNat ≤ ty.refs.length ∧ j.toNat + n.toNat ≤ tx.refs.length) (hn0 : n ≠ 0)
    (w : Value) :
    otherwiseAt (simEnv20T B) "Step_read" [] 17
      (.tuple [configV hn ⟨s, f, tcopyCode j i n x y⟩, w]) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAtT_read (hasRuleAt_tableCopyTrap (B := B))
  refine otherwiseAt_of_table hrel (tags_of_take hrel readTagsT) (by decide)
    (lhsIn_tableCopy s f j i n x y) (exc := [15, 16]) (by decide) ?_
  intro k hk _ r hr w' hw
  obtain ⟨c', rfl⟩ := Whole.sameLhs_inv hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_tableCopyTrap) hr]
    exact not_tableCopyTrapBodyT hax htx hay hty hb c'
  · rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_tableCopyZero) hr]
    exact not_tableCopyZeroBodyT hn0 c'

/-- **`otherwise` for rule 18 in `simEnv20T`**, where both bounds hold, `n ≠ 0` and `i < j`. -/
theorem otherwise18T {s : Store H} {f : Frame} {j i n : BitVec 32} {x y : TableIdx}
    {ax ay : Nat} {tx ty : TableInst}
    (hax : f.module.tables[x.toNat]? = some ax) (htx : s.tables[ax]? = some tx)
    (hay : f.module.tables[y.toNat]? = some ay) (hty : s.tables[ay]? = some ty)
    (hb : i.toNat + n.toNat ≤ ty.refs.length ∧ j.toNat + n.toNat ≤ tx.refs.length) (hn0 : n ≠ 0)
    (hgt : i.toNat < j.toNat) (w : Value) :
    otherwiseAt (simEnv20T B) "Step_read" [] 18
      (.tuple [configV hn ⟨s, f, tcopyCode j i n x y⟩, w]) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAtT_read (hasRuleAt_tableCopyTrap (B := B))
  refine otherwiseAt_of_table hrel (tags_of_take hrel readTagsT) (by decide)
    (lhsIn_tableCopy s f j i n x y) (exc := [15, 16, 17]) (by decide) ?_
  intro k hk _ r hr w' hw
  obtain ⟨c', rfl⟩ := Whole.sameLhs_inv hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_tableCopyTrap) hr]
    exact not_tableCopyTrapBodyT hax htx hay hty hb c'
  · rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_tableCopyZero) hr]
    exact not_tableCopyZeroBodyT hn0 c'
  · rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_tableCopyLe) hr]
    exact not_tableCopyLeBodyT hgt c'

/-! ## The four rules fire -/

/-- A `table.copy` rule fires in `simEnv20T` from its right-hand side evaluated in `simEnv20`
and its premises in `simEnv20T`. -/
theorem firesT_tableCopy_of {k : Nat} {nm : IL.Id} {rhs : Exp} {prems : List Prem}
    (hR : HasRuleAt (E20 B) "Step_read" "%~>%" k
      (.ruleD nm copyQs "%~>%" (.tupE [tableCopyLhs, rhs]) prems))
    {s : Store H} {f : Frame} {j i n : BitVec 32} {x y : TableIdx} {W : Value}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (hr : EvalExp (E20 B) (VarEnv.empty.bindVals (tableCopyScope (hn := hn) s f j i n x y)) rhs W)
    (hp : ∀ pr ∈ prems, PremW (simEnv20T B) (Sim.DDerives (simEnv20T B) (Sim.otherwise (simEnv20T B)))
      (Sim.otherwise (simEnv20T B) "Step_read" [] k
        (.tuple [configV hn ⟨s, f, tcopyCode j i n x y⟩, W]))
      (VarEnv.empty.bindVals (tableCopyScope (hn := hn) s f j i n x y)) pr) :
    Fires (simEnv20T B) "Step_read" k (.tuple [configV hn ⟨s, f, tcopyCode j i n x y⟩, W]) := by
  have hρ := Pure.valsOnly_bindVals (tableCopyScope (hn := hn) s f j i n x y)
  have hGe : RelFree.GoodEvs RelFree.bad20 (evExp (.tupE [tableCopyLhs, rhs])) := by
    have hG := RelFree.goodEvs_of_all (readGood hR)
    simp only [evRule, RelFree.goodEvs_append] at hG
    exact hG.1.2
  exact Pure.fires_of_ruleAt (hasRuleAtT_read hR) _ (quantsOkT_tableCopy hz)
    (StoreDeep.evalT_of_20 hρ hGe (evalExp_tup2 evalExp_tableCopyLhs hr)) hp

/-- **`Step_read/table.copy-trap` in `simEnv20T`.** -/
theorem firesT_tableCopyTrap {s : Store H} {f : Frame} {j i n : BitVec 32} {x y : TableIdx}
    {ax ay : Nat} {tx ty : TableInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (hax : f.module.tables[x.toNat]? = some ax) (htx : s.tables[ax]? = some tx)
    (hay : f.module.tables[y.toNat]? = some ay) (hty : s.tables[ay]? = some ty)
    (hlt : ty.refs.length < i.toNat + n.toNat ∨ tx.refs.length < j.toNat + n.toNat) :
    Fires (simEnv20T B) "Step_read" 15
      (.tuple [configV hn ⟨s, f, tcopyCode j i n x y⟩, .list (adminsToV [.trap])]) := by
  refine firesT_read_of20 (D := fun _ _ _ _ => True) (els := True) hasRuleAt_tableCopyTrap rfl
    (tableCopyScope (hn := hn) s f j i n x y) (quantsOkT_tableCopy hz)
    (evalExp_tup2 evalExp_tableCopyLhs evalExp_trapRhs) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (Whole.evalExp_or
    (evalExp_gtNat (evalExp_addNat20 (evalExp_iPay rfl) (evalExp_var rfl))
      (evalExp_tableLenVar20 rfl rfl rfl hay hty))
    (evalExp_gtNat (evalExp_addNat20 (evalExp_jPay rfl) (evalExp_var rfl))
      (evalExp_tableLen20 rfl rfl rfl hax htx))
    (by simpa using hlt))

/-- **`Step_read/table.copy-zero` in `simEnv20T`.** -/
theorem firesT_tableCopyZero {s : Store H} {f : Frame} {j i : BitVec 32} {x y : TableIdx}
    {ax ay : Nat} {tx ty : TableInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (hax : f.module.tables[x.toNat]? = some ax) (htx : s.tables[ax]? = some tx)
    (hay : f.module.tables[y.toNat]? = some ay) (hty : s.tables[ay]? = some ty)
    (hb : i.toNat ≤ ty.refs.length ∧ j.toNat ≤ tx.refs.length) :
    Fires (simEnv20T B) "Step_read" 16
      (.tuple [configV hn ⟨s, f, tcopyCode j i 0 x y⟩, .list (adminsToV [])]) := by
  refine firesT_tableCopy_of hasRuleAt_tableCopyZero hz Pure.evalExp_list0 ?_
  intro pr hpr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
  rcases hpr with rfl | rfl
  · exact .elsePr (otherwise16T hax htx hay hty (by simpa using hb) _)
  · refine .ifPr (StoreDeep.evalT_of_20 (Pure.valsOnly_bindVals _)
      (RelFree.goodEvs_of_all (by decide)) ?_)
    exact evalExp_cmpE_iff.2 ⟨_, _, evalExp_var rfl, evalExp_numE_iff.2 rfl,
      cmpValues_eq_true_iff.2 rfl⟩

/-- **`Step_read/table.copy-le` in `simEnv20T`**, where `j + 1` and `i + 1` do not wrap. -/
theorem firesT_tableCopyLe {s : Store H} {f : Frame} {j i n : BitVec 32} {x y : TableIdx}
    {ax ay : Nat} {tx ty : TableInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (hax : f.module.tables[x.toNat]? = some ax) (htx : s.tables[ax]? = some tx)
    (hay : f.module.tables[y.toNat]? = some ay) (hty : s.tables[ay]? = some ty)
    (hb : i.toNat + n.toNat ≤ ty.refs.length ∧ j.toNat + n.toNat ≤ tx.refs.length) (hn0 : n ≠ 0)
    (hle : j.toNat ≤ i.toNat) (hj1 : j.toNat + 1 < 2 ^ 32) (hi1 : i.toNat + 1 < 2 ^ 32) :
    Fires (simEnv20T B) "Step_read" 17 (.tuple [configV hn ⟨s, f, tcopyCode j i n x y⟩,
      .list (adminsToV [constI32 j, constI32 i, .plain (.tableGet y), .plain (.tableSet x),
        constI32 (j + 1), constI32 (i + 1), constI32 (n - 1), .plain (.tableCopy x y)])]) := by
  have hn1 : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
  rw [adminsToV_tableCopyLe j i n x y hj1 hi1 hn0]
  refine firesT_tableCopy_of hasRuleAt_tableCopyLe hz (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_constVar rfl) (evalExps_cons (evalExp_constVar rfl)
    (evalExps_cons (evalExp_case (evalExp_var rfl)) (evalExps_cons (evalExp_case (evalExp_var rfl))
    (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_jPay rfl) (evalExp_numE_iff.2 rfl)))
    (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_iPay rfl) (evalExp_numE_iff.2 rfl)))
    (evalExps_cons (evalExp_constPE (evalExp_pred hn1 rfl))
    (evalExps_cons (evalExp_case (evalExp_tup2 (evalExp_var rfl) (evalExp_var rfl)))
      evalExps_nil))))))), rfl⟩) ?_
  intro pr hpr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
  rcases hpr with rfl | rfl
  · exact .elsePr (otherwise17T hax htx hay hty hb hn0 _)
  · refine .ifPr (StoreDeep.evalT_of_20 (Pure.valsOnly_bindVals _)
      (RelFree.goodEvs_of_all (by decide)) ?_)
    exact evalExp_cmpE_iff.2 ⟨_, _, evalExp_jPay rfl, evalExp_iPay rfl,
      by simp [cmpValues, Num.cmp, Res.ofOption, hle]⟩

/-- **`Step_read/table.copy-gt` in `simEnv20T`**, where `j + n - 1` and `i + n - 1` do not
wrap. -/
theorem firesT_tableCopyGt {s : Store H} {f : Frame} {j i n : BitVec 32} {x y : TableIdx}
    {ax ay : Nat} {tx ty : TableInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (hax : f.module.tables[x.toNat]? = some ax) (htx : s.tables[ax]? = some tx)
    (hay : f.module.tables[y.toNat]? = some ay) (hty : s.tables[ay]? = some ty)
    (hb : i.toNat + n.toNat ≤ ty.refs.length ∧ j.toNat + n.toNat ≤ tx.refs.length) (hn0 : n ≠ 0)
    (hgt : i.toNat < j.toNat) (hj1 : j.toNat + n.toNat - 1 < 2 ^ 32)
    (hi1 : i.toNat + n.toNat - 1 < 2 ^ 32) :
    Fires (simEnv20T B) "Step_read" 18 (.tuple [configV hn ⟨s, f, tcopyCode j i n x y⟩,
      .list (adminsToV [constI32 (j + n - 1), constI32 (i + n - 1), .plain (.tableGet y),
        .plain (.tableSet x), constI32 j, constI32 i, constI32 (n - 1),
        .plain (.tableCopy x y)])]) := by
  have hn1 : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
  rw [adminsToV_tableCopyGt j i n x y hn1 hj1 hi1]
  refine firesT_tableCopy_of hasRuleAt_tableCopyGt hz (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_constPE (evalExp_sumPred hn1 (evalExp_jPay rfl) rfl))
    (evalExps_cons (evalExp_constPE (evalExp_sumPred hn1 (evalExp_iPay rfl) rfl))
    (evalExps_cons (evalExp_case (evalExp_var rfl)) (evalExps_cons (evalExp_case (evalExp_var rfl))
    (evalExps_cons (evalExp_constVar rfl) (evalExps_cons (evalExp_constVar rfl)
    (evalExps_cons (evalExp_constPE (evalExp_pred hn1 rfl))
    (evalExps_cons (evalExp_case (evalExp_tup2 (evalExp_var rfl) (evalExp_var rfl)))
      evalExps_nil))))))), rfl⟩) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .elsePr (otherwise18T hax htx hay hty hb hn0 hgt _)

end Silmaril.Wasm.SpecTec.Sim20.StoreBulk
