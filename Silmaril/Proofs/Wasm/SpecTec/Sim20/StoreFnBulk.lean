module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFnRun

/-!
# `memory.fill` forward in `simEnv20T`

The bulk rules of 2.0 rewrite to code with stores: `memory.fill-succ` (`Step_read` 39) puts an
`i32.store8` in front of the next `memory.fill`. So their successors are typed in `simEnv20T`
only, and they are fired there, from a state typed there:

* `firesT_memFillTrap` (rule 37);
* `firesT_memFillZero` (rule 38, `-- otherwise`): the `otherwise` is proved in `simEnv20T`
  (`otherwise38T`); rule 37 is the only earlier rule with the same tags, and its body is refuted
  where the fill is in bounds (`not_memFillTrapBodyT`);
* `firesT_memFillSucc` (rule 39, `-- otherwise`): rules 37 and 38 are refuted
  (`otherwise39T`).

**Restatement at `-succ`.** V2 computes `i + 1` in `i32`, which wraps at `2 ^ 32`; the script's
`CONST I32 (% $(i + 1))` does not. When `i = 2 ^ 32 - 1`, `n = 1` and the memory has `2 ^ 32`
bytes (65536 pages, the 2.0 maximum), V2 steps to `i32.const 0` where the script's image would
hold `CONST I32 (% 2 ^ 32)`, which is not a value of `num_(I32)`. The forward statement here
asks for `i + 1 < 2 ^ 32`, which holds whenever the memory has fewer than `2 ^ 32` bytes.

The rules are fired as rules; they are not yet part of the invariant `Good20F`, whose covered
code (`okD`) does not admit `memory.fill`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreFn

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
open Silmaril.Wasm.SpecTec.Sim.RefsGC (otherwiseAt_of_table tags_of_take relRules ruleTags LhsIn)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Whole (memFillQs memFillEs memFillLhs memFillTrapRule
  memFillZeroRule memFillSuccRule memFillSuccRhs memLenE constIE constNE valE iPay predE
  store8E trapRhs evalExp_constIE evalExp_constNE evalExp_trapRhs evalExp_iPay evalExp_addNat20
  evalExp_memLen20 cmpValues_gtOp_nat20 evalExp_constPE evalExp_pred evalExp_store8
  adminsToV_memoryFillSucc hasRuleAt_memFillTrap hasRuleAt_memFillZero hasRuleAt_memFillSucc
  codes20_four constI_of_lhs constN_of_lhs constI32_inj)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evRule evExp evPrems evPrem)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-! ## The left-hand side -/

/-- The scope of the three rules. -/
abbrev memFillScope (s : Store H) (f : Frame) (i : BitVec 32) (v : Val) (n : BitVec 32) :
    List (IL.Id × Value) :=
  [("z", stateV hn s f), ("i", pctV i.toNat), ("val", valV v), ("n", .num (.natN n.toNat))]

/-- The left-hand side, evaluated in `simEnv20`. -/
theorem evalExp_memFillLhs {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val} :
    EvalExp (E20 B) (VarEnv.empty.bindVals (memFillScope (hn := hn) s f i v n)) memFillLhs
      (configV hn ⟨s, f, [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill]⟩) := by
  have hv : EvalExp (E20 B) (VarEnv.empty.bindVals (memFillScope (hn := hn) s f i v n)) valE
      (adminToV v.toAdmin) := by
    rw [Pure.adminToV_toAdmin]
    exact evalExp_subE_iff.2 (evalExp_var rfl)
  exact evalExp_case (evalExp_tup2 (evalExp_var rfl) (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_constIE rfl) (evalExps_cons hv (evalExps_cons (evalExp_constNE rfl)
      (evalExps_cons (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)) evalExps_nil))),
    rfl⟩))

/-- The quantifiers, typed in `simEnv20T`. -/
theorem quantsOkT_memFill {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f)) :
    QuantsOk (simEnv20T B) (VarEnv.empty.bindVals (memFillScope (hn := hn) s f i v n)) memFillQs :=
  have hρ := Pure.valsOnly_bindVals (memFillScope (hn := hn) s f i v n)
  quantsOkT_z hρ rfl hz (by decide) (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
    (QuantsOk.cons rfl (Whole.typedV_val20 v _ hρ)
      (QuantsOk.cons rfl (Whole.typedV_n20 _ _ hρ) QuantsOk.nil)))

/-- The tags of a `memory.fill` left-hand side. -/
theorem lhsIn_memFill (s : Store H) (f : Frame) (i n : BitVec 32) (v : Val) :
    LhsIn ["CONST", "VCONST", "REF.NULL", "REF.FUNC_ADDR", "REF.HOST_ADDR", "MEMORY.FILL"]
      (configV hn ⟨s, f, [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill]⟩) := by
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

/-- A `memory.fill` rule body in `simEnv20T` at a `memory.fill` left-hand side binds the state
and the operands, and its premises hold in `simEnv20T`. -/
theorem memFillBodyT_parts {D : Sim.Interp} {els : Prop} {nm : IL.Id} {rhs : Exp}
    {prems : List Prem} {k : Nat}
    (hR : HasRuleAt (E20 B) "Step_read" "%~>%" k
      (.ruleD nm memFillQs "%~>%" (.tupE [memFillLhs, rhs]) prems))
    {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val} {w : Value}
    (hbody : RuleBody (simEnv20T B) D els [] [] "%~>%"
      (.ruleD nm memFillQs "%~>%" (.tupE [memFillLhs, rhs]) prems)
      (.tuple [configV hn ⟨s, f, [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill]⟩, w])) :
    ∃ ρ : VarEnv, ValsOnly ρ ∧ ρ.findVal? "z" = some (stateV hn s f) ∧
      ρ.findVal? "i" = some (pctV i.toNat) ∧ ρ.findVal? "n" = some (.num (.natN n.toNat)) ∧
      ρ.findDef? "mem" = none ∧ RelFree.GoodEvs RelFree.bad20 (evPrems prems) ∧
      ∀ pr ∈ prems, PremW (simEnv20T B) D els ρ pr := by
  obtain ⟨-, ρ₀, σ, hps, -, he, hp⟩ := hbody
  obtain rfl : ρ₀ = VarEnv.empty := (Option.some.inj hps).symm
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have hG := RelFree.goodEvs_of_all (readGood hR)
  have hG' : (RelFree.GoodEvs RelFree.bad20 (Sim.Round7.Script.evParams memFillQs) ∧
      RelFree.GoodEvs RelFree.bad20 (evExp (.tupE [memFillLhs, rhs]))) ∧
      RelFree.GoodEvs RelFree.bad20 (evPrems prems) := by
    simpa only [evRule, RelFree.goodEvs_append] using hG
  have hl := Sim.RefsGC.lhs_of_concl (evalBack20 hρ hG'.1.2 he)
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 hl
  have hu' : u = .tuple [stateV hn s f,
      .list (adminsToV [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill])] :=
    (Value.case.inj hcu.symm).2
  obtain ⟨hZ, hL⟩ := Pure.evalExp_tup2_inv (hu' ▸ hu)
  obtain ⟨a₁, a₂, a₃, a₄, he4, h₁, -, h₃, -⟩ := codes20_four (Sim.RefsGC.elems_of_list hL)
  obtain ⟨rfl, -, rfl, -⟩ : constI32 i = a₁ ∧ v.toAdmin = a₂ ∧ constI32 n = a₃ ∧
      Admin.plain .memoryFill = a₄ := by simpa using he4
  obtain ⟨i', hi', fi⟩ := constI_of_lhs h₁
  obtain ⟨n', hn', fn⟩ := constN_of_lhs h₃
  obtain rfl := constI32_inj hi'
  obtain rfl := constI32_inj hn'
  exact ⟨_, hρ, evalExp_varE_iff.1 hZ, fi, fn, rfl, hG'.2, hp⟩

/-- An `if` premise of a rule body in `simEnv20T`, moved back to `simEnv20`. -/
theorem ifBack {D : Sim.Interp} {els : Prop} {ρ : VarEnv} {prems : List Prem} {e : Exp}
    (hρ : ValsOnly ρ) (hG : RelFree.GoodEvs RelFree.bad20 (evPrems prems))
    (hp : ∀ pr ∈ prems, PremW (simEnv20T B) D els ρ pr) (hm : Prem.ifPr e ∈ prems) :
    EvalExp (E20 B) ρ e (.bool true) :=
  evalBack20 hρ (RelFree.goodEvs_prems hG _ hm) (Pure.ifPrem (hp _ hm))

/-- **Rule 37's body is refuted in `simEnv20T`** where the fill is in bounds. -/
theorem not_memFillTrapBodyT {D : Sim.Interp} {els : Prop} {s : Store H} {f : Frame}
    {i n : BitVec 32} {v : Val} {a : Nat} {mi : MemInst} (ha : f.module.memAddr? memIdx0 = some a)
    (hm : s.memInst? a = some mi) (hb : i.toNat + n.toNat ≤ mi.bytes.size) (w : Value) :
    ¬ RuleBody (simEnv20T B) D els [] [] "%~>%" memFillTrapRule
      (.tuple [configV hn ⟨s, f, [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill]⟩, w]) := by
  intro hbody
  obtain ⟨ρ, hρ, fz, fi, fn, hd, hG, hp⟩ := memFillBodyT_parts hasRuleAt_memFillTrap hbody
  have hpr := ifBack hρ hG hp (List.mem_singleton_self _)
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 hpr
  rw [EvalExp.unique e₁ (evalExp_addNat20 (evalExp_iPay fi) (evalExp_var fn)),
    EvalExp.unique e₂ (evalExp_memLen20 hd fz ha hm)] at hcmp
  simp [cmpValues, Num.cmp, Res.ofOption] at hcmp
  omega

/-- **Rule 38's body is refuted in `simEnv20T`** at a nonzero count. -/
theorem not_memFillZeroBodyT {D : Sim.Interp} {els : Prop} {s : Store H} {f : Frame}
    {i n : BitVec 32} {v : Val} (hn0 : n ≠ 0) (w : Value) :
    ¬ RuleBody (simEnv20T B) D els [] [] "%~>%" memFillZeroRule
      (.tuple [configV hn ⟨s, f, [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill]⟩, w]) := by
  intro hbody
  obtain ⟨ρ, hρ, -, -, fn, -, hG, hp⟩ := memFillBodyT_parts hasRuleAt_memFillZero hbody
  have hpr := ifBack hρ hG hp (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 hpr
  have e : v₁ = v₂ := cmpValues_eq_true_iff.1 hcmp
  rw [EvalExp.unique e₁ (evalExp_var fn), EvalExp.unique e₂ (evalExp_numE_iff.2 rfl)] at e
  exact hn0 (BitVec.eq_of_toNat_eq (by simpa using e))

/-! ## `otherwise` in `simEnv20T` -/

/-- The tag table of `Step_read`, in `simEnv20T`. -/
theorem readTagsT : ((relRules (simEnv20T B) "Step_read").map ruleTags).take 47 =
    Whole.readTags20 := by
  rw [relRules_readT, Whole.relRules_simEnv20, Whole.readTags20_eq]
  rfl

/-- **`otherwise` for rule 38 in `simEnv20T`**, where the fill is in bounds. -/
theorem otherwise38T {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val} {a : Nat}
    {mi : MemInst} (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hb : i.toNat + n.toNat ≤ mi.bytes.size) (w : Value) :
    otherwiseAt (simEnv20T B) "Step_read" [] 38
      (.tuple [configV hn ⟨s, f, [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill]⟩, w]) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAtT_read (hasRuleAt_memFillTrap (B := B))
  refine otherwiseAt_of_table hrel (tags_of_take hrel readTagsT) (by decide)
    (lhsIn_memFill s f i n v) (exc := [37]) (by decide) ?_
  intro k hk _ r hr w' hw
  obtain ⟨c', rfl⟩ := Whole.sameLhs_inv hw
  obtain rfl := List.mem_singleton.1 hk
  rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_memFillTrap) hr]
  exact not_memFillTrapBodyT ha hm hb c'

/-- **`otherwise` for rule 39 in `simEnv20T`**, where the fill is in bounds and the count
nonzero. -/
theorem otherwise39T {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val} {a : Nat}
    {mi : MemInst} (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hb : i.toNat + n.toNat ≤ mi.bytes.size) (hn0 : n ≠ 0) (w : Value) :
    otherwiseAt (simEnv20T B) "Step_read" [] 39
      (.tuple [configV hn ⟨s, f, [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill]⟩, w]) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAtT_read (hasRuleAt_memFillTrap (B := B))
  refine otherwiseAt_of_table hrel (tags_of_take hrel readTagsT) (by decide)
    (lhsIn_memFill s f i n v) (exc := [37, 38]) (by decide) ?_
  intro k hk _ r hr w' hw
  obtain ⟨c', rfl⟩ := Whole.sameLhs_inv hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_memFillTrap) hr]
    exact not_memFillTrapBodyT ha hm hb c'
  · rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_memFillZero) hr]
    exact not_memFillZeroBodyT hn0 c'

/-! ## The three rules fire -/

/-- **`Step_read/memory.fill-trap` in `simEnv20T`.** -/
theorem firesT_memFillTrap {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val} {a : Nat}
    {mi : MemInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hlt : mi.bytes.size < i.toNat + n.toNat) :
    Fires (simEnv20T B) "Step_read" 37 (.tuple [
      configV hn ⟨s, f, [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill]⟩,
      .list (adminsToV [.trap])]) := by
  refine firesT_read_of20 (D := fun _ _ _ _ => True) (els := True) hasRuleAt_memFillTrap rfl
    (memFillScope (hn := hn) s f i v n) (quantsOkT_memFill hz)
    (evalExp_tup2 evalExp_memFillLhs evalExp_trapRhs) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_addNat20 (evalExp_iPay rfl) (evalExp_var rfl),
    evalExp_memLen20 rfl rfl ha hm, cmpValues_gtOp_nat20 hlt⟩)

/-- The scope's evaluations move to `simEnv20T` whole. -/
theorem firesT_memFill_of {k : Nat} {nm : IL.Id} {rhs : Exp} {prems : List Prem}
    (hR : HasRuleAt (E20 B) "Step_read" "%~>%" k
      (.ruleD nm memFillQs "%~>%" (.tupE [memFillLhs, rhs]) prems))
    {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val} {W : Value}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (hr : EvalExp (E20 B) (VarEnv.empty.bindVals (memFillScope (hn := hn) s f i v n)) rhs W)
    (hp : ∀ pr ∈ prems, PremW (simEnv20T B) (Sim.DDerives (simEnv20T B) (Sim.otherwise (simEnv20T B)))
      (Sim.otherwise (simEnv20T B) "Step_read" [] k
        (.tuple [configV hn ⟨s, f, [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill]⟩, W]))
      (VarEnv.empty.bindVals (memFillScope (hn := hn) s f i v n)) pr) :
    Fires (simEnv20T B) "Step_read" k
      (.tuple [configV hn ⟨s, f, [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill]⟩, W]) := by
  have hρ := Pure.valsOnly_bindVals (memFillScope (hn := hn) s f i v n)
  have hG := RelFree.goodEvs_of_all (readGood hR)
  have hGe : RelFree.GoodEvs RelFree.bad20 (evExp (.tupE [memFillLhs, rhs])) := by
    simp only [evRule, RelFree.goodEvs_append] at hG
    exact hG.1.2
  exact Pure.fires_of_ruleAt (hasRuleAtT_read hR) _ (quantsOkT_memFill hz)
    (StoreDeep.evalT_of_20 hρ hGe (evalExp_tup2 evalExp_memFillLhs hr)) hp

/-- **`Step_read/memory.fill-zero` in `simEnv20T`.** -/
theorem firesT_memFillZero {s : Store H} {f : Frame} {i : BitVec 32} {v : Val} {a : Nat}
    {mi : MemInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hb : i.toNat ≤ mi.bytes.size) :
    Fires (simEnv20T B) "Step_read" 38 (.tuple [
      configV hn ⟨s, f, [constI32 i, v.toAdmin, constI32 0, .plain .memoryFill]⟩,
      .list (adminsToV [])]) := by
  refine firesT_memFill_of hasRuleAt_memFillZero hz Pure.evalExp_list0 ?_
  intro pr hpr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
  rcases hpr with rfl | rfl
  · exact .elsePr (otherwise38T ha hm (by simpa using hb) _)
  · refine .ifPr (StoreDeep.evalT_of_20 (Pure.valsOnly_bindVals _) (RelFree.goodEvs_of_all (by decide)) ?_)
    exact evalExp_cmpE_iff.2 ⟨_, _, evalExp_var rfl, evalExp_numE_iff.2 rfl,
      cmpValues_eq_true_iff.2 rfl⟩

/-- **`Step_read/memory.fill-succ` in `simEnv20T`**, where `i + 1` does not wrap (a documented
restatement: see the module docstring). -/
theorem firesT_memFillSucc {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val} {a : Nat}
    {mi : MemInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hb : i.toNat + n.toNat ≤ mi.bytes.size) (hn0 : n ≠ 0) (hi1 : i.toNat + 1 < 2 ^ 32) :
    Fires (simEnv20T B) "Step_read" 39 (.tuple [
      configV hn ⟨s, f, [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill]⟩,
      .list (adminsToV [constI32 i, v.toAdmin, store8, constI32 (i + 1), v.toAdmin,
        constI32 (n - 1), .plain .memoryFill])]) := by
  have hn1 : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
  have hv : EvalExp (E20 B) (VarEnv.empty.bindVals (memFillScope (hn := hn) s f i v n)) valE
      (valV v) := evalExp_subE_iff.2 (evalExp_var rfl)
  rw [adminsToV_memoryFillSucc i n v hi1 hn0]
  refine firesT_memFill_of hasRuleAt_memFillSucc hz (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
      (evalExp_var rfl))) (evalExps_cons hv (evalExps_cons (evalExp_store8 rfl)
    (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_iPay rfl) (evalExp_numE_iff.2 rfl)))
    (evalExps_cons hv (evalExps_cons (evalExp_constPE (evalExp_pred hn1 rfl))
    (evalExps_cons (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)) evalExps_nil)))))),
    rfl⟩) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .elsePr (otherwise39T ha hm hb hn0 _)

end Silmaril.Wasm.SpecTec.Sim20.StoreFn
