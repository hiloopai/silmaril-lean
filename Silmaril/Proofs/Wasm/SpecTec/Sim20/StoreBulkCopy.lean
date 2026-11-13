module

public import Silmaril.Wasm.SpecTec.Sim20.StoreFn.Thms

/-!
# `memory.copy` forward in `simEnv20T`

`Step_read` 40–43 of the 2.0 script are `memory.copy-trap`, `-zero`, `-le` and `-gt`. The `-le`
and `-gt` successors hold `i32.load8_u` and `i32.store8`, so they are typed in `simEnv20T` only,
and the rules are fired there from a state typed there:

* `firesT_memCopyTrap` (40);
* `firesT_memCopyZero` (41, `-- otherwise`): rule 40's body is refuted where both bounds hold
  (`otherwise41T`);
* `firesT_memCopyLe` (42, `-- otherwise`): rules 40 and 41 are refuted (`otherwise42T`);
* `firesT_memCopyGt` (43, `-- otherwise`): rules 40–42 are refuted (`otherwise43T`); rule 42's
  body is refuted through its `if j ≤ i` premise, without its own `otherwise`.

Each body is read back by moving its evaluations from `simEnv20T` to `simEnv20`
(`memCopyBodyT_parts`, through `StoreFn.evalBack20`).

**Restatements.** V2 computes `j + 1`, `i + 1` (`-le`) and `j + n - 1`, `i + n - 1` (`-gt`) in
`i32`; the script computes them over the naturals. The firing lemmas ask for these sums below
`2 ^ 32`; all hold when the memory has fewer than `2 ^ 32` bytes, since the bounds give
`i + n ≤ |mem|` and `j + n ≤ |mem|`.
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
open Silmaril.Wasm.SpecTec.Sim.RefsGC (otherwiseAt_of_table tags_of_take relRules ruleTags)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Whole (memCopyQs memCopyLhs memCopyE memCopyTrapRule
  memCopyZeroRule memCopyLeRule memCopyGtRule constJE constIE constNE jPay iPay predE memLenE
  load8E store8E constSuccE constPE sumPredE trapRhs evalExp_constIE evalExp_constNE
  evalExp_trapRhs evalExp_iPay evalExp_jPay evalExp_addNat20 evalExp_memLen20 evalExp_constVar
  evalExp_constPE evalExp_pred evalExp_store8 evalExp_load8 evalExp_sumPred evalExp_gtNat
  hasRuleAt_memCopyTrap hasRuleAt_memCopyZero hasRuleAt_memCopyLe hasRuleAt_memCopyGt
  codes20_four constJ_of_lhs constI_of_lhs constN_of_lhs constI32_inj zero_of_prem le_of_prem
  not_or_true lhsIn_memCopy adminsToV_memoryCopyLe adminsToV_memoryCopyGt toNat_add_sub_one)
open Silmaril.Wasm.SpecTec.Sim20.StoreFn (firesT_read_of20 hasRuleAtT_read readGood evalBack20
  quantsOkT_z ifBack readTagsT)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evRule evExp evPrems)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-! ## The left-hand side -/

/-- The code of the four rules. -/
abbrev copyCode (j i n : BitVec 32) : List Admin :=
  [constI32 j, constI32 i, constI32 n, .plain .memoryCopy]

/-- The scope of the four rules. -/
abbrev memCopyScope (s : Store H) (f : Frame) (j i n : BitVec 32) : List (IL.Id × Value) :=
  [("z", stateV hn s f), ("j", pctV j.toNat), ("i", pctV i.toNat), ("n", .num (.natN n.toNat))]

theorem evalExp_constJE {env : Env} {ρ : VarEnv} {c : BitVec 32}
    (fj : ρ.findVal? "j" = some (pctV c.toNat)) :
    EvalExp env ρ constJE (adminToV (constI32 c)) :=
  evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
    (evalExp_var fj))

/-- The left-hand side, evaluated in `simEnv20`. -/
theorem evalExp_memCopyLhs {s : Store H} {f : Frame} {j i n : BitVec 32} :
    EvalExp (E20 B) (VarEnv.empty.bindVals (memCopyScope (hn := hn) s f j i n)) memCopyLhs
      (configV hn ⟨s, f, copyCode j i n⟩) :=
  evalExp_case (evalExp_tup2 (evalExp_var rfl) (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_constJE rfl) (evalExps_cons (evalExp_constIE rfl) (evalExps_cons (evalExp_constNE rfl)
      (evalExps_cons (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)) evalExps_nil))),
    rfl⟩))

/-- The quantifiers, typed in `simEnv20T`. -/
theorem quantsOkT_memCopy {s : Store H} {f : Frame} {j i n : BitVec 32}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f)) :
    QuantsOk (simEnv20T B) (VarEnv.empty.bindVals (memCopyScope (hn := hn) s f j i n)) memCopyQs :=
  have hρ := Pure.valsOnly_bindVals (memCopyScope (hn := hn) s f j i n)
  quantsOkT_z hρ rfl hz (by decide) (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 j _ hρ)
    (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons rfl (Whole.typedV_n20 _ _ hρ) QuantsOk.nil)))

/-! ## Rule bodies in `simEnv20T`, read back -/

/-- A `memory.copy` rule body in `simEnv20T` at a `memory.copy` left-hand side binds the state
and the operands, and its premises hold in `simEnv20T`. -/
theorem memCopyBodyT_parts {D : Sim.Interp} {els : Prop} {nm : IL.Id} {rhs : Exp}
    {prems : List Prem} {k : Nat}
    (hR : HasRuleAt (E20 B) "Step_read" "%~>%" k
      (.ruleD nm memCopyQs "%~>%" (.tupE [memCopyLhs, rhs]) prems))
    {s : Store H} {f : Frame} {j i n : BitVec 32} {w : Value}
    (hbody : RuleBody (simEnv20T B) D els [] [] "%~>%"
      (.ruleD nm memCopyQs "%~>%" (.tupE [memCopyLhs, rhs]) prems)
      (.tuple [configV hn ⟨s, f, copyCode j i n⟩, w])) :
    ∃ ρ : VarEnv, ValsOnly ρ ∧ ρ.findVal? "z" = some (stateV hn s f) ∧
      ρ.findVal? "j" = some (pctV j.toNat) ∧ ρ.findVal? "i" = some (pctV i.toNat) ∧
      ρ.findVal? "n" = some (.num (.natN n.toNat)) ∧
      ρ.findDef? "mem" = none ∧ RelFree.GoodEvs RelFree.bad20 (evPrems prems) ∧
      ∀ pr ∈ prems, PremW (simEnv20T B) D els ρ pr := by
  obtain ⟨-, ρ₀, σ, hps, -, he, hp⟩ := hbody
  obtain rfl : ρ₀ = VarEnv.empty := (Option.some.inj hps).symm
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have hG := RelFree.goodEvs_of_all (readGood hR)
  have hG' : (RelFree.GoodEvs RelFree.bad20 (Sim.Round7.Script.evParams memCopyQs) ∧
      RelFree.GoodEvs RelFree.bad20 (evExp (.tupE [memCopyLhs, rhs]))) ∧
      RelFree.GoodEvs RelFree.bad20 (evPrems prems) := by
    simpa only [evRule, RelFree.goodEvs_append] using hG
  have hl := Sim.RefsGC.lhs_of_concl (evalBack20 hρ hG'.1.2 he)
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 hl
  have hu' : u = .tuple [stateV hn s f, .list (adminsToV (copyCode j i n))] :=
    (Value.case.inj hcu.symm).2
  obtain ⟨hZ, hL⟩ := Pure.evalExp_tup2_inv (hu' ▸ hu)
  obtain ⟨a₁, a₂, a₃, a₄, he4, h₁, h₂, h₃, -⟩ := codes20_four (Sim.RefsGC.elems_of_list hL)
  obtain ⟨rfl, rfl, rfl, -⟩ : constI32 j = a₁ ∧ constI32 i = a₂ ∧ constI32 n = a₃ ∧
      Admin.plain .memoryCopy = a₄ := by simpa using he4
  obtain ⟨j', hj', fj⟩ := constJ_of_lhs h₁
  obtain ⟨i', hi', fi⟩ := constI_of_lhs h₂
  obtain ⟨n', hn', fn⟩ := constN_of_lhs h₃
  obtain rfl := constI32_inj hj'
  obtain rfl := constI32_inj hi'
  obtain rfl := constI32_inj hn'
  exact ⟨_, hρ, evalExp_varE_iff.1 hZ, fj, fi, fn, rfl, hG'.2, hp⟩

/-- **Rule 40's body is refuted in `simEnv20T`** where both bounds hold. -/
theorem not_memCopyTrapBodyT {D : Sim.Interp} {els : Prop} {s : Store H} {f : Frame}
    {j i n : BitVec 32} {a : Nat} {mi : MemInst} (ha : f.module.memAddr? memIdx0 = some a)
    (hm : s.memInst? a = some mi)
    (hb : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size) (w : Value) :
    ¬ RuleBody (simEnv20T B) D els [] [] "%~>%" memCopyTrapRule
      (.tuple [configV hn ⟨s, f, copyCode j i n⟩, w]) := by
  intro hbody
  obtain ⟨ρ, hρ, fz, fj, fi, fn, hd, hG, hp⟩ := memCopyBodyT_parts hasRuleAt_memCopyTrap hbody
  have hpr := ifBack hρ hG hp (List.mem_singleton_self _)
  have hm' := evalExp_memLen20 (B := B) hd fz ha hm
  have h₁ : EvalExp (E20 B) ρ (.cmpE .gtOp (.numT .natT)
      (.binE .addOp (.numT .natT) iPay (.varE "n")) memLenE) (.bool false) := by
    have h := evalExp_gtNat (evalExp_addNat20 (evalExp_iPay fi) (evalExp_var fn)) hm'
    rwa [show decide (mi.bytes.size < i.toNat + n.toNat) = false by simp; omega] at h
  have h₂ : EvalExp (E20 B) ρ (.cmpE .gtOp (.numT .natT)
      (.binE .addOp (.numT .natT) jPay (.varE "n")) memLenE) (.bool false) := by
    have h := evalExp_gtNat (evalExp_addNat20 (evalExp_jPay fj) (evalExp_var fn)) hm'
    rwa [show decide (mi.bytes.size < j.toNat + n.toNat) = false by simp; omega] at h
  exact not_or_true h₁ h₂ hpr

/-- **Rule 41's body is refuted in `simEnv20T`** at a nonzero count. -/
theorem not_memCopyZeroBodyT {D : Sim.Interp} {els : Prop} {s : Store H} {f : Frame}
    {j i n : BitVec 32} (hn0 : n ≠ 0) (w : Value) :
    ¬ RuleBody (simEnv20T B) D els [] [] "%~>%" memCopyZeroRule
      (.tuple [configV hn ⟨s, f, copyCode j i n⟩, w]) := by
  intro hbody
  obtain ⟨ρ, hρ, -, -, -, fn, -, hG, hp⟩ := memCopyBodyT_parts hasRuleAt_memCopyZero hbody
  exact hn0 (zero_of_prem fn (ifBack hρ hG hp (List.mem_cons_of_mem _ (List.mem_singleton_self _))))

/-- **Rule 42's body is refuted in `simEnv20T`** where `i < j`: its `if j ≤ i` fails. -/
theorem not_memCopyLeBodyT {D : Sim.Interp} {els : Prop} {s : Store H} {f : Frame}
    {j i n : BitVec 32} (hgt : i.toNat < j.toNat) (w : Value) :
    ¬ RuleBody (simEnv20T B) D els [] [] "%~>%" memCopyLeRule
      (.tuple [configV hn ⟨s, f, copyCode j i n⟩, w]) := by
  intro hbody
  obtain ⟨ρ, hρ, -, fj, fi, -, -, hG, hp⟩ := memCopyBodyT_parts hasRuleAt_memCopyLe hbody
  have hle := le_of_prem fj fi (ifBack hρ hG hp (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  omega

/-! ## `otherwise` in `simEnv20T` -/

theorem lhsIn_copyCode (s : Store H) (f : Frame) (j i n : BitVec 32) :
    Sim.RefsGC.LhsIn ["CONST", "MEMORY.COPY"] (configV hn ⟨s, f, copyCode j i n⟩) :=
  lhsIn_memCopy s f j i n

/-- **`otherwise` for rule 41 in `simEnv20T`**, where both bounds hold. -/
theorem otherwise41T {s : Store H} {f : Frame} {j i n : BitVec 32} {a : Nat} {mi : MemInst}
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hb : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size) (w : Value) :
    otherwiseAt (simEnv20T B) "Step_read" [] 41
      (.tuple [configV hn ⟨s, f, copyCode j i n⟩, w]) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAtT_read (hasRuleAt_memCopyTrap (B := B))
  refine otherwiseAt_of_table hrel (tags_of_take hrel readTagsT) (by decide)
    (lhsIn_copyCode s f j i n) (exc := [40]) (by decide) ?_
  intro k hk _ r hr w' hw
  obtain ⟨c', rfl⟩ := Whole.sameLhs_inv hw
  obtain rfl := List.mem_singleton.1 hk
  rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_memCopyTrap) hr]
  exact not_memCopyTrapBodyT ha hm hb c'

/-- **`otherwise` for rule 42 in `simEnv20T`**, where both bounds hold and `n ≠ 0`. -/
theorem otherwise42T {s : Store H} {f : Frame} {j i n : BitVec 32} {a : Nat} {mi : MemInst}
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hb : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size) (hn0 : n ≠ 0)
    (w : Value) :
    otherwiseAt (simEnv20T B) "Step_read" [] 42
      (.tuple [configV hn ⟨s, f, copyCode j i n⟩, w]) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAtT_read (hasRuleAt_memCopyTrap (B := B))
  refine otherwiseAt_of_table hrel (tags_of_take hrel readTagsT) (by decide)
    (lhsIn_copyCode s f j i n) (exc := [40, 41]) (by decide) ?_
  intro k hk _ r hr w' hw
  obtain ⟨c', rfl⟩ := Whole.sameLhs_inv hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_memCopyTrap) hr]
    exact not_memCopyTrapBodyT ha hm hb c'
  · rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_memCopyZero) hr]
    exact not_memCopyZeroBodyT hn0 c'

/-- **`otherwise` for rule 43 in `simEnv20T`**, where both bounds hold, `n ≠ 0` and `i < j`. -/
theorem otherwise43T {s : Store H} {f : Frame} {j i n : BitVec 32} {a : Nat} {mi : MemInst}
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hb : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size) (hn0 : n ≠ 0)
    (hgt : i.toNat < j.toNat) (w : Value) :
    otherwiseAt (simEnv20T B) "Step_read" [] 43
      (.tuple [configV hn ⟨s, f, copyCode j i n⟩, w]) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAtT_read (hasRuleAt_memCopyTrap (B := B))
  refine otherwiseAt_of_table hrel (tags_of_take hrel readTagsT) (by decide)
    (lhsIn_copyCode s f j i n) (exc := [40, 41, 42]) (by decide) ?_
  intro k hk _ r hr w' hw
  obtain ⟨c', rfl⟩ := Whole.sameLhs_inv hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_memCopyTrap) hr]
    exact not_memCopyTrapBodyT ha hm hb c'
  · rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_memCopyZero) hr]
    exact not_memCopyZeroBodyT hn0 c'
  · rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_memCopyLe) hr]
    exact not_memCopyLeBodyT hgt c'

/-! ## The four rules fire -/

/-- A `memory.copy` rule fires in `simEnv20T` from its right-hand side evaluated in `simEnv20`
and its premises in `simEnv20T`. -/
theorem firesT_memCopy_of {k : Nat} {nm : IL.Id} {rhs : Exp} {prems : List Prem}
    (hR : HasRuleAt (E20 B) "Step_read" "%~>%" k
      (.ruleD nm memCopyQs "%~>%" (.tupE [memCopyLhs, rhs]) prems))
    {s : Store H} {f : Frame} {j i n : BitVec 32} {W : Value}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (hr : EvalExp (E20 B) (VarEnv.empty.bindVals (memCopyScope (hn := hn) s f j i n)) rhs W)
    (hp : ∀ pr ∈ prems, PremW (simEnv20T B) (Sim.DDerives (simEnv20T B) (Sim.otherwise (simEnv20T B)))
      (Sim.otherwise (simEnv20T B) "Step_read" [] k
        (.tuple [configV hn ⟨s, f, copyCode j i n⟩, W]))
      (VarEnv.empty.bindVals (memCopyScope (hn := hn) s f j i n)) pr) :
    Fires (simEnv20T B) "Step_read" k (.tuple [configV hn ⟨s, f, copyCode j i n⟩, W]) := by
  have hρ := Pure.valsOnly_bindVals (memCopyScope (hn := hn) s f j i n)
  have hG := RelFree.goodEvs_of_all (readGood hR)
  have hGe : RelFree.GoodEvs RelFree.bad20 (evExp (.tupE [memCopyLhs, rhs])) := by
    simp only [evRule, RelFree.goodEvs_append] at hG
    exact hG.1.2
  exact Pure.fires_of_ruleAt (hasRuleAtT_read hR) _ (quantsOkT_memCopy hz)
    (StoreDeep.evalT_of_20 hρ hGe (evalExp_tup2 evalExp_memCopyLhs hr)) hp

/-- **`Step_read/memory.copy-trap` in `simEnv20T`.** -/
theorem firesT_memCopyTrap {s : Store H} {f : Frame} {j i n : BitVec 32} {a : Nat}
    {mi : MemInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hlt : mi.bytes.size < i.toNat + n.toNat ∨ mi.bytes.size < j.toNat + n.toNat) :
    Fires (simEnv20T B) "Step_read" 40
      (.tuple [configV hn ⟨s, f, copyCode j i n⟩, .list (adminsToV [.trap])]) := by
  refine firesT_read_of20 (D := fun _ _ _ _ => True) (els := True) hasRuleAt_memCopyTrap rfl
    (memCopyScope (hn := hn) s f j i n) (quantsOkT_memCopy hz)
    (evalExp_tup2 evalExp_memCopyLhs evalExp_trapRhs) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  have hm' := evalExp_memLen20 (B := B) (ρ := VarEnv.empty.bindVals
    (memCopyScope (hn := hn) s f j i n)) rfl rfl ha hm
  exact .ifPr (Whole.evalExp_or
    (evalExp_gtNat (evalExp_addNat20 (evalExp_iPay rfl) (evalExp_var rfl)) hm')
    (evalExp_gtNat (evalExp_addNat20 (evalExp_jPay rfl) (evalExp_var rfl)) hm')
    (by simpa using hlt))

/-- **`Step_read/memory.copy-zero` in `simEnv20T`.** -/
theorem firesT_memCopyZero {s : Store H} {f : Frame} {j i : BitVec 32} {a : Nat}
    {mi : MemInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hb : i.toNat ≤ mi.bytes.size ∧ j.toNat ≤ mi.bytes.size) :
    Fires (simEnv20T B) "Step_read" 41
      (.tuple [configV hn ⟨s, f, copyCode j i 0⟩, .list (adminsToV [])]) := by
  refine firesT_memCopy_of hasRuleAt_memCopyZero hz Pure.evalExp_list0 ?_
  intro pr hpr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
  rcases hpr with rfl | rfl
  · exact .elsePr (otherwise41T ha hm (by simpa using hb) _)
  · refine .ifPr (StoreDeep.evalT_of_20 (Pure.valsOnly_bindVals _)
      (RelFree.goodEvs_of_all (by decide)) ?_)
    exact evalExp_cmpE_iff.2 ⟨_, _, evalExp_var rfl, evalExp_numE_iff.2 rfl,
      cmpValues_eq_true_iff.2 rfl⟩

/-- **`Step_read/memory.copy-le` in `simEnv20T`**, where `j + 1` and `i + 1` do not wrap. -/
theorem firesT_memCopyLe {s : Store H} {f : Frame} {j i n : BitVec 32} {a : Nat}
    {mi : MemInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hb : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size) (hn0 : n ≠ 0)
    (hle : j.toNat ≤ i.toNat) (hj1 : j.toNat + 1 < 2 ^ 32) (hi1 : i.toNat + 1 < 2 ^ 32) :
    Fires (simEnv20T B) "Step_read" 42 (.tuple [configV hn ⟨s, f, copyCode j i n⟩,
      .list (adminsToV [constI32 j, constI32 i, load8u, store8, constI32 (j + 1),
        constI32 (i + 1), constI32 (n - 1), .plain .memoryCopy])]) := by
  have hn1 : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
  rw [adminsToV_memoryCopyLe j i n hj1 hi1 hn0]
  refine firesT_memCopy_of hasRuleAt_memCopyLe hz (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_constVar rfl) (evalExps_cons (evalExp_constVar rfl) (evalExps_cons (evalExp_load8 rfl)
    (evalExps_cons (evalExp_store8 rfl)
    (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_jPay rfl) (evalExp_numE_iff.2 rfl)))
    (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_iPay rfl) (evalExp_numE_iff.2 rfl)))
    (evalExps_cons (evalExp_constPE (evalExp_pred hn1 rfl))
    (evalExps_cons (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
      evalExps_nil))))))), rfl⟩) ?_
  intro pr hpr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
  rcases hpr with rfl | rfl
  · exact .elsePr (otherwise42T ha hm hb hn0 _)
  · refine .ifPr (StoreDeep.evalT_of_20 (Pure.valsOnly_bindVals _)
      (RelFree.goodEvs_of_all (by decide)) ?_)
    exact evalExp_cmpE_iff.2 ⟨_, _, evalExp_jPay rfl, evalExp_iPay rfl,
      by simp [cmpValues, Num.cmp, Res.ofOption, hle]⟩

/-- **`Step_read/memory.copy-gt` in `simEnv20T`**, where `j + n - 1` and `i + n - 1` do not
wrap. -/
theorem firesT_memCopyGt {s : Store H} {f : Frame} {j i n : BitVec 32} {a : Nat}
    {mi : MemInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hb : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size) (hn0 : n ≠ 0)
    (hgt : i.toNat < j.toNat) (hj1 : j.toNat + n.toNat - 1 < 2 ^ 32)
    (hi1 : i.toNat + n.toNat - 1 < 2 ^ 32) :
    Fires (simEnv20T B) "Step_read" 43 (.tuple [configV hn ⟨s, f, copyCode j i n⟩,
      .list (adminsToV [constI32 (j + n - 1), constI32 (i + n - 1), load8u, store8, constI32 j,
        constI32 i, constI32 (n - 1), .plain .memoryCopy])]) := by
  have hn1 : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
  rw [adminsToV_memoryCopyGt j i n hn1 hj1 hi1]
  refine firesT_memCopy_of hasRuleAt_memCopyGt hz (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_constPE (evalExp_sumPred hn1 (evalExp_jPay rfl) rfl))
    (evalExps_cons (evalExp_constPE (evalExp_sumPred hn1 (evalExp_iPay rfl) rfl))
    (evalExps_cons (evalExp_load8 rfl) (evalExps_cons (evalExp_store8 rfl)
    (evalExps_cons (evalExp_constVar rfl) (evalExps_cons (evalExp_constVar rfl)
    (evalExps_cons (evalExp_constPE (evalExp_pred hn1 rfl))
    (evalExps_cons (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
      evalExps_nil))))))), rfl⟩) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .elsePr (otherwise43T ha hm hb hn0 hgt _)

end Silmaril.Wasm.SpecTec.Sim20.StoreBulk
