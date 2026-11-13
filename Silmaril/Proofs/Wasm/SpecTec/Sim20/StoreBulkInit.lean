module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkCopy

/-!
# `memory.init` forward in `simEnv20T`

`Step_read` 44–46 of the 2.0 script are `memory.init-trap`, `-zero` and `-succ`. `-succ` writes
one byte of the data segment with `i32.store8`, so its successor is typed in `simEnv20T` only:

* `firesT_memInitTrap` (44);
* `firesT_memInitZero` (45, `-- otherwise`): rule 44's body is refuted where both bounds hold
  (`otherwise45T`);
* `firesT_memInitSucc` (46, `-- otherwise`): rules 44 and 45 are refuted (`otherwise46T`).

**Restatement.** V2 computes `j + 1` and `i + 1` in `i32`; the script does not. `-succ` asks for
both below `2 ^ 32`. They hold when the memory and the data segment have fewer than `2 ^ 32`
bytes, since the bounds give `j + n ≤ |mem|` and `i + n ≤ |data|`.
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
open Silmaril.Wasm.SpecTec.Sim.RefsGC (otherwiseAt_of_table tags_of_take LhsIn)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Whole (memInitQs memInitLhs memInitE memInitTrapRule
  memInitZeroRule memInitSuccRule dataBytesE dataByteE constJE constIE constNE jPay iPay predE
  memLenE store8E constSuccE constPE trapRhs evalExp_constIE evalExp_constNE evalExp_trapRhs
  evalExp_iPay evalExp_jPay evalExp_addNat20 evalExp_memLen20 evalExp_constVar evalExp_constPE
  evalExp_pred evalExp_store8 evalExp_gtNat evalExp_dataBytes20 evalExp_dataByte20
  bytesV_length20 hasRuleAt_memInitTrap hasRuleAt_memInitZero hasRuleAt_memInitSucc codes20_four
  constJ_of_lhs constI_of_lhs constN_of_lhs constI32_inj zero_of_prem not_or_true
  adminsToV_memoryInitSucc)
open Silmaril.Wasm.SpecTec.Sim20.StoreFn (firesT_read_of20 hasRuleAtT_read readGood evalBack20
  quantsOkT_z ifBack readTagsT)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evRule evExp evPrems)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-! ## The left-hand side -/

/-- The code of the three rules. -/
abbrev initCode (j i n : BitVec 32) (x : DataIdx) : List Admin :=
  [constI32 j, constI32 i, constI32 n, .plain (.memoryInit x)]

/-- The scope of the three rules. -/
abbrev memInitScope (s : Store H) (f : Frame) (j i n : BitVec 32) (x : DataIdx) :
    List (IL.Id × Value) :=
  [("z", stateV hn s f), ("j", pctV j.toNat), ("i", pctV i.toNat), ("n", .num (.natN n.toNat)),
    ("x", idxV x)]

/-- The left-hand side, evaluated in `simEnv20`. -/
theorem evalExp_memInitLhs {s : Store H} {f : Frame} {j i n : BitVec 32} {x : DataIdx} :
    EvalExp (E20 B) (VarEnv.empty.bindVals (memInitScope (hn := hn) s f j i n x)) memInitLhs
      (configV hn ⟨s, f, initCode j i n x⟩) :=
  evalExp_case (evalExp_tup2 (evalExp_var rfl) (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_constJE rfl) (evalExps_cons (evalExp_constIE rfl) (evalExps_cons (evalExp_constNE rfl)
      (evalExps_cons (evalExp_case (evalExp_var rfl)) evalExps_nil))), rfl⟩))

/-- The quantifiers, typed in `simEnv20T`. -/
theorem quantsOkT_memInit {s : Store H} {f : Frame} {j i n : BitVec 32} {x : DataIdx}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f)) :
    QuantsOk (simEnv20T B) (VarEnv.empty.bindVals (memInitScope (hn := hn) s f j i n x))
      memInitQs :=
  have hρ := Pure.valsOnly_bindVals (memInitScope (hn := hn) s f j i n x)
  quantsOkT_z hρ rfl hz (by decide) (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 j _ hρ)
    (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons rfl (Whole.typedV_n20 _ _ hρ)
        (QuantsOk.cons rfl (Whole.typedV_idx20 x _ hρ) QuantsOk.nil))))

/-- The tags of a `memory.init` left-hand side. -/
theorem lhsIn_initCode (s : Store H) (f : Frame) (j i n : BitVec 32) (x : DataIdx) :
    LhsIn ["CONST", "MEMORY.INIT"] (configV hn ⟨s, f, initCode j i n x⟩) := by
  refine Or.inr ⟨_, _, rfl, ?_⟩
  intro u hu op w hw
  simp only [adminsToV, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl <;>
  · rw [← Whole.adminToV_case20 hw]
    simp [Whole.adminHead20, Whole.instrHead20]

/-- A data segment of the frame's module, from V2's `data?`. -/
theorem data?_some {s : Store H} {f : Frame} {x : DataIdx} {di : DataInst}
    (h : (⟨s, f⟩ : State H).data? x = some di) :
    ∃ a, f.module.datas[x.toNat]? = some a ∧ s.datas[a]? = some di := by
  simp only [State.data?, ModuleInst.dataAddr?, Store.dataInst?, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at h
  exact h

/-! ## Rule bodies in `simEnv20T`, read back -/

/-- A `memory.init` rule body in `simEnv20T` at a `memory.init` left-hand side binds the state
and the operands, and its premises hold in `simEnv20T`. -/
theorem memInitBodyT_parts {D : Sim.Interp} {els : Prop} {nm : IL.Id} {rhs : Exp}
    {prems : List Prem} {k : Nat}
    (hR : HasRuleAt (E20 B) "Step_read" "%~>%" k
      (.ruleD nm memInitQs "%~>%" (.tupE [memInitLhs, rhs]) prems))
    {s : Store H} {f : Frame} {j i n : BitVec 32} {x : DataIdx} {w : Value}
    (hbody : RuleBody (simEnv20T B) D els [] [] "%~>%"
      (.ruleD nm memInitQs "%~>%" (.tupE [memInitLhs, rhs]) prems)
      (.tuple [configV hn ⟨s, f, initCode j i n x⟩, w])) :
    ∃ ρ : VarEnv, ValsOnly ρ ∧ ρ.findVal? "z" = some (stateV hn s f) ∧
      ρ.findVal? "j" = some (pctV j.toNat) ∧ ρ.findVal? "i" = some (pctV i.toNat) ∧
      ρ.findVal? "n" = some (.num (.natN n.toNat)) ∧ ρ.findVal? "x" = some (idxV x) ∧
      ρ.findDef? "mem" = none ∧ ρ.findDef? "data" = none ∧
      RelFree.GoodEvs RelFree.bad20 (evPrems prems) ∧
      ∀ pr ∈ prems, PremW (simEnv20T B) D els ρ pr := by
  obtain ⟨-, ρ₀, σ, hps, -, he, hp⟩ := hbody
  obtain rfl : ρ₀ = VarEnv.empty := (Option.some.inj hps).symm
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have hG' : (RelFree.GoodEvs RelFree.bad20 (Sim.Round7.Script.evParams memInitQs) ∧
      RelFree.GoodEvs RelFree.bad20 (evExp (.tupE [memInitLhs, rhs]))) ∧
      RelFree.GoodEvs RelFree.bad20 (evPrems prems) := by
    simpa only [evRule, RelFree.goodEvs_append] using RelFree.goodEvs_of_all (readGood hR)
  have hl : EvalExp (E20 B) (VarEnv.empty.bindVals σ) memInitLhs
      (configV hn ⟨s, f, initCode j i n x⟩) :=
    Sim.RefsGC.lhs_of_concl (evalBack20 hρ hG'.1.2 he)
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 hl
  have hu' : u = .tuple [stateV hn s f, .list (adminsToV (initCode j i n x))] :=
    (Value.case.inj hcu.symm).2
  obtain ⟨hZ, hL⟩ := Pure.evalExp_tup2_inv (hu' ▸ hu)
  obtain ⟨a₁, a₂, a₃, a₄, he4, h₁, h₂, h₃, h₄⟩ := codes20_four (Sim.RefsGC.elems_of_list hL)
  obtain ⟨rfl, rfl, rfl, rfl⟩ : constI32 j = a₁ ∧ constI32 i = a₂ ∧ constI32 n = a₃ ∧
      Admin.plain (.memoryInit x) = a₄ := by simpa using he4
  obtain ⟨j', hj', fj⟩ := constJ_of_lhs h₁
  obtain ⟨i', hi', fi⟩ := constI_of_lhs h₂
  obtain ⟨n', hn', fn⟩ := constN_of_lhs h₃
  obtain rfl := constI32_inj hj'
  obtain rfl := constI32_inj hi'
  obtain rfl := constI32_inj hn'
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) :=
    Whole.idx_of_caseE (X := idxV x) h₄ rfl
  exact ⟨_, hρ, evalExp_varE_iff.1 hZ, fj, fi, fn, fx, rfl, rfl, hG'.2, hp⟩

/-- `|$data(z, x).BYTES|`, evaluated. -/
theorem evalExp_dataLen20 {ρ : VarEnv} {s : Store H} {f : Frame} {x : DataIdx} {a : Nat}
    {di : DataInst} (hρ : ρ.findDef? "data" = none) (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? "x" = some (idxV x)) (ha : f.module.datas[x.toNat]? = some a)
    (hd : s.datas[a]? = some di) :
    EvalExp (E20 B) ρ (.lenE dataBytesE) (.num (.natN di.bytes.size)) := by
  refine evalExp_lenE_iff.2 ⟨_, evalExp_dataBytes20 hρ fz fx ha hd, ?_⟩
  rw [(bytesV_length20 di.bytes).2]

/-- **Rule 44's body is refuted in `simEnv20T`** where both bounds hold. -/
theorem not_memInitTrapBodyT {D : Sim.Interp} {els : Prop} {s : Store H} {f : Frame}
    {j i n : BitVec 32} {x : DataIdx} {am ad : Nat} {mi : MemInst} {di : DataInst}
    (ham : f.module.memAddr? memIdx0 = some am) (hm : s.memInst? am = some mi)
    (had : f.module.datas[x.toNat]? = some ad) (hd : s.datas[ad]? = some di)
    (hb : i.toNat + n.toNat ≤ di.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size) (w : Value) :
    ¬ RuleBody (simEnv20T B) D els [] [] "%~>%" memInitTrapRule
      (.tuple [configV hn ⟨s, f, initCode j i n x⟩, w]) := by
  intro hbody
  obtain ⟨ρ, hρ, fz, fj, fi, fn, fx, hdm, hdd, hG, hp⟩ :=
    memInitBodyT_parts hasRuleAt_memInitTrap hbody
  have hpr := ifBack hρ hG hp (List.mem_singleton_self _)
  have h₁ : EvalExp (E20 B) ρ (.cmpE .gtOp (.numT .natT)
      (.binE .addOp (.numT .natT) iPay (.varE "n")) (.lenE dataBytesE)) (.bool false) := by
    have h := evalExp_gtNat (evalExp_addNat20 (evalExp_iPay fi) (evalExp_var fn))
      (evalExp_dataLen20 (B := B) hdd fz fx had hd)
    rwa [show decide (di.bytes.size < i.toNat + n.toNat) = false by simp; omega] at h
  have h₂ : EvalExp (E20 B) ρ (.cmpE .gtOp (.numT .natT)
      (.binE .addOp (.numT .natT) jPay (.varE "n")) memLenE) (.bool false) := by
    have h := evalExp_gtNat (evalExp_addNat20 (evalExp_jPay fj) (evalExp_var fn))
      (evalExp_memLen20 (B := B) hdm fz ham hm)
    rwa [show decide (mi.bytes.size < j.toNat + n.toNat) = false by simp; omega] at h
  exact not_or_true h₁ h₂ hpr

/-- **Rule 45's body is refuted in `simEnv20T`** at a nonzero count. -/
theorem not_memInitZeroBodyT {D : Sim.Interp} {els : Prop} {s : Store H} {f : Frame}
    {j i n : BitVec 32} {x : DataIdx} (hn0 : n ≠ 0) (w : Value) :
    ¬ RuleBody (simEnv20T B) D els [] [] "%~>%" memInitZeroRule
      (.tuple [configV hn ⟨s, f, initCode j i n x⟩, w]) := by
  intro hbody
  obtain ⟨ρ, hρ, -, -, -, fn, -, -, -, hG, hp⟩ := memInitBodyT_parts hasRuleAt_memInitZero hbody
  exact hn0 (zero_of_prem fn (ifBack hρ hG hp (List.mem_cons_of_mem _ (List.mem_singleton_self _))))

/-! ## `otherwise` in `simEnv20T` -/

/-- **`otherwise` for rule 45 in `simEnv20T`**, where both bounds hold. -/
theorem otherwise45T {s : Store H} {f : Frame} {j i n : BitVec 32} {x : DataIdx} {am ad : Nat}
    {mi : MemInst} {di : DataInst} (ham : f.module.memAddr? memIdx0 = some am)
    (hm : s.memInst? am = some mi) (had : f.module.datas[x.toNat]? = some ad)
    (hd : s.datas[ad]? = some di)
    (hb : i.toNat + n.toNat ≤ di.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size) (w : Value) :
    otherwiseAt (simEnv20T B) "Step_read" [] 45
      (.tuple [configV hn ⟨s, f, initCode j i n x⟩, w]) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAtT_read (hasRuleAt_memInitTrap (B := B))
  refine otherwiseAt_of_table hrel (tags_of_take hrel readTagsT) (by decide)
    (lhsIn_initCode s f j i n x) (exc := [44]) (by decide) ?_
  intro k hk _ r hr w' hw
  obtain ⟨c', rfl⟩ := Whole.sameLhs_inv hw
  obtain rfl := List.mem_singleton.1 hk
  rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_memInitTrap) hr]
  exact not_memInitTrapBodyT ham hm had hd hb c'

/-- **`otherwise` for rule 46 in `simEnv20T`**, where both bounds hold and `n ≠ 0`. -/
theorem otherwise46T {s : Store H} {f : Frame} {j i n : BitVec 32} {x : DataIdx} {am ad : Nat}
    {mi : MemInst} {di : DataInst} (ham : f.module.memAddr? memIdx0 = some am)
    (hm : s.memInst? am = some mi) (had : f.module.datas[x.toNat]? = some ad)
    (hd : s.datas[ad]? = some di)
    (hb : i.toNat + n.toNat ≤ di.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size) (hn0 : n ≠ 0)
    (w : Value) :
    otherwiseAt (simEnv20T B) "Step_read" [] 46
      (.tuple [configV hn ⟨s, f, initCode j i n x⟩, w]) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAtT_read (hasRuleAt_memInitTrap (B := B))
  refine otherwiseAt_of_table hrel (tags_of_take hrel readTagsT) (by decide)
    (lhsIn_initCode s f j i n x) (exc := [44, 45]) (by decide) ?_
  intro k hk _ r hr w' hw
  obtain ⟨c', rfl⟩ := Whole.sameLhs_inv hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_memInitTrap) hr]
    exact not_memInitTrapBodyT ham hm had hd hb c'
  · rw [Whole.rule_of_hasRuleAt hrel (hasRuleAtT_read hasRuleAt_memInitZero) hr]
    exact not_memInitZeroBodyT hn0 c'

/-! ## The three rules fire -/

/-- A `memory.init` rule fires in `simEnv20T` from its right-hand side evaluated in `simEnv20`
and its premises in `simEnv20T`. -/
theorem firesT_memInit_of {k : Nat} {nm : IL.Id} {rhs : Exp} {prems : List Prem}
    (hR : HasRuleAt (E20 B) "Step_read" "%~>%" k
      (.ruleD nm memInitQs "%~>%" (.tupE [memInitLhs, rhs]) prems))
    {s : Store H} {f : Frame} {j i n : BitVec 32} {x : DataIdx} {W : Value}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (hr : EvalExp (E20 B) (VarEnv.empty.bindVals (memInitScope (hn := hn) s f j i n x)) rhs W)
    (hp : ∀ pr ∈ prems, PremW (simEnv20T B) (Sim.DDerives (simEnv20T B) (Sim.otherwise (simEnv20T B)))
      (Sim.otherwise (simEnv20T B) "Step_read" [] k
        (.tuple [configV hn ⟨s, f, initCode j i n x⟩, W]))
      (VarEnv.empty.bindVals (memInitScope (hn := hn) s f j i n x)) pr) :
    Fires (simEnv20T B) "Step_read" k (.tuple [configV hn ⟨s, f, initCode j i n x⟩, W]) := by
  have hρ := Pure.valsOnly_bindVals (memInitScope (hn := hn) s f j i n x)
  have hG := RelFree.goodEvs_of_all (readGood hR)
  have hGe : RelFree.GoodEvs RelFree.bad20 (evExp (.tupE [memInitLhs, rhs])) := by
    simp only [evRule, RelFree.goodEvs_append] at hG
    exact hG.1.2
  exact Pure.fires_of_ruleAt (hasRuleAtT_read hR) _ (quantsOkT_memInit hz)
    (StoreDeep.evalT_of_20 hρ hGe (evalExp_tup2 evalExp_memInitLhs hr)) hp

/-- **`Step_read/memory.init-trap` in `simEnv20T`.** -/
theorem firesT_memInitTrap {s : Store H} {f : Frame} {j i n : BitVec 32} {x : DataIdx}
    {am ad : Nat} {mi : MemInst} {di : DataInst}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ham : f.module.memAddr? memIdx0 = some am) (hm : s.memInst? am = some mi)
    (had : f.module.datas[x.toNat]? = some ad) (hd : s.datas[ad]? = some di)
    (hlt : di.bytes.size < i.toNat + n.toNat ∨ mi.bytes.size < j.toNat + n.toNat) :
    Fires (simEnv20T B) "Step_read" 44
      (.tuple [configV hn ⟨s, f, initCode j i n x⟩, .list (adminsToV [.trap])]) := by
  refine firesT_read_of20 (D := fun _ _ _ _ => True) (els := True) hasRuleAt_memInitTrap rfl
    (memInitScope (hn := hn) s f j i n x) (quantsOkT_memInit hz)
    (evalExp_tup2 evalExp_memInitLhs evalExp_trapRhs) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (Whole.evalExp_or
    (evalExp_gtNat (evalExp_addNat20 (evalExp_iPay rfl) (evalExp_var rfl))
      (evalExp_dataLen20 rfl rfl rfl had hd))
    (evalExp_gtNat (evalExp_addNat20 (evalExp_jPay rfl) (evalExp_var rfl))
      (evalExp_memLen20 rfl rfl ham hm))
    (by simpa using hlt))

/-- **`Step_read/memory.init-zero` in `simEnv20T`.** -/
theorem firesT_memInitZero {s : Store H} {f : Frame} {j i : BitVec 32} {x : DataIdx}
    {am ad : Nat} {mi : MemInst} {di : DataInst}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ham : f.module.memAddr? memIdx0 = some am) (hm : s.memInst? am = some mi)
    (had : f.module.datas[x.toNat]? = some ad) (hd : s.datas[ad]? = some di)
    (hb : i.toNat ≤ di.bytes.size ∧ j.toNat ≤ mi.bytes.size) :
    Fires (simEnv20T B) "Step_read" 45
      (.tuple [configV hn ⟨s, f, initCode j i 0 x⟩, .list (adminsToV [])]) := by
  refine firesT_memInit_of hasRuleAt_memInitZero hz Pure.evalExp_list0 ?_
  intro pr hpr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
  rcases hpr with rfl | rfl
  · exact .elsePr (otherwise45T ham hm had hd (by simpa using hb) _)
  · refine .ifPr (StoreDeep.evalT_of_20 (Pure.valsOnly_bindVals _)
      (RelFree.goodEvs_of_all (by decide)) ?_)
    exact evalExp_cmpE_iff.2 ⟨_, _, evalExp_var rfl, evalExp_numE_iff.2 rfl,
      cmpValues_eq_true_iff.2 rfl⟩

/-- **`Step_read/memory.init-succ` in `simEnv20T`**, where `j + 1` and `i + 1` do not wrap. -/
theorem firesT_memInitSucc {s : Store H} {f : Frame} {j i n : BitVec 32} {x : DataIdx}
    {am ad : Nat} {mi : MemInst} {di : DataInst} {b : UInt8}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ham : f.module.memAddr? memIdx0 = some am) (hm : s.memInst? am = some mi)
    (had : f.module.datas[x.toNat]? = some ad) (hd : s.datas[ad]? = some di)
    (hb : i.toNat + n.toNat ≤ di.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size) (hn0 : n ≠ 0)
    (hbyte : di.bytes.data[i.toNat]? = some b)
    (hj1 : j.toNat + 1 < 2 ^ 32) (hi1 : i.toNat + 1 < 2 ^ 32) :
    Fires (simEnv20T B) "Step_read" 46 (.tuple [configV hn ⟨s, f, initCode j i n x⟩,
      .list (adminsToV [constI32 j, constI32 (BitVec.ofNat 32 b.toNat), store8,
        constI32 (j + 1), constI32 (i + 1), constI32 (n - 1), .plain (.memoryInit x)])]) := by
  have hn1 : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
  rw [adminsToV_memoryInitSucc j i n b x hj1 hi1 hn0]
  refine firesT_memInit_of hasRuleAt_memInitSucc hz (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_constVar rfl)
    (evalExps_cons (evalExp_constPE (evalExp_dataByte20 rfl rfl rfl rfl had hd hbyte))
    (evalExps_cons (evalExp_store8 rfl)
    (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_jPay rfl) (evalExp_numE_iff.2 rfl)))
    (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_iPay rfl) (evalExp_numE_iff.2 rfl)))
    (evalExps_cons (evalExp_constPE (evalExp_pred hn1 rfl))
    (evalExps_cons (evalExp_case (evalExp_var rfl)) evalExps_nil)))))), rfl⟩) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .elsePr (otherwise46T ham hm had hd hb hn0 _)

end Silmaril.Wasm.SpecTec.Sim20.StoreBulk
