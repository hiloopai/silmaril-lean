module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFnGen

/-!
# The variable, reference, call and size rules in `simEnv20T`, from a state typed there

Each rule is fired by `firesT_of_parts`: the quantifiers typed in `simEnv20T` (the state by
hypothesis, the rest moved 's typings in `simEnv20`), the conclusion and the
premises evaluated 's lemmas in `simEnv20`.

* `Step_read` 7 `local.get`, 8 `global.get`, 6 `ref.func`, 2 `call` (`firesT_localGet`, …);
* `Step_read` 11 `table.size`, 36 `memory.size`, 9 and 10 `table.get` (`firesT_tableSize`, …);
* `Step` 4 `local.set` and 5 `global.set` of the original script, rules 5 and 6 of
  `simEnv20T` (`firesT_localSet`, `firesT_globalSet`), and as steps of `simEnv20T`
  (`sstepT_of_firesStep`).
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
open Silmaril.Wasm.SpecTec.Sim (TypedV QuantsOk ValsOnly Fires stateT evalExp_tup2 evalExp_case
  evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evRule)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-! ## Typings moved to `simEnv20T` -/

theorem typedT_idx {k : IndexKind} (x : Idx k) :
    TypedV (simEnv20T B) (.varT "idx" []) (idxV x) := typedT (by decide) (Whole.typedV_idx20 x)

theorem typedT_val (v : Val) : TypedV (simEnv20T B) (.varT "val" []) (valV v) :=
  typedT (by decide) (Whole.typedV_val20 v)

theorem typedT_n (k : Nat) : TypedV (simEnv20T B) (.varT "n" []) (.num (.natN k)) :=
  typedT (by decide) (Whole.typedV_n20 k)

theorem typedT_i32 (c : BitVec 32) :
    TypedV (simEnv20T B) (.varT "num_" [.expA (.caseE "I32" (.tupE []))]) (pctV c.toNat) :=
  typedT (by decide) ((Pure.numTyped_simEnv20 B).i32 c)

/-! ## One-instruction rules without premises -/

/-- **A one-instruction `Step_read` rule without premises fires in `simEnv20T`** at the image of
`s; f; [a]`, from a state typed there and its right-hand side evaluated in `simEnv20`. -/
theorem firesT_read1 {k : Nat} {nm : IL.Id} {op : MixopS} {rhs : Exp} {s : Store H} {f : Frame}
    {a : Admin} {X W : Value}
    (h : HasRuleAt (E20 B) "Step_read" "%~>%" k (.ruleD nm [.expP "z" stateT,
      .expP "x" (.varT "idx" [])] "%~>%"
      (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [.caseE op (.varE "x")]]), rhs]) []))
    (ha : adminToV a = .case op X)
    (hr : EvalExp (E20 B) (VarEnv.empty.bindVals [("z", stateV hn s f), ("x", X)]) rhs W)
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f)) (hx : TypedV (simEnv20T B) (.varT "idx" []) X) :
    Fires (simEnv20T B) "Step_read" k (.tuple [configV hn ⟨s, f, [a]⟩, W]) := by
  have hc : configV hn ⟨s, f, [a]⟩ = .case "%;%" (.tuple [stateV hn s f, .list [.case op X]]) := by
    rw [State.configV_single, ha]
  rw [hc]
  exact firesT_read_of20 h rfl [("z", stateV hn s f), ("x", X)]
    (QuantsOk.cons rfl (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hx _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var rfl)
      (evalExp_list1 (evalExp_case (evalExp_var rfl))))) hr) (D := fun _ _ _ _ => True) (els := True)
    Pure.prems_nil

/-- **`Step_read/local.get` in `simEnv20T`.** -/
theorem firesT_localGet {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (hv : f.locals[x.toNat]? = some v) (hz : TypedV (simEnv20T B) stateT (stateV hn s f)) :
    Fires (simEnv20T B) "Step_read" 7
      (.tuple [configV hn ⟨s, f, [.plain (.localGet x)]⟩, .list (adminsToV [v.toAdmin])]) := by
  have hw : Value.list (adminsToV [v.toAdmin]) = .list [valV v] := by
    show Value.list [adminToV v.toAdmin] = _
    rw [Pure.adminToV_toAdmin]
  rw [hw]
  exact firesT_read1 (B := B) (State.hasRuleAt_localGet B) rfl (evalExp_list1
    (evalExp_subE_iff.2 (State.evalExp_local20 B hn rfl (evalExp_var rfl) (evalExp_var rfl) hv)))
    hz (typedT_idx x)

/-- **`Step_read/global.get` in `simEnv20T`.** -/
theorem firesT_globalGet {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (ha : f.module.globals[x.toNat]? = some a) (hg : s.globals[a]? = some g)
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f)) :
    Fires (simEnv20T B) "Step_read" 8
      (.tuple [configV hn ⟨s, f, [.plain (.globalGet x)]⟩, .list (adminsToV [g.value.toAdmin])]) := by
  have hw : Value.list (adminsToV [g.value.toAdmin]) = .list [valV g.value] := by
    show Value.list [adminToV g.value.toAdmin] = _
    rw [Pure.adminToV_toAdmin]
  rw [hw]
  exact firesT_read1 (B := B) (State.hasRuleAt_globalGet B) rfl (evalExp_list1
    (evalExp_subE_iff.2 (evalExp_dotE_iff.2 ⟨globalInstV g,
      State.evalExp_global20 B hn rfl (evalExp_var rfl) (evalExp_var rfl) ha hg, rfl⟩))) hz
    (typedT_idx x)

/-- **`Step_read/ref.func` in `simEnv20T`.** -/
theorem firesT_refFunc {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat}
    (ha : f.module.funcs[x.toNat]? = some a) (hz : TypedV (simEnv20T B) stateT (stateV hn s f)) :
    Fires (simEnv20T B) "Step_read" 6
      (.tuple [configV hn ⟨s, f, [.plain (.refFunc x)]⟩, .list (adminsToV [.refFuncAddr a])]) :=
  firesT_read1 (B := B) (State.hasRuleAt_refFunc B) rfl (evalExp_list1 (evalExp_case
    (evalExp_idxE_iff.2 ⟨_, x.toNat, State.evalExp_funcaddr20 B hn rfl (evalExp_var rfl),
      Sim.State.evalExp_idxPayload rfl, by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩)))
    hz (typedT_idx x)

/-- **`Step_read/call` in `simEnv20T`.** -/
theorem firesT_call {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat}
    (ha : f.module.funcs[x.toNat]? = some a) (hz : TypedV (simEnv20T B) stateT (stateV hn s f)) :
    Fires (simEnv20T B) "Step_read" 2
      (.tuple [configV hn ⟨s, f, [.plain (.call x)]⟩, .list (adminsToV [.callAddr a])]) :=
  firesT_read1 (B := B) (State.hasRuleAt_call B) rfl (evalExp_list1 (evalExp_case
    (evalExp_idxE_iff.2 ⟨_, x.toNat, State.evalExp_funcaddr20 B hn rfl (evalExp_var rfl),
      Sim.State.evalExp_idxPayload rfl, by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩)))
    hz (typedT_idx x)

/-! ## Sizes and `table.get` -/

/-- **`Step_read/table.size` in `simEnv20T`.** -/
theorem firesT_tableSize {s : Store H} {f : Frame} {x : TableIdx} {ti : TableInst} {n : BitVec 32}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ht : (⟨s, f⟩ : State H).table? x = some ti) (hn' : ti.refs.length = n.toNat) :
    Fires (simEnv20T B) "Step_read" 11
      (.tuple [configV hn ⟨s, f, [.plain (.tableSize x)]⟩, .list (adminsToV [constI32 n])]) := by
  obtain ⟨a, ha, hti⟩ := Whole.table?_some ht
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("x", idxV x), ("n", .num (.natN n.toNat))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have hq : QuantsOk (simEnv20T B) (VarEnv.empty.bindVals σ)
      [.expP "z" (.varT "state" []), .expP "x" (.varT "idx" []), .expP "n" (.varT "n" [])] :=
    QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (typedT_idx x _ hρ)
      (QuantsOk.cons rfl (typedT_n _ _ hρ) QuantsOk.nil))
  have he : EvalExp (E20 B) (VarEnv.empty.bindVals σ)
      (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [.caseE "TABLE.SIZE" (.varE "x")]]),
        Whole.constNRhs])
      (.tuple [configV hn ⟨s, f, [.plain (.tableSize x)]⟩, .list (adminsToV [constI32 n])]) :=
    evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var rfl)
      (evalExp_list1 (evalExp_case (evalExp_var rfl)))))
      (evalExp_list1 (Whole.evalExp_constN rfl))
  have hpr : EvalExp (E20 B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT Whole.tableLenE (.varE "n")) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, Whole.evalExp_tableLen20 rfl rfl rfl ha hti, evalExp_var rfl,
      cmpValues_eq_true_iff.2 (by rw [hn'])⟩
  exact firesT_read_of20 Whole.hasRuleAt_tableSize rfl σ hq he (Pure.prems_one (.ifPr hpr))
    (D := fun _ _ _ _ => True) (els := True)

/-- **`Step_read/memory.size` in `simEnv20T`.** -/
theorem firesT_memorySize {s : Store H} {f : Frame} {mi : MemInst} {n : BitVec 32}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (hn' : n.toNat * Silmaril.Wasm.Execution.Memory.pageSize = mi.bytes.size) :
    Fires (simEnv20T B) "Step_read" 36
      (.tuple [configV hn ⟨s, f, [.plain .memorySize]⟩, .list (adminsToV [constI32 n])]) := by
  obtain ⟨a, ha, hmi⟩ := Whole.mem?_some hm
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("n", .num (.natN n.toNat))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have hq : QuantsOk (simEnv20T B) (VarEnv.empty.bindVals σ)
      [.expP "z" (.varT "state" []), .expP "n" (.varT "n" [])] :=
    QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (typedT_n _ _ hρ) QuantsOk.nil)
  have he : EvalExp (E20 B) (VarEnv.empty.bindVals σ)
      (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [.caseE "MEMORY.SIZE" (.tupE [])]]),
        Whole.constNRhs])
      (.tuple [configV hn ⟨s, f, [.plain .memorySize]⟩, .list (adminsToV [constI32 n])]) :=
    evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var rfl)
      (evalExp_list1 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)))))
      (evalExp_list1 (Whole.evalExp_constN rfl))
  have hsize : n.toNat * 64 * 1024 = mi.bytes.size := by
    rw [← hn']
    show n.toNat * 64 * 1024 = n.toNat * 65536
    omega
  have hpr : EvalExp (E20 B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.binE .mulOp (.numT .natT) (.binE .mulOp (.numT .natT) (.varE "n")
        (.numE (.natN 64))) (.callE "Ki" [])) (.lenE (.dotE Whole.mem0E "BYTES"))) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, CallIndGood.evalExp_pages rfl (Whole.evalExp_ki20 rfl),
      Whole.evalExp_memLen20 rfl rfl ha hmi, cmpValues_eq_true_iff.2 (by rw [hsize])⟩
  exact firesT_read_of20 Whole.hasRuleAt_memorySize rfl σ hq he (Pure.prems_one (.ifPr hpr))
    (D := fun _ _ _ _ => True) (els := True)

theorem quantsOkT_tableGet {s : Store H} {f : Frame} {i : BitVec 32} {x : TableIdx}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f)) :
    QuantsOk (simEnv20T B) (VarEnv.empty.bindVals (CallIndGood.tableGetScope (hn := hn) s f i x))
      [.expP "z" (.varT "state" []), .expP "i" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]),
        .expP "x" (.varT "idx" [])] := by
  have hρ := Pure.valsOnly_bindVals (CallIndGood.tableGetScope (hn := hn) s f i x)
  exact QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (typedT_i32 i _ hρ)
    (QuantsOk.cons rfl (typedT_idx x _ hρ) QuantsOk.nil))

/-- **`Step_read/table.get-trap` in `simEnv20T`.** -/
theorem firesT_tableGetTrap {s : Store H} {f : Frame} {x : TableIdx} {i : BitVec 32}
    {ti : TableInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ht : (⟨s, f⟩ : State H).table? x = some ti) (hge : ti.refs.length ≤ i.toNat) :
    Fires (simEnv20T B) "Step_read" 9 (.tuple [
      configV hn ⟨s, f, [constI32 i, .plain (.tableGet x)]⟩, .list (adminsToV [.trap])]) := by
  obtain ⟨a, ha, hti⟩ := Whole.table?_some ht
  refine firesT_read_of20 CallIndGood.hasRuleAt_tableGetTrap20 rfl
    (CallIndGood.tableGetScope (hn := hn) s f i x) (quantsOkT_tableGet hz)
    (evalExp_tup2 CallIndGood.evalExp_tableGetLhs Whole.evalExp_trapRhs)
    (Pure.prems_one (.ifPr ?_)) (D := fun _ _ _ _ => True) (els := True)
  exact evalExp_cmpNum (Whole.evalExp_iPay rfl) (Whole.evalExp_tableLen20 rfl rfl rfl ha hti)
    (by simpa [Num.cmp] using hge)

/-- **`Step_read/table.get-val` in `simEnv20T`.** -/
theorem firesT_tableGetVal {s : Store H} {f : Frame} {x : TableIdx} {i : BitVec 32}
    {ti : TableInst} {r : Ref} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ht : (⟨s, f⟩ : State H).table? x = some ti) (hr : ti.refs[i.toNat]? = some r) :
    Fires (simEnv20T B) "Step_read" 10 (.tuple [
      configV hn ⟨s, f, [constI32 i, .plain (.tableGet x)]⟩, .list (adminsToV [aref r])]) := by
  obtain ⟨a, ha, hti⟩ := Whole.table?_some ht
  have hlt : i.toNat < ti.refs.length := by
    rcases List.getElem?_eq_some_iff.1 hr with ⟨h, -⟩
    exact h
  have hres : adminsToV [aref r] = [refV r] :=
    congrArg (fun v => [v]) (Pure.adminToV_toAdmin (.ref r))
  rw [hres]
  refine firesT_read_of20 Whole.hasRuleAt_tableGetVal rfl
    (CallIndGood.tableGetScope (hn := hn) s f i x) (quantsOkT_tableGet hz)
    (evalExp_tup2 CallIndGood.evalExp_tableGetLhs (evalExp_list1 (evalExp_subE_iff.2
      (evalExp_idxE_iff.2 ⟨_, i.toNat, evalExp_dotE_iff.2 ⟨tableInstV ti,
        Whole.evalExp_table20 rfl (evalExp_var rfl) (evalExp_var rfl) ha hti, rfl⟩,
        Whole.evalExp_iPay rfl, by simp [Value.idx?, List.getElem?_map, hr]⟩))))
    (Pure.prems_one (.ifPr ?_)) (D := fun _ _ _ _ => True) (els := True)
  exact evalExp_cmpNum (Whole.evalExp_iPay rfl) (Whole.evalExp_tableLen20 rfl rfl rfl ha hti)
    (by simpa [Num.cmp] using hlt)

/-! ## `local.set`, `global.set` -/

/-- **`Step/local.set` in `simEnv20T`** (rule 5 there). -/
theorem firesT_localSet {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f)) (hlt : x.toNat < f.locals.length) :
    Fires (simEnv20T B) "Step" 5 (.tuple [configV hn ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩,
      configV hn ⟨s, f.setLocal x v, []⟩]) := by
  rw [State.configV_localSet]
  exact firesT_step_of20 (le_refl 4) (State.hasRuleAt_localSet B) rfl
    [("z", stateV hn s f), ("val", valV v), ("x", idxV x)]
    (QuantsOk.cons rfl (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (typedT_val v _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (typedT_idx x _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))
    (State.eval_localSet B hn rfl rfl rfl hlt) Pure.prems_nil (D := fun _ _ _ _ => True)
    (els := True)

/-- **`Step/global.set` in `simEnv20T`** (rule 6 there). -/
theorem firesT_globalSet {s : Store H} {f : Frame} {x : GlobalIdx} {v : Val} {a : Nat}
    {g : GlobalInst} (hz : TypedV (simEnv20T B) stateT (stateV hn s f))
    (ha : f.module.globals[x.toNat]? = some a) (hg : s.globals[a]? = some g) :
    Fires (simEnv20T B) "Step" 6 (.tuple [configV hn ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩,
      configV hn ⟨s.setGlobalInst a { g with value := v }, f, []⟩]) := by
  rw [State.configV_globalSet]
  exact firesT_step_of20 (by decide) (State.hasRuleAt_globalSet B) rfl
    [("z", stateV hn s f), ("val", valV v), ("x", idxV x)]
    (QuantsOk.cons rfl (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (typedT_val v _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (typedT_idx x _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))
    (State.eval_globalSet B hn rfl rfl rfl ha hg) Pure.prems_nil (D := fun _ _ _ _ => True)
    (els := True)

end Silmaril.Wasm.SpecTec.Sim20.StoreFn
