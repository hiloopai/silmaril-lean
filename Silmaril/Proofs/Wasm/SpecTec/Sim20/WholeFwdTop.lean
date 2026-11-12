module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdGrow

/-!
# The restricted forward 2.0 half, widened to the table and drop rules

`WholeFwdGrow` proves the forward half on V2's four growth steps. The same method covers four
more `Step` rules that the script applies at the top of the code with no structural rule:
`table.set-trap` (6), `table.set-val` (7), `elem.drop` (10) and `data.drop` (21).

* `fires_tableSetTrap`, `fires_tableSetVal`, `fires_elemDrop`, `fires_dataDrop`: each fires from
  the image of V2's left-hand side to the image of V2's successor, at any builtins, from a typed
  state. The `i : num_(I32)` quantifier is typed by `numTyped_simEnv20`, the reference and index
  as in `WholeGrowTyping`.
* `TopStep20 P`: the growth steps and V2's `tableSetTrap`, `tableSetVal`, `elemDrop`,
  `dataDrop`, with V2's premises (`TopStep20.step` embeds it in `Step`).
* **`Task.wholeStepTop20`** (proved, `wholeStepTop20`): `Task.wholeStepGrow20` with `TopStep20`
  for `GrowStep20`.

Not covered, and why:
* `local.set` (4) and `global.set` (5) quantify a `val`; the forward firing needs the IL typing
  of every V2 value, which is not proved for `simEnv20` (only its inversion, `valHead_of_typed`).
* The `store`/`vstore` rules (11–18): `STORE` and `VEXTRACT_LANE` have no IL type in the 2.0
  script (track F2's upstream note 1), so their configurations are never typed and the forward
  statement would be vacuous there; the `VSTORE` rules are not attempted.
* Every rule reached through `Step/pure`, `Step/read`, `ctxt-label`, `ctxt-frame`: these are the
  structural obstructions (`not_wholeStepValid`, `not_fwd_noCtxt`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV ValsOnly stateT QuantsOk evalExp_tup2 evalExp_case
  evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Left-hand sides -/

/-- `CONST I32 i` at `i` bound to the constant's image. -/
theorem evalExp_constIE {env : Env} {ρ : VarEnv} {c : BitVec 32}
    (fi : ρ.findVal? "i" = some (pctV c.toNat)) :
    EvalExp env ρ constIE (adminToV (constI32 c)) :=
  evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
    (evalExp_var fi))

/-- `z; CONST I32 i ref TABLE.SET x`, the left-hand side of rules 6 and 7. -/
theorem evalExp_tableSetLhs {env : Env} {ρ : VarEnv} {s : Store H} {f : Frame} {x : TableIdx}
    {c : BitVec 32} {r : Ref} (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fi : ρ.findVal? "i" = some (pctV c.toNat)) (fr : ρ.findVal? "ref" = some (refV r))
    (fx : ρ.findVal? "x" = some (idxV x)) :
    EvalExp env ρ (.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
      .subE (.varE "ref") (.varT "ref" []) (.varT "admininstr" []),
      .caseE "TABLE.SET" (.varE "x")]]))
      (configV hn ⟨s, f, [constI32 c, aref r, .plain (.tableSet x)]⟩) := by
  have hr : adminToV (aref r) = refV r := Pure.adminToV_toAdmin (.ref r)
  refine evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_constIE fi) (evalExps_cons (evalExp_subE_iff.2 (evalExp_var fr))
      (evalExps_cons (evalExp_case (evalExp_var fx)) evalExps_nil)), ?_⟩))
  simp only [adminsToV, hr]
  rfl

/-- The scope of rules 6 and 7. -/
abbrev tableSetScope (s : Store H) (f : Frame) (c : BitVec 32) (r : Ref) (x : TableIdx) :
    List (IL.Id × Value) :=
  [("z", stateV hn s f), ("i", pctV c.toNat), ("ref", refV r), ("x", idxV x)]

/-- Rules 6 and 7 have their quantifiers typed at `tableSetScope`. -/
theorem quantsOk_tableSet {s : Store H} {f : Frame} {c : BitVec 32} {r : Ref} {x : TableIdx}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f)) :
    QuantsOk (simEnv20 B) (VarEnv.empty.bindVals (tableSetScope (hn := hn) s f c r x))
      [.expP "z" (.varT "state" []), .expP "i" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]),
        .expP "ref" (.varT "ref" []), .expP "x" (.varT "idx" [])] := by
  have hρ := Pure.valsOnly_bindVals (tableSetScope (hn := hn) s f c r x)
  exact QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 c _ hρ)
    (QuantsOk.cons rfl (typedV_ref20 r _ hρ) (QuantsOk.cons rfl (typedV_idx20 x _ hρ)
      QuantsOk.nil)))

/-! ## The four rules, forward -/

/-- **`Step/table.set-trap` fires forward** at the image of V2's `tableSetTrap`. -/
theorem fires_tableSetTrap {s : Store H} {f : Frame} {x : TableIdx} {c : BitVec 32} {r : Ref}
    {a : Nat} {ti : TableInst} (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ha : f.module.tables[x.toNat]? = some a) (ht : s.tables[a]? = some ti)
    (hge : ti.refs.length ≤ c.toNat) :
    Fires (simEnv20 B) "Step" 6 (.tuple [
      configV hn ⟨s, f, [constI32 c, aref r, .plain (.tableSet x)]⟩, configV hn ⟨s, f, [.trap]⟩]) := by
  let σ := tableSetScope (hn := hn) s f c r x
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV c.toNat) := rfl
  have fr : (VarEnv.empty.bindVals σ).findVal? "ref" = some (refV r) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) := rfl
  refine Pure.fires_of_ruleAt hasRuleAt_tableSetTrap σ (quantsOk_tableSet hz)
    (evalExp_tup2 (evalExp_tableSetLhs fz fi fr fx) (evalExp_case (evalExp_tup2 (evalExp_var fz)
      (evalExp_list1 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)))))) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  refine .ifPr (evalExp_cmpNum (evalExp_iPay fi) (evalExp_tableLen20 rfl fz fx ha ht) ?_)
  simpa [Num.cmp] using hge

/-- **`Step/table.set-val` fires forward** at the image of V2's `tableSetVal`. -/
theorem fires_tableSetVal {s : Store H} {f : Frame} {x : TableIdx} {c : BitVec 32} {r : Ref}
    {a : Nat} {ti : TableInst} (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ha : f.module.tables[x.toNat]? = some a) (ht : s.tables[a]? = some ti)
    (hlt : c.toNat < ti.refs.length) :
    Fires (simEnv20 B) "Step" 7 (.tuple [
      configV hn ⟨s, f, [constI32 c, aref r, .plain (.tableSet x)]⟩,
      configV hn ⟨s.setTableInst a (ti.setRef c.toNat r), f, []⟩]) := by
  let σ := tableSetScope (hn := hn) s f c r x
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV c.toNat) := rfl
  have fr : (VarEnv.empty.bindVals σ).findVal? "ref" = some (refV r) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) := rfl
  refine Pure.fires_of_ruleAt hasRuleAt_tableSetVal σ (quantsOk_tableSet hz)
    (evalExp_tup2 (evalExp_tableSetLhs fz fi fr fx) (evalExp_case (evalExp_tup2
      (evalExp_withTable20 rfl (evalExp_var fz) (evalExp_var fx) (evalExp_iPay fi)
        (evalExp_var fr) ha ht hlt) Pure.evalExp_list0))) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  refine .ifPr (evalExp_cmpNum (evalExp_iPay fi) (evalExp_tableLen20 rfl fz fx ha ht) ?_)
  simpa [Num.cmp] using hlt

/-- **`Step/elem.drop` fires forward** at the image of V2's `elemDrop`. -/
theorem fires_elemDrop {s : Store H} {f : Frame} {x : ElemIdx} {a : Nat} {ei : ElemInst}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ha : f.module.elems[x.toNat]? = some a) (he : s.elems[a]? = some ei) :
    Fires (simEnv20 B) "Step" 10 (.tuple [configV hn ⟨s, f, [.plain (.elemDrop x)]⟩,
      configV hn ⟨s.setElemInst a { ei with refs := [] }, f, []⟩]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("x", idxV x)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) := rfl
  exact Pure.fires_of_ruleAt hasRuleAt_elemDrop σ
    (QuantsOk.cons fz (hz _ hρ) (QuantsOk.cons fx (typedV_idx20 x _ hρ) QuantsOk.nil))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
      (evalExp_list1 (evalExp_case (evalExp_var fx)))))
      (evalExp_case (evalExp_tup2 (evalExp_withElem20 rfl (evalExp_var fz) (evalExp_var fx) ha he)
        Pure.evalExp_list0))) Pure.prems_nil

/-- **`Step/data.drop` fires forward** at the image of V2's `dataDrop`. -/
theorem fires_dataDrop {s : Store H} {f : Frame} {x : DataIdx} {a : Nat} {di : DataInst}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ha : f.module.datas[x.toNat]? = some a) (hd : s.datas[a]? = some di) :
    Fires (simEnv20 B) "Step" 21 (.tuple [configV hn ⟨s, f, [.plain (.dataDrop x)]⟩,
      configV hn ⟨s.setDataInst a ⟨ByteArray.empty⟩, f, []⟩]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("x", idxV x)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) := rfl
  exact Pure.fires_of_ruleAt hasRuleAt_dataDrop σ
    (QuantsOk.cons fz (hz _ hρ) (QuantsOk.cons fx (typedV_idx20 x _ hρ) QuantsOk.nil))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
      (evalExp_list1 (evalExp_case (evalExp_var fx)))))
      (evalExp_case (evalExp_tup2 (evalExp_withData20 rfl (evalExp_var fz) (evalExp_var fx) ha hd)
        Pure.evalExp_list0))) Pure.prems_nil

/-! ## The fragment and the target -/

/-- **The top-level store steps of V2 the forward half covers**: the growth steps, and V2's
`tableSetTrap`, `tableSetVal`, `elemDrop` and `dataDrop`, with their premises. -/
inductive TopStep20 (P : Profile) : Config H → Config H → Prop where
  | grow {c c' : Config H} (h : GrowStep20 P c c') : TopStep20 P c c'
  | tableSetTrap {s : Store H} {f : Frame} {x : TableIdx} {i : BitVec 32} {r : Ref}
      {a : TableAddr} {ti : TableInst} (ha : f.module.tableAddr? x = some a)
      (ht : s.tableInst? a = some ti) (h : ti.refs.length ≤ i.toNat) :
      TopStep20 P ⟨s, f, [constI32 i, aref r, .plain (.tableSet x)]⟩ ⟨s, f, [.trap]⟩
  | tableSetVal {s : Store H} {f : Frame} {x : TableIdx} {i : BitVec 32} {r : Ref}
      {a : TableAddr} {ti : TableInst} (ha : f.module.tableAddr? x = some a)
      (ht : s.tableInst? a = some ti) (h : i.toNat < ti.refs.length) :
      TopStep20 P ⟨s, f, [constI32 i, aref r, .plain (.tableSet x)]⟩
        ⟨s.setTableInst a (ti.setRef i.toNat r), f, []⟩
  | elemDrop {s : Store H} {f : Frame} {x : ElemIdx} {a : ElemAddr} {ei : ElemInst}
      (ha : f.module.elemAddr? x = some a) (he : s.elemInst? a = some ei) :
      TopStep20 P ⟨s, f, [.plain (.elemDrop x)]⟩ ⟨s.setElemInst a { ei with refs := [] }, f, []⟩
  | dataDrop {s : Store H} {f : Frame} {x : DataIdx} {a : DataAddr} {di : DataInst}
      (ha : f.module.dataAddr? x = some a) (hd : s.dataInst? a = some di) :
      TopStep20 P ⟨s, f, [.plain (.dataDrop x)]⟩ ⟨s.setDataInst a ⟨ByteArray.empty⟩, f, []⟩

/-- Every step of the fragment is a V2 step. -/
theorem TopStep20.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : TopStep20 P c c') : Step P host c c' := by
  cases h with
  | grow h => exact h.step
  | tableSetTrap ha ht h => exact .tableSetTrap ha ht h
  | tableSetVal ha ht h => exact .tableSetVal ha ht h
  | elemDrop ha he => exact .elemDrop ha he
  | dataDrop ha hd => exact .dataDrop ha hd

/-- **The forward half on the fragment**, at builtins answering V2's growth. -/
theorem fwd_topStep20 {P : Profile} (hG : GrowCalls20 B) {c c' : Config H}
    (hc : Typed20 (simEnv20 B) hn c) (hw : WholePages c.store) (h : TopStep20 P c c') :
    SStepB (simEnv20 B) (configV hn c) (configV hn c') := by
  have hz := typedV_state_of_typed20 hc
  cases h with
  | grow h => exact fwd_growStep20 hG hc hw h
  | tableSetTrap ha ht h => exact sstepB_of_fires20 (fires_tableSetTrap hz ha ht h)
  | tableSetVal ha ht h => exact sstepB_of_fires20 (fires_tableSetVal hz ha ht h)
  | elemDrop ha he => exact sstepB_of_fires20 (fires_elemDrop hz ha he)
  | dataDrop ha hd => exact sstepB_of_fires20 (fires_dataDrop hz ha hd)

/-- **`Task.wholeStepGrow20` on the wider fragment** (proved below). -/
def Task.wholeStepTop20 : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
      GrowLike20 (Profile.spec nd r) B ∧
      (∀ c c' : Config H, Typed20 (simEnv20 B) hn c → WholePages c.store →
        TopStep20 (Profile.spec nd r) c c' →
        SStepB (simEnv20 B) (configV hn c) (configV hn c')) ∧
      (∀ (c : Config H) (w : Value), GoodW c → SStepB (simEnv20 B) (configV hn c) w →
        ∃ c', w = configV hn c' ∧ Step (Profile.spec nd r) host c c')

/-- **`Task.wholeStepTop20` holds**, at `growB`. -/
theorem wholeStepTop20 : Task.wholeStepTop20 := by
  intro H hn _ host nd r
  refine ⟨growB (Profile.spec nd r), growLike20_growB _, fun c c' hc hw h => ?_,
    fun c w hg hs => wholeStepBwdW_growB nd r c w hg hs⟩
  exact fwd_topStep20 (growCalls20_growB _) hc hw h

end Silmaril.Wasm.SpecTec.Sim20.Whole
