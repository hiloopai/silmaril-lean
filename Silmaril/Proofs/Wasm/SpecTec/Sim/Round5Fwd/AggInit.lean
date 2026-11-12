module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.AggData

/-!
# Round 5: `R4Fwd/InitData.lean` on bounded types

A copy of the aggregate lemmas of `R4Fwd/InitData.lean` that take `Aggregates.AggTypes`, each renamed with a
suffix `B`, taking `AggTypesB` (the bounded restatement) and a local instance
`Fact (Round4.ModuleBnd f.module)`; the bounds are discharged by `AggTypesB`'s auto-parameters.
The proofs are otherwise unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Fwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV mutV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open RefsGC

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty

variable {B : Builtins} {H : Type} {hn : H → String}

open R4Fwd

variable {env : Env} {B : Builtins} {H : Type} {hn : H → String} {P : Numerics.Profile}

/-- **`array.init_data-oob2` (`Step_read` rule 100), forward.** -/
theorem sread_arrayInitDataOob₂B (R : RTyping (simEnv B)) (A : AggTypesB (simEnv B))
    {s : Store H} {f : Frame} [Fact (Round4.ModuleBnd f.module)] {x : TypeIdx} {y : DataIdx} {i j n : BitVec 32} {a da : Nat}
    {d : DefType} {m : Mutability} {zt : CStorageType} {di : DataInst}
    (hd : f.type? x = some d) (he : Expand d (.array (.field m zt)))
    (hdat : s.data? f y = some (da, di)) (h0 : 0 < storageSize zt)
    (h : di.bytes.size < j.toNat + n.toNat * storageSize zt / 8)
    (hz : TypedV (simEnv B) stateT (stateV hn s f)) :
    SRead (simEnv B) (configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
      .plain (.arrayInitData x y)]⟩) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("i", pctV i.toNat), ("j", pctV j.toNat), ("n", .num (.natN n.toNat)),
    ("x", Encode.toValue x), ("y", Encode.toValue y), ("mut?", mutV m), ("zt", tyV zt)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hb := evalExp_initDataBound (B := B) hρ h0 hdat (by eval_tac) (by eval_tac) (by eval_tac)
    (by eval_tac) (by eval_tac)
  rw [decide_eq_true h] at hb
  exact dderives_of_ruleAt (Aggregates.rd B).arrayInitDataOob2 σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (R.i32 j _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.idx _ y.value.isLt _ hρ) (QuantsOk.cons rfl (A.mut_ m _ hρ)
      (QuantsOk.cons rfl (A.storagetype _ _ hρ) QuantsOk.nil)))))))))
    (by eval_tac)
    (prems_two (.rulePr evalArgs_nil (evalExp_expandArray hρ hd rfl rfl rfl rfl)
      (A.expand _ _ he)) (.ifPr hb))

set_option maxHeartbeats 400000 in
/-- **`array.init_data-num` (`Step_read` rule 102), forward.** -/
theorem sread_arrayInitDataNumB {P : Numerics.Profile} (hF : Floats.FloatB P B)
    (Z : ZBytes.ZB B) (XI : ExpandInv (simEnv B)) (LT : LitTyping (simEnv B))
    (R : RTyping (simEnv B)) (G : RStoreFuns (simEnv B)) (A : AggTypesB (simEnv B))
    {s : Store H} {f : Frame} [Fact (Round4.ModuleBnd f.module)] {x : TypeIdx} {y : DataIdx} {i j n : BitVec 32} {a da : Nat}
    {ai : ArrayInst} {d : DefType} {m : Mutability} {zt : CStorageType} {di : DataInst} {v : Val}
    (ha : s.arrays[a]? = some ai) (hd : f.type? x = some d)
    (he : Expand d (.array (.field m zt))) (hdat : s.data? f y = some (da, di))
    (h : i.toNat + n.toNat ≤ ai.fields.length ∧
      j.toNat + n.toNat * storageSize zt / 8 ≤ di.bytes.size)
    (hn0 : n ≠ 0) (hv : readField? zt di.bytes j.toNat = some v)
    (hb₁ : ai.fields.length < 2 ^ 32) (hb₂ : di.bytes.size < 2 ^ 32)
    (hz : TypedV (simEnv B) stateT (stateV hn s f)) :
    SRead (simEnv B) (configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
      .plain (.arrayInitData x y)]⟩)
      (adminsToV [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x),
        arrRef a, constI32 (i + 1), constI32 (j + BitVec.ofNat 32 (storageSize zt / 8)),
        constI32 (n - 1), .plain (.arrayInitData x y)]) := by
  have h0 := storageSize_pos_of_readField hv
  obtain ⟨k, hk, hjb, hsl, rfl⟩ := readField_spec hv
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("i", pctV i.toNat), ("j", pctV j.toNat), ("n", .num (.natN n.toNat)),
    ("x", Encode.toValue x), ("y", Encode.toValue y), ("zt", tyV zt), ("c", litV zt k),
    ("mut?", mutV m)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hl : LhsIn ["ARRAY.INIT_DATA", "REF.ARRAY_ADDR", "CONST"]
      (configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitData x y)]⟩) :=
    .inr ⟨_, _, rfl, tagsIn_cons (tag_case (by decide)) (tagsIn_cons (tag_case (by decide))
      (tagsIn_cons (tag_case (by decide)) (tagsIn_cons (tag_case (by decide))
      (tagsIn_cons (tag_case (by decide)) tagsIn_nil))))⟩
  have hel := otherwise_of_ruleAt (Aggregates.rd B).arrayInitDataNum (readTable_simEnv B)
    (i := 102) (b := .list (adminsToV [arrRef a, constI32 i, (fieldOfLit zt k).toAdmin,
        .plain (.arraySet x), arrRef a, constI32 (i + 1),
        constI32 (j + BitVec.ofNat 32 (storageSize zt / 8)), constI32 (n - 1),
        .plain (.arrayInitData x y)])) (by decide) (exc := [99, 100, 101]) hl (by decide) (by
      intro k' hk' _ r' hr' w hw
      obtain ⟨c, rfl⟩ := sameLhs_inv hw
      rcases (by simpa using hk' : k' = 99 ∨ k' = 100 ∨ k' = 101) with rfl | rfl | rfl
      · rw [relRules_of_ruleAt (Aggregates.rd B).arrayInitDataOob1 hr']
        exact not_arrayInitDataOob₁ G ha h.1
      · rw [relRules_of_ruleAt (Aggregates.rd B).arrayInitDataOob2 hr']
        exact not_arrayInitDataOob₂ XI hd he hdat h0 h.2
      · rw [relRules_of_ruleAt (Aggregates.rd B).arrayInitDataZero hr']
        exact not_arrayInitDataZero hn0)
  have hsz : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "zsize" [.expA (.varE "zt")]) .natT .ratT)
        (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT) (.num (.natN (storageSize zt / 8))) :=
    evalExp_divBy8 (dvd_storageSize zt h0) (Vec.evalExp_call (Aggregates.findDef_none hρ _)
      (evalArgs_cons (by eval_tac) evalArgs_nil) (applies_zsize zt h0))
  have hdata : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "data" [.expA (.varE "z"), .expA (.varE "y")])
      (Silmaril.SpecTec.Equiv.RuntimeBridge.dataInstToValue di) := by
    obtain ⟨M, Ls, As, a', hS, hM, hA, ha', hr⟩ := Memory.dataAt_of_data? hn hdat
    exact State.evalExp_data (State.stateDefs_simEnv B) (Aggregates.findDef_none hρ _)
      (by eval_tac) (by eval_tac) hS hM hA ha' hr
  have hif : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.callE "zbytes_" [.expA (.varE "zt"), .expA (.varE "c")])
        (.sliceE (.dotE (.callE "data" [.expA (.varE "z"), .expA (.varE "y")]) "BYTES")
          (.projE (.uncaseE (.varE "j") "%") 0)
          (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "zsize" [.expA (.varE "zt")]) .natT .ratT)
            (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))) (.bool true) :=
    evalExp_eq_true (Vec.evalExp_call (Aggregates.findDef_none hρ _)
      (evalArgs_cons (by eval_tac) (evalArgs_cons (by eval_tac) evalArgs_nil))
      (applies_zbytes Z h0 hk))
      (evalExp_sliceE_iff.2 ⟨_, _, _, evalExp_dot hdata (Memory.dataInstV_BYTES di),
        evalExp_unpct (by eval_tac), hsz, by
          rw [Equiv.ExecReadAggregate.slice?_list (by simpa using hjb), hsl]; rfl⟩)
  have hb₂' : j.toNat + storageSize zt / 8 < 2 ^ 32 := by
    have : storageSize zt / 8 ≤ n.toNat * storageSize zt / 8 := by
      have : n.toNat ≠ 0 := fun h' => hn0 (BitVec.eq_of_toNat_eq (by simpa using h'))
      exact Nat.div_le_div_right (Nat.le_mul_of_pos_left _ (by omega))
    omega
  have hi : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0) (.numE (.natN 1)))
      (.num (.natN (i + 1).toNat)) := by
    rw [FwdSimdAgg.toNat_succ h.1 hb₁ hn0]
    exact evalExp_addNat (evalExp_unpct (by eval_tac)) evalExp_num'
  have hj : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "j") "%") 0)
        (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "zsize" [.expA (.varE "zt")]) .natT .ratT)
          (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))
      (.num (.natN (j + BitVec.ofNat 32 (storageSize zt / 8)).toNat)) := by
    rw [toNat_add_ofNat hb₂']
    exact evalExp_addNat (evalExp_unpct (by eval_tac)) hsz
  have hn' : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE "n") .natT .intT)
        (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT) (.num (.natN (n - 1).toNat)) := by
    rw [toNat_sub_one hn0]
    exact evalExp_predNat (by eval_tac) (by
      have : n.toNat ≠ 0 := fun h' => hn0 (BitVec.eq_of_toNat_eq (by simpa using h'))
      omega)
  have hcst := evalExp_constField hF hρ h0 hk (by rfl) (by rfl)
  refine dderives_of_ruleAt (Aggregates.rd B).arrayInitDataNum σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (R.i32 j _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.idx _ y.value.isLt _ hρ) (QuantsOk.cons rfl (A.storagetype _ _ hρ)
      (QuantsOk.cons rfl (LT zt k _ hρ rfl h0 hk) (QuantsOk.cons rfl (A.mut_ m _ hρ)
        QuantsOk.nil))))))))))
    (evalExp_tup2 (by eval_tac) ?_)
    (Aggregates.prems_three (.elsePr hel) (.rulePr evalArgs_nil
      (evalExp_expandArray hρ hd rfl rfl rfl rfl) (A.expand _ _ he)) (.ifPr hif))
  have e₆ := evalExp_case (op := "CONST") (evalExp_tupE_of (evalExps_cons'
    (evalExp_case (op := "I32") (evalExp_tupE_of evalExps_nil')) (evalExps_cons'
      (evalExp_case (op := "%") (evalExp_tupE_of (evalExps_cons' hi evalExps_nil'))) evalExps_nil')))
  have e₇ := evalExp_case (op := "CONST") (evalExp_tupE_of (evalExps_cons'
    (evalExp_case (op := "I32") (evalExp_tupE_of evalExps_nil')) (evalExps_cons'
      (evalExp_case (op := "%") (evalExp_tupE_of (evalExps_cons' hj evalExps_nil'))) evalExps_nil')))
  have e₈ := evalExp_case (op := "CONST") (evalExp_tupE_of (evalExps_cons'
    (evalExp_case (op := "I32") (evalExp_tupE_of evalExps_nil')) (evalExps_cons'
      (evalExp_case (op := "%") (evalExp_tupE_of (evalExps_cons' hn' evalExps_nil'))) evalExps_nil')))
  have e₃ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "const" [.expA (.callE "cunpack" [.expA (.varE "zt")]),
        .expA (.callE "cunpacknum_" [.expA (.varE "zt"), .expA (.varE "c")])])
      (adminToV (fieldOfLit zt k).toAdmin) := by
    rw [adminToV_toAdmin]; exact hcst
  exact evalExp_listE_of (evalExps_cons' (by eval_tac) (evalExps_cons' (by eval_tac)
    (evalExps_cons' e₃ (evalExps_cons' (by eval_tac) (evalExps_cons' (by eval_tac)
    (evalExps_cons' e₆ (evalExps_cons' e₇ (evalExps_cons' e₈
    (evalExps_cons' (by eval_tac) evalExps_nil')))))))))

/-- **`array.init_data-num`, as a forward obligation** (bounded store). -/
theorem fwd_arrayInitDataNumB {P : Numerics.Profile} (hF : Floats.FloatB P B)
    (Z : ZBytes.ZB B) (XI : ExpandInv (simEnv B)) (LT : LitTyping (simEnv B))
    (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B)) (G : RStoreFuns (simEnv B))
    (A : AggTypesB (simEnv B))
    {s : Store H} {f : Frame} [Fact (Round4.ModuleBnd f.module)] {x : TypeIdx} {y : DataIdx} {i j n : BitVec 32} {a da : Nat}
    {ai : ArrayInst} {d : DefType} {ft : CFieldType} {di : DataInst} {v : Val}
    (hbd : Aggregates.Bounded s) (ha : s.arrays[a]? = some ai) (hd : f.type? x = some d)
    (he : Expand d (.array ft)) (hdat : s.data? f y = some (da, di))
    (h : i.toNat + n.toNat ≤ ai.fields.length ∧
      j.toNat + n.toNat * storageSize (fieldStorage ft) / 8 ≤ di.bytes.size)
    (hn0 : n ≠ 0) (hv : readField? (fieldStorage ft) di.bytes j.toNat = some v) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitData x y)]⟩
      ⟨s, f, [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x),
        arrRef a, constI32 (i + 1),
        constI32 (j + BitVec.ofNat 32 (storageSize (fieldStorage ft) / 8)),
        constI32 (n - 1), .plain (.arrayInitData x y)]⟩ := by
  obtain ⟨m, zt⟩ := ft
  refine RefsGC.fwd_of_sread T (hasStepRules_simEnv B).read fun hz _ => ?_
  exact sread_arrayInitDataNumB hF Z XI LT R G A ha hd he hdat h hn0 hv (hbd.array ha)
    (hbd.datas di (List.mem_of_getElem? (State.Store.data?_eq_some hdat).2)) hz

/-- **`array.init_data-oob2`, as a forward obligation.** -/
theorem fwd_arrayInitDataOob₂B (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B))
    (A : AggTypesB (simEnv B)) {s : Store H} {f : Frame} [Fact (Round4.ModuleBnd f.module)] {x : TypeIdx} {y : DataIdx}
    {i j n : BitVec 32} {a da : Nat} {d : DefType} {ft : CFieldType} {di : DataInst}
    (hd : f.type? x = some d) (he : Expand d (.array ft)) (hdat : s.data? f y = some (da, di))
    (h0 : 0 < storageSize (fieldStorage ft))
    (h : di.bytes.size < j.toNat + n.toNat * storageSize (fieldStorage ft) / 8) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitData x y)]⟩ ⟨s, f, [.trap]⟩ := by
  obtain ⟨m, zt⟩ := ft
  exact RefsGC.fwd_of_sread T (hasStepRules_simEnv B).read fun hz _ =>
    sread_arrayInitDataOob₂B R A hd he hdat h0 h hz

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd
