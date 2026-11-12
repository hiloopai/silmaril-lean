module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.RefsGC.Forward

/-!
# Family R: the aggregate rules, forward

Core's `AggregateStep` constructors as SpecTec steps of the images. This file covers the rules
that trap on a null reference (`Step_read` 70, 77, 80, 82, 86, 87, 93, 98; `Step` 30, 33).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.RefsGC

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.SpecTec.Equiv.ExecStepRules
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {env : Env} {H : Type} {hn : H → String}

/-- An encoded `Val.toAdmin` that is a typed instruction is a typed `val`. -/
theorem typed_toAdmin (R : RTyping env) (v : Val)
    (h : TypedV env instrsT (.list [adminToV v.toAdmin])) :
    TypedV env valT (adminToV v.toAdmin) := by
  rw [adminToV_toAdmin] at h ⊢
  exact R.val v h

/-- `structGetNull` (rule 70). -/
theorem sread_structGetNull (h : HasRuleAt env "Step_read" "%~>%" 70 structGetNullRule) (R : RTyping env)
    {s : Store H} {f : Frame} {sx : Option Signedness} {x : TypeIdx} {i : FieldIdx}
    (hz : TypedV env stateT (stateV hn s f))
    (_hc : TypedV env instrsT (.list (adminsToV [.ref .null, .plain (.structGet sx x i)]))) :
    SRead env (configV hn ⟨s, f, [.ref .null, .plain (.structGet sx x i)]⟩) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("sx?", .opt (sx.map sxV)), ("x", Encode.toValue x), ("i", Encode.toValue i)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  exact dderives_of_ruleAt h σ (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.sxOpt sx _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ) (QuantsOk.cons rfl (R.fieldidx _ i.value.isLt _ hρ) QuantsOk.nil))))
    (by eval_tac) (fun _ hp => nomatch hp)

/-- `arrayGetNull` (rule 77). -/
theorem sread_arrayGetNull (h : HasRuleAt env "Step_read" "%~>%" 77 arrayGetNullRule) (R : RTyping env)
    {s : Store H} {f : Frame} {sx : Option Signedness} {x : TypeIdx} {i : BitVec 32}
    (hz : TypedV env stateT (stateV hn s f))
    (_hc : TypedV env instrsT (.list (adminsToV [.ref .null, constI32 i, .plain (.arrayGet sx x)]))) :
    SRead env (configV hn ⟨s, f, [.ref .null, constI32 i, .plain (.arrayGet sx x)]⟩) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat), ("sx?", .opt (sx.map sxV)), ("x", Encode.toValue x)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  exact dderives_of_ruleAt h σ (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (R.sxOpt sx _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ) QuantsOk.nil))))
    (by eval_tac) (fun _ hp => nomatch hp)

/-- `arrayLenNull` (rule 80). -/
theorem sread_arrayLenNull (h : HasRuleAt env "Step_read" "%~>%" 80 arrayLenNullRule)
    {s : Store H} {f : Frame} 
    (hz : TypedV env stateT (stateV hn s f))
    (_hc : TypedV env instrsT (.list (adminsToV [.ref .null, .plain .arrayLen]))) :
    SRead env (configV hn ⟨s, f, [.ref .null, .plain .arrayLen]⟩) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  exact dderives_of_ruleAt h σ (QuantsOk.cons rfl (hz _ hρ) QuantsOk.nil)
    (by eval_tac) (fun _ hp => nomatch hp)

/-- `arrayFillNull` (rule 82). -/
theorem sread_arrayFillNull (h : HasRuleAt env "Step_read" "%~>%" 82 arrayFillNullRule) (T : TypingFacts env hn) (R : RTyping env)
    {s : Store H} {f : Frame} {x : TypeIdx} {i n : BitVec 32} {v : Val}
    (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref .null, constI32 i, v.toAdmin, constI32 n, .plain (.arrayFill x)]))) :
    SRead env (configV hn ⟨s, f, [.ref .null, constI32 i, v.toAdmin, constI32 n, .plain (.arrayFill x)]⟩) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat), ("val", adminToV v.toAdmin), ("n", .num (.natN n.toNat)), ("x", Encode.toValue x)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  exact dderives_of_ruleAt h σ (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (typed_toAdmin R v (typed_head T (typed_tail T (typed_tail T hc))) _ hρ) (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ) QuantsOk.nil)))))
    (by eval_tac) (fun _ hp => nomatch hp)

/-- `arrayCopyNull1` (rule 86). -/
theorem sread_arrayCopyNull₁ (h : HasRuleAt env "Step_read" "%~>%" 86 arrayCopyNull1Rule) (T : TypingFacts env hn) (R : RTyping env)
    {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32} {r : Ref}
    (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref .null, constI32 i₁, .ref r, constI32 i₂, constI32 n, .plain (.arrayCopy x₁ x₂)]))) :
    SRead env (configV hn ⟨s, f, [.ref .null, constI32 i₁, .ref r, constI32 i₂, constI32 n, .plain (.arrayCopy x₁ x₂)]⟩) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i_1", pctV i₁.toNat), ("ref", refToValue r), ("i_2", pctV i₂.toNat), ("n", .num (.natN n.toNat)), ("x_1", Encode.toValue x₁), ("x_2", Encode.toValue x₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  exact dderives_of_ruleAt h σ (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.i32 i₁ _ hρ) (QuantsOk.cons rfl (R.ref r (typed_head T (typed_tail T (typed_tail T hc))) _ hρ) (QuantsOk.cons rfl (R.i32 i₂ _ hρ) (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x₁.value.isLt _ hρ) (QuantsOk.cons rfl (R.idx _ x₂.value.isLt _ hρ) QuantsOk.nil)))))))
    (by eval_tac) (fun _ hp => nomatch hp)

/-- `arrayCopyNull2` (rule 87). -/
theorem sread_arrayCopyNull₂ (h : HasRuleAt env "Step_read" "%~>%" 87 arrayCopyNull2Rule) (T : TypingFacts env hn) (R : RTyping env)
    {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32} {r : Ref}
    (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref r, constI32 i₁, .ref .null, constI32 i₂, constI32 n, .plain (.arrayCopy x₁ x₂)]))) :
    SRead env (configV hn ⟨s, f, [.ref r, constI32 i₁, .ref .null, constI32 i₂, constI32 n, .plain (.arrayCopy x₁ x₂)]⟩) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("ref", refToValue r), ("i_1", pctV i₁.toNat), ("i_2", pctV i₂.toNat), ("n", .num (.natN n.toNat)), ("x_1", Encode.toValue x₁), ("x_2", Encode.toValue x₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  exact dderives_of_ruleAt h σ (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.ref r (typed_head T hc) _ hρ) (QuantsOk.cons rfl (R.i32 i₁ _ hρ) (QuantsOk.cons rfl (R.i32 i₂ _ hρ) (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x₁.value.isLt _ hρ) (QuantsOk.cons rfl (R.idx _ x₂.value.isLt _ hρ) QuantsOk.nil)))))))
    (by eval_tac) (fun _ hp => nomatch hp)

/-- `arrayInitElemNull` (rule 93). -/
theorem sread_arrayInitElemNull (h : HasRuleAt env "Step_read" "%~>%" 93 arrayInitElemNullRule) (R : RTyping env)
    {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx} {i j n : BitVec 32}
    (hz : TypedV env stateT (stateV hn s f))
    (_hc : TypedV env instrsT (.list (adminsToV [.ref .null, constI32 i, constI32 j, constI32 n, .plain (.arrayInitElem x y)]))) :
    SRead env (configV hn ⟨s, f, [.ref .null, constI32 i, constI32 j, constI32 n, .plain (.arrayInitElem x y)]⟩) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat), ("j", pctV j.toNat), ("n", .num (.natN n.toNat)), ("x", Encode.toValue x), ("y", Encode.toValue y)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  exact dderives_of_ruleAt h σ (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (R.i32 j _ hρ) (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ) (QuantsOk.cons rfl (R.idx _ y.value.isLt _ hρ) QuantsOk.nil))))))
    (by eval_tac) (fun _ hp => nomatch hp)

/-- `arrayInitDataNull` (rule 98). -/
theorem sread_arrayInitDataNull (h : HasRuleAt env "Step_read" "%~>%" 98 arrayInitDataNullRule) (R : RTyping env)
    {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx} {i j n : BitVec 32}
    (hz : TypedV env stateT (stateV hn s f))
    (_hc : TypedV env instrsT (.list (adminsToV [.ref .null, constI32 i, constI32 j, constI32 n, .plain (.arrayInitData x y)]))) :
    SRead env (configV hn ⟨s, f, [.ref .null, constI32 i, constI32 j, constI32 n, .plain (.arrayInitData x y)]⟩) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat), ("j", pctV j.toNat), ("n", .num (.natN n.toNat)), ("x", Encode.toValue x), ("y", Encode.toValue y)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  exact dderives_of_ruleAt h σ (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (R.i32 j _ hρ) (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ) (QuantsOk.cons rfl (R.idx _ y.value.isLt _ hρ) QuantsOk.nil))))))
    (by eval_tac) (fun _ hp => nomatch hp)

/-! ## Reading the array store -/

/-- The fields of `$arrayinst(z)[a]`. -/
theorem evalExp_arrayFields (G : RStoreFuns env) {ρ : VarEnv} {s : Store H} {f : Frame} {a : Nat}
    {ai : ArrayInst} (hvo : ValsOnly ρ) (hz : EvalExp env ρ (.varE "z") (stateV hn s f))
    {xa : IL.Id} (ha : EvalExp env ρ (.varE xa) (.num (.natN a))) (hai : s.arrays[a]? = some ai) :
    EvalExp env ρ (.dotE (.idxE (.callE "arrayinst" [.expA (.varE "z")]) (.varE xa)) "FIELDS")
      (.list (ai.fields.map fieldValV)) :=
  evalExp_dot (evalExp_idx (v := arrayInstV ai) (G.arrayinst hn ρ _ s f hvo hz) ha (by simp [hai])) rfl

/-- `arrayGetOob` (rule 78). -/
theorem sread_arrayGetOob (h₀ : HasRuleAt env "Step_read" "%~>%" 78 arrayGetOobRule) (R : RTyping env)
    (G : RStoreFuns env) {s : Store H} {f : Frame} {sx : Option Signedness} {x : TypeIdx} {i : BitVec 32} {a : Nat} {ai : ArrayInst}
    (ha : s.arrays[a]? = some ai) (h : ai.fields.length ≤ i.toNat)
    (hz : TypedV env stateT (stateV hn s f))
    (_hc : TypedV env instrsT (.list (adminsToV [arrRef a, constI32 i, .plain (.arrayGet sx x)]))) :
    SRead env (configV hn ⟨s, f, [arrRef a, constI32 i, .plain (.arrayGet sx x)]⟩) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)), ("i", pctV i.toNat), ("sx?", .opt (sx.map sxV)), ("x", Encode.toValue x)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  refine dderives_of_ruleAt h₀ σ (QuantsOk.cons rfl (hz _ hρ)
      (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ)
      (QuantsOk.cons rfl (R.sxOpt sx _ hρ)
      (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      QuantsOk.nil))))) (by eval_tac)
    (prems_one (.ifPr (evalExp_geNat (evalExp_unpct (by eval_tac))
      (evalExp_len (evalExp_arrayFields G (by exact ⟨rfl, rfl, rfl⟩) (by eval_tac) (by eval_tac) ha)) (by simpa using h))))

/-- `arrayLenArray` (rule 81). -/
theorem sread_arrayLenArray (h₀ : HasRuleAt env "Step_read" "%~>%" 81 arrayLenArrayRule) (R : RTyping env)
    (G : RStoreFuns env) {s : Store H} {f : Frame} {a : Nat} {ai : ArrayInst}
    (ha : s.arrays[a]? = some ai) (hlen : ai.fields.length < 2 ^ 32)
    (hz : TypedV env stateT (stateV hn s f))
    (_hc : TypedV env instrsT (.list (adminsToV [arrRef a, .plain .arrayLen]))) :
    SRead env (configV hn ⟨s, f, [arrRef a, .plain .arrayLen]⟩) (adminsToV [constI32 (BitVec.ofNat 32 ai.fields.length)]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  refine dderives_of_ruleAt h₀ σ (QuantsOk.cons rfl (hz _ hρ)
      (QuantsOk.cons rfl (R.addr _ _ hρ)
      QuantsOk.nil)) ?_ (fun _ hp => nomatch hp)
  have hl := evalExp_len (evalExp_arrayFields G (ρ := VarEnv.empty.bindVals σ) (by exact ⟨rfl, rfl, rfl⟩) (by eval_tac)
    (xa := "a") (by eval_tac) ha)
  rw [List.length_map] at hl
  have hb : (BitVec.ofNat 32 ai.fields.length).toNat = ai.fields.length := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hlen
  refine evalExp_tup2 (by eval_tac) (evalExp_list1 (evalExp_case (evalExp_tupE_of
    (evalExps_cons' (by eval_tac) (evalExps_cons' ?_ evalExps_nil')))))
  show EvalExp _ _ _ (pctV (BitVec.ofNat 32 ai.fields.length).toNat)
  rw [hb]
  exact evalExp_case (evalExp_tupE_of (evalExps_cons' hl evalExps_nil'))

/-- `arrayFillOob` (rule 83). -/
theorem sread_arrayFillOob (h₀ : HasRuleAt env "Step_read" "%~>%" 83 arrayFillOobRule) (T : TypingFacts env hn) (R : RTyping env)
    (G : RStoreFuns env) {s : Store H} {f : Frame} {x : TypeIdx} {i n : BitVec 32} {v : Val} {a : Nat} {ai : ArrayInst}
    (ha : s.arrays[a]? = some ai) (h : ai.fields.length < i.toNat + n.toNat)
    (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [arrRef a, constI32 i, v.toAdmin, constI32 n, .plain (.arrayFill x)]))) :
    SRead env (configV hn ⟨s, f, [arrRef a, constI32 i, v.toAdmin, constI32 n, .plain (.arrayFill x)]⟩) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)), ("i", pctV i.toNat), ("val", adminToV v.toAdmin), ("n", .num (.natN n.toNat)), ("x", Encode.toValue x)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  refine dderives_of_ruleAt h₀ σ (QuantsOk.cons rfl (hz _ hρ)
      (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ)
      (QuantsOk.cons rfl (typed_toAdmin R v (typed_head T (typed_tail T (typed_tail T hc))) _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ)
      (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      QuantsOk.nil)))))) (by eval_tac)
    (prems_one (.ifPr (evalExp_gtNat (evalExp_addNat (evalExp_unpct (by eval_tac)) (by eval_tac))
      (evalExp_len (evalExp_arrayFields G (by exact ⟨rfl, rfl, rfl⟩) (by eval_tac) (by eval_tac) ha)) (by simpa using h))))

/-- `arrayCopyOob1` (rule 88). -/
theorem sread_arrayCopyOob₁ (h₀ : HasRuleAt env "Step_read" "%~>%" 88 arrayCopyOob1Rule) (R : RTyping env)
    (G : RStoreFuns env) {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32} {a₁ a₂ : Nat} {ai₁ : ArrayInst}
    (ha : s.arrays[a₁]? = some ai₁) (h : ai₁.fields.length < i₁.toNat + n.toNat)
    (hz : TypedV env stateT (stateV hn s f))
    (_hc : TypedV env instrsT (.list (adminsToV [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n, .plain (.arrayCopy x₁ x₂)]))) :
    SRead env (configV hn ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n, .plain (.arrayCopy x₁ x₂)]⟩) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a_1", .num (.natN a₁)), ("i_1", pctV i₁.toNat), ("a_2", .num (.natN a₂)), ("i_2", pctV i₂.toNat), ("n", .num (.natN n.toNat)), ("x_1", Encode.toValue x₁), ("x_2", Encode.toValue x₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  refine dderives_of_ruleAt h₀ σ (QuantsOk.cons rfl (hz _ hρ)
      (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i₁ _ hρ)
      (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i₂ _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ)
      (QuantsOk.cons rfl (R.idx _ x₁.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.idx _ x₂.value.isLt _ hρ)
      QuantsOk.nil)))))))) (by eval_tac)
    (prems_one (.ifPr (evalExp_gtNat (evalExp_addNat (evalExp_unpct (by eval_tac)) (by eval_tac))
      (evalExp_len (evalExp_arrayFields G (by exact ⟨rfl, rfl, rfl⟩) (by eval_tac) (by eval_tac) ha)) (by simpa using h))))

/-- `arrayCopyOob2` (rule 89). -/
theorem sread_arrayCopyOob₂ (h₀ : HasRuleAt env "Step_read" "%~>%" 89 arrayCopyOob2Rule) (R : RTyping env)
    (G : RStoreFuns env) {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32} {a₁ a₂ : Nat} {ai₂ : ArrayInst}
    (ha : s.arrays[a₂]? = some ai₂) (h : ai₂.fields.length < i₂.toNat + n.toNat)
    (hz : TypedV env stateT (stateV hn s f))
    (_hc : TypedV env instrsT (.list (adminsToV [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n, .plain (.arrayCopy x₁ x₂)]))) :
    SRead env (configV hn ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n, .plain (.arrayCopy x₁ x₂)]⟩) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a_1", .num (.natN a₁)), ("i_1", pctV i₁.toNat), ("a_2", .num (.natN a₂)), ("i_2", pctV i₂.toNat), ("n", .num (.natN n.toNat)), ("x_1", Encode.toValue x₁), ("x_2", Encode.toValue x₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  refine dderives_of_ruleAt h₀ σ (QuantsOk.cons rfl (hz _ hρ)
      (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i₁ _ hρ)
      (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i₂ _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ)
      (QuantsOk.cons rfl (R.idx _ x₁.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.idx _ x₂.value.isLt _ hρ)
      QuantsOk.nil)))))))) (by eval_tac)
    (prems_one (.ifPr (evalExp_gtNat (evalExp_addNat (evalExp_unpct (by eval_tac)) (by eval_tac))
      (evalExp_len (evalExp_arrayFields G (by exact ⟨rfl, rfl, rfl⟩) (by eval_tac) (by eval_tac) ha)) (by simpa using h))))

/-- `arrayInitElemOob1` (rule 94). -/
theorem sread_arrayInitElemOob₁ (h₀ : HasRuleAt env "Step_read" "%~>%" 94 arrayInitElemOob1Rule) (R : RTyping env)
    (G : RStoreFuns env) {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx} {i j n : BitVec 32} {a : Nat} {ai : ArrayInst}
    (ha : s.arrays[a]? = some ai) (h : ai.fields.length < i.toNat + n.toNat)
    (hz : TypedV env stateT (stateV hn s f))
    (_hc : TypedV env instrsT (.list (adminsToV [arrRef a, constI32 i, constI32 j, constI32 n, .plain (.arrayInitElem x y)]))) :
    SRead env (configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n, .plain (.arrayInitElem x y)]⟩) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)), ("i", pctV i.toNat), ("j", pctV j.toNat), ("n", .num (.natN n.toNat)), ("x", Encode.toValue x), ("y", Encode.toValue y)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  refine dderives_of_ruleAt h₀ σ (QuantsOk.cons rfl (hz _ hρ)
      (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ)
      (QuantsOk.cons rfl (R.i32 j _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ)
      (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.idx _ y.value.isLt _ hρ)
      QuantsOk.nil))))))) (by eval_tac)
    (prems_one (.ifPr (evalExp_gtNat (evalExp_addNat (evalExp_unpct (by eval_tac)) (by eval_tac))
      (evalExp_len (evalExp_arrayFields G (by exact ⟨rfl, rfl, rfl⟩) (by eval_tac) (by eval_tac) ha)) (by simpa using h))))

/-- `arrayInitDataOob1` (rule 99). -/
theorem sread_arrayInitDataOob₁ (h₀ : HasRuleAt env "Step_read" "%~>%" 99 arrayInitDataOob1Rule) (R : RTyping env)
    (G : RStoreFuns env) {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx} {i j n : BitVec 32} {a : Nat} {ai : ArrayInst}
    (ha : s.arrays[a]? = some ai) (h : ai.fields.length < i.toNat + n.toNat)
    (hz : TypedV env stateT (stateV hn s f))
    (_hc : TypedV env instrsT (.list (adminsToV [arrRef a, constI32 i, constI32 j, constI32 n, .plain (.arrayInitData x y)]))) :
    SRead env (configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n, .plain (.arrayInitData x y)]⟩) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)), ("i", pctV i.toNat), ("j", pctV j.toNat), ("n", .num (.natN n.toNat)), ("x", Encode.toValue x), ("y", Encode.toValue y)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  refine dderives_of_ruleAt h₀ σ (QuantsOk.cons rfl (hz _ hρ)
      (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ)
      (QuantsOk.cons rfl (R.i32 j _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ)
      (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.idx _ y.value.isLt _ hρ)
      QuantsOk.nil))))))) (by eval_tac)
    (prems_one (.ifPr (evalExp_gtNat (evalExp_addNat (evalExp_unpct (by eval_tac)) (by eval_tac))
      (evalExp_len (evalExp_arrayFields G (by exact ⟨rfl, rfl, rfl⟩) (by eval_tac) (by eval_tac) ha)) (by simpa using h))))

/-! ## The trapping `Step` rules -/

/-- `struct.set-null` (`Step` rule 30), forward. -/
theorem fwd_structSetNull (h₀ : HasRuleAt env "Step" "%~>%" 30 structSetNullRule)
    (T : TypingFacts env hn) (R : RTyping env) {s : Store H} {f : Frame} {x : TypeIdx}
    {i : FieldIdx} {v : Val} :
    FwdP env hn ⟨s, f, [.ref .null, v.toAdmin, .plain (.structSet x i)]⟩ ⟨s, f, [.trap]⟩ := by
  intro hc _
  obtain ⟨hz, hcode⟩ := (T.config _).1 hc
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("val", adminToV v.toAdmin),
    ("x", Encode.toValue x), ("i", Encode.toValue i)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hv : TypedV env valT (adminToV v.toAdmin) := typed_toAdmin R v (typed_head T (typed_tail T hcode))
  exact dderives_of_ruleAt h₀ σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (hv _ hρ)
      (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.fieldidx _ i.value.isLt _ hρ) QuantsOk.nil))))
    (by eval_tac) (fun _ hp => nomatch hp)

/-- `array.set-null` (`Step` rule 33), forward. -/
theorem fwd_arraySetNull (h₀ : HasRuleAt env "Step" "%~>%" 33 arraySetNullRule)
    (T : TypingFacts env hn) (R : RTyping env) {s : Store H} {f : Frame} {x : TypeIdx}
    {i : BitVec 32} {v : Val} :
    FwdP env hn ⟨s, f, [.ref .null, constI32 i, v.toAdmin, .plain (.arraySet x)]⟩
      ⟨s, f, [.trap]⟩ := by
  intro hc _
  obtain ⟨hz, hcode⟩ := (T.config _).1 hc
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat),
    ("val", adminToV v.toAdmin), ("x", Encode.toValue x)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hv : TypedV env valT (adminToV v.toAdmin) :=
    typed_toAdmin R v (typed_head T (typed_tail T (typed_tail T hcode)))
  exact dderives_of_ruleAt h₀ σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.i32 i _ hρ)
      (QuantsOk.cons rfl (hv _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ) QuantsOk.nil))))
    (by eval_tac) (fun _ hp => nomatch hp)

/-- `array.set-oob` (`Step` rule 34), forward. -/
theorem fwd_arraySetOob (h₀ : HasRuleAt env "Step" "%~>%" 34 arraySetOobRule)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env) {s : Store H} {f : Frame}
    {x : TypeIdx} {i : BitVec 32} {v : Val} {a : Nat} {ai : ArrayInst}
    (ha : s.arrays[a]? = some ai) (h : ai.fields.length ≤ i.toNat) :
    FwdP env hn ⟨s, f, [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x)]⟩
      ⟨s, f, [.trap]⟩ := by
  intro hc _
  obtain ⟨hz, hcode⟩ := (T.config _).1 hc
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("i", pctV i.toNat), ("val", adminToV v.toAdmin), ("x", Encode.toValue x)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hv : TypedV env valT (adminToV v.toAdmin) :=
    typed_toAdmin R v (typed_head T (typed_tail T (typed_tail T hcode)))
  exact dderives_of_ruleAt h₀ σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (hv _ hρ)
      (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ) QuantsOk.nil)))))
    (by eval_tac)
    (prems_one (.ifPr (evalExp_geNat (evalExp_unpct (by eval_tac))
      (evalExp_len (evalExp_arrayFields G (by exact ⟨rfl, rfl, rfl⟩) (by eval_tac) (by eval_tac) ha)) (by simpa using h))))

end Silmaril.Wasm.SpecTec.Sim.RefsGC
