module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FwdSimdAgg.Copy

/-!
# Track `fwd-simd-agg`: `array.init_elem-succ`, and the forward obligations

`Step_read` 97, then `fwd_arrayCopyLe`, `fwd_arrayCopyGt`, `fwd_arrayInitElemSucc` as `FwdP`
obligations at `simEnv B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_nil)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV mutV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open RefsGC

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## `array.init_elem-succ` -/

/-- `array.init_elem-zero` does not fire for `n ≠ 0`. -/
theorem not_arrayInitElemZero {env : Env} {D : Interp} {els : Prop} {s : Store H} {f : Frame}
    {x : TypeIdx} {y : ElemIdx} {i j n : BitVec 32} {a : Nat} (hn0 : n ≠ 0) {c : Value} :
    ¬ RuleBody env D els [] [] "%~>%" arrayInitElemZeroRule
      (.tuple [configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitElem x y)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, -, -, he, hp⟩
  obtain ⟨-, hl⟩ := cfgz_inv (lhs_of_concl he)
  obtain ⟨-, -, -, hn', -⟩ := binds_arrayInitElem hl
  have hif := premW_if (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have h0 : Value.num (.natN n.toNat) = .num (.natN 0) := eq_of_evalExp_eq hif hn' evalExp_num'
  simp only [Value.num.injEq, Num.natN.injEq] at h0
  exact hn0 (BitVec.eq_of_toNat_eq (by simpa using h0))

/-- `array.init_elem-succ` (`Step_read` rule 97), forward, on a bounded store. -/
theorem sread_arrayInitElemSucc (R : RTyping (simEnv B)) (G : RStoreFuns (simEnv B))
    {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx} {i j n : BitVec 32} {a ea : Nat}
    {ai : ArrayInst} {ei : ElemInst} {r : Ref} (ha : s.arrays[a]? = some ai)
    (he : s.elem? f y = some (ea, ei))
    (h : i.toNat + n.toNat ≤ ai.fields.length ∧ j.toNat + n.toNat ≤ ei.refs.length)
    (hn0 : n ≠ 0) (hr : ei.refs[j.toNat]? = some r) (hb₁ : ai.fields.length < 2 ^ 32)
    (hb₂ : ei.refs.length < 2 ^ 32) (hz : TypedV (simEnv B) stateT (stateV hn s f)) :
    SRead (simEnv B) (configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
      .plain (.arrayInitElem x y)]⟩)
      (adminsToV [arrRef a, constI32 i, .ref r, .plain (.arraySet x),
        arrRef a, constI32 (i + 1), constI32 (j + 1), constI32 (n - 1),
        .plain (.arrayInitElem x y)]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("i", pctV i.toNat), ("j", pctV j.toNat), ("n", .num (.natN n.toNat)),
    ("x", Encode.toValue x), ("y", Encode.toValue y), ("ref", Equiv.RuntimeBridge.refToValue r)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hn₀ : n.toNat ≠ 0 := fun h' => hn0 (BitVec.eq_of_toNat_eq (by simpa using h'))
  have hl : LhsIn ["ARRAY.INIT_ELEM", "REF.ARRAY_ADDR", "CONST"]
      (configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitElem x y)]⟩) :=
    .inr ⟨_, _, rfl, tagsIn_cons (tag_case (by decide)) (tagsIn_cons (tag_case (by decide))
      (tagsIn_cons (tag_case (by decide)) (tagsIn_cons (tag_case (by decide))
      (tagsIn_cons (tag_case (by decide)) tagsIn_nil))))⟩
  have hel := otherwise_of_ruleAt (Aggregates.rd B).arrayInitElemSucc (readTable_simEnv B)
    (i := 97) (b := .list (adminsToV [arrRef a, constI32 i, .ref r, .plain (.arraySet x),
        arrRef a, constI32 (i + 1), constI32 (j + 1), constI32 (n - 1),
        .plain (.arrayInitElem x y)])) (by decide) (exc := [94, 95, 96]) hl (by decide) (by
      intro k hk _ r' hr' w hw
      obtain ⟨c, rfl⟩ := sameLhs_inv hw
      rcases (by simpa using hk : k = 94 ∨ k = 95 ∨ k = 96) with rfl | rfl | rfl
      · rw [relRules_of_ruleAt (Aggregates.rd B).arrayInitElemOob1 hr']
        exact not_arrayInitElemOob₁ G ha h.1
      · rw [relRules_of_ruleAt (Aggregates.rd B).arrayInitElemOob2 hr']
        exact not_arrayInitElemOob₂ G he h.2
      · rw [relRules_of_ruleAt (Aggregates.rd B).arrayInitElemZero hr']
        exact not_arrayInitElemZero hn0)
  have hi : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0) (.numE (.natN 1)))
      (.num (.natN (i + 1).toNat)) := by
    rw [toNat_succ h.1 hb₁ hn0]
    exact evalExp_addNat (evalExp_unpct (by eval_tac)) evalExp_num'
  have hj : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "j") "%") 0) (.numE (.natN 1)))
      (.num (.natN (j + 1).toNat)) := by
    rw [toNat_succ h.2 hb₂ hn0]
    exact evalExp_addNat (evalExp_unpct (by eval_tac)) evalExp_num'
  have hn' : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE "n") .natT .intT)
        (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT) (.num (.natN (n - 1).toNat)) := by
    rw [toNat_sub_one hn0]
    exact evalExp_predNat (by eval_tac) (by omega)
  have href : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.varE "ref") (.idxE (.dotE (.callE "elem" [.expA (.varE "z"),
        .expA (.varE "y")]) "REFS") (.projE (.uncaseE (.varE "j") "%") 0))) (.bool true) :=
    evalExp_eq_true (by eval_tac) (evalExp_idx (evalExp_elemRefs G hρ he (by eval_tac)
      (by eval_tac)) (evalExp_unpct (by eval_tac)) (by simp [hr]))
  refine dderives_of_ruleAt (Aggregates.rd B).arrayInitElemSucc σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (R.i32 j _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.idx _ y.value.isLt _ hρ)
      (QuantsOk.cons rfl (Typing.typedV_ref r _ hρ) QuantsOk.nil))))))))
    (evalExp_tup2 (by eval_tac) ?_) (prems_two (.elsePr hel) (.ifPr href))
  have e₆ := evalExp_case (op := "CONST") (evalExp_tupE_of (evalExps_cons'
    (evalExp_case (op := "I32") (evalExp_tupE_of evalExps_nil')) (evalExps_cons'
      (evalExp_case (op := "%") (evalExp_tupE_of (evalExps_cons' hi evalExps_nil'))) evalExps_nil')))
  have e₇ := evalExp_case (op := "CONST") (evalExp_tupE_of (evalExps_cons'
    (evalExp_case (op := "I32") (evalExp_tupE_of evalExps_nil')) (evalExps_cons'
      (evalExp_case (op := "%") (evalExp_tupE_of (evalExps_cons' hj evalExps_nil'))) evalExps_nil')))
  have e₈ := evalExp_case (op := "CONST") (evalExp_tupE_of (evalExps_cons'
    (evalExp_case (op := "I32") (evalExp_tupE_of evalExps_nil')) (evalExps_cons'
      (evalExp_case (op := "%") (evalExp_tupE_of (evalExps_cons' hn' evalExps_nil'))) evalExps_nil')))
  exact evalExp_listE_of (evalExps_cons' (by eval_tac) (evalExps_cons' (by eval_tac)
    (evalExps_cons' (evalExp_sub_of (by eval_tac)) (evalExps_cons' (by eval_tac)
    (evalExps_cons' (by eval_tac) (evalExps_cons' e₆ (evalExps_cons' e₇ (evalExps_cons' e₈
    (evalExps_cons' (by eval_tac) evalExps_nil')))))))))

/-! ## As forward obligations -/

/-- `array.copy-le`, as a forward obligation (unpacked frame, bounded store). -/
theorem fwd_arrayCopyLe (hV : VVB B) (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B))
    (G : RStoreFuns (simEnv B)) (A : Aggregates.AggTypes (simEnv B)) {s : Store H} {f : Frame}
    {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32} {a₁ a₂ : Nat} {ai₁ ai₂ : ArrayInst} {d₂ : DefType}
    {ft₂ : CFieldType} (hu : Aggregates.Unpacked f) (hbd : Aggregates.Bounded s)
    (ha₁ : s.arrays[a₁]? = some ai₁) (ha₂ : s.arrays[a₂]? = some ai₂)
    (h : i₁.toNat + n.toNat ≤ ai₁.fields.length ∧ i₂.toNat + n.toNat ≤ ai₂.fields.length)
    (hn0 : n ≠ 0) (hd : f.type? x₂ = some d₂) (he : Expand d₂ (.array ft₂))
    (hle : i₁.toNat ≤ i₂.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n,
      .plain (.arrayCopy x₁ x₂)]⟩
      ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂,
        .plain (.arrayGet (storageSx (fieldStorage ft₂)) x₂), .plain (.arraySet x₁),
        arrRef a₁, constI32 (i₁ + 1), arrRef a₂, constI32 (i₂ + 1), constI32 (n - 1),
        .plain (.arrayCopy x₁ x₂)]⟩ := by
  obtain ⟨m, t, rfl⟩ := hu.array hd he
  refine RefsGC.fwd_of_sread T (hasStepRules_simEnv B).read fun hz _ => ?_
  exact sread_arrayCopyLe (x₁ := x₁) (hn := hn) hV R G A ha₁ ha₂ h hn0 hd he hle (hbd.array ha₁) (hbd.array ha₂) hz

/-- `array.copy-gt`, as a forward obligation (unpacked frame, bounded store). -/
theorem fwd_arrayCopyGt (hV : VVB B) (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B))
    (G : RStoreFuns (simEnv B)) (A : Aggregates.AggTypes (simEnv B)) {s : Store H} {f : Frame}
    {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32} {a₁ a₂ : Nat} {ai₁ ai₂ : ArrayInst} {d₂ : DefType}
    {ft₂ : CFieldType} (hu : Aggregates.Unpacked f) (hbd : Aggregates.Bounded s)
    (ha₁ : s.arrays[a₁]? = some ai₁) (ha₂ : s.arrays[a₂]? = some ai₂)
    (h : i₁.toNat + n.toNat ≤ ai₁.fields.length ∧ i₂.toNat + n.toNat ≤ ai₂.fields.length)
    (hn0 : n ≠ 0) (hd : f.type? x₂ = some d₂) (he : Expand d₂ (.array ft₂))
    (hgt : i₂.toNat < i₁.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n,
      .plain (.arrayCopy x₁ x₂)]⟩
      ⟨s, f, [arrRef a₁, constI32 (i₁ + n - 1), arrRef a₂, constI32 (i₂ + n - 1),
        .plain (.arrayGet (storageSx (fieldStorage ft₂)) x₂), .plain (.arraySet x₁),
        arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 (n - 1),
        .plain (.arrayCopy x₁ x₂)]⟩ := by
  obtain ⟨m, t, rfl⟩ := hu.array hd he
  refine RefsGC.fwd_of_sread T (hasStepRules_simEnv B).read fun hz _ => ?_
  exact sread_arrayCopyGt (x₁ := x₁) (hn := hn) hV R G A ha₁ ha₂ h hn0 hd he hgt (hbd.array ha₁) (hbd.array ha₂) hz

/-- `array.init_elem-succ`, as a forward obligation (bounded store). -/
theorem fwd_arrayInitElemSucc (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B))
    (G : RStoreFuns (simEnv B)) {s : Store H} {f : Frame}
    {x : TypeIdx} {y : ElemIdx} {i j n : BitVec 32} {a ea : Nat} {ai : ArrayInst} {ei : ElemInst}
    {r : Ref} (hbd : Aggregates.Bounded s) (ha : s.arrays[a]? = some ai)
    (he : s.elem? f y = some (ea, ei))
    (h : i.toNat + n.toNat ≤ ai.fields.length ∧ j.toNat + n.toNat ≤ ei.refs.length)
    (hn0 : n ≠ 0) (hr : ei.refs[j.toNat]? = some r) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
      .plain (.arrayInitElem x y)]⟩
      ⟨s, f, [arrRef a, constI32 i, .ref r, .plain (.arraySet x),
        arrRef a, constI32 (i + 1), constI32 (j + 1), constI32 (n - 1),
        .plain (.arrayInitElem x y)]⟩ := by
  refine RefsGC.fwd_of_sread T (hasStepRules_simEnv B).read fun hz _ => ?_
  exact sread_arrayInitElemSucc (x := x) (hn := hn) R G ha he h hn0 hr (hbd.array ha)
      (hbd.elems ei (List.mem_of_getElem? (State.Store.elem?_eq_some he).2)) hz

end Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg
