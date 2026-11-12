module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FwdSimdAgg.CopyPrems

/-!
# Track `fwd-simd-agg`: `array.copy-le`, `array.copy-gt`, forward (`Step_read` 91, 92)

See `CopyPrems.lean` for the `otherwise` refutations and `$sx`.
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

/-- `array.copy-le` (`Step_read` rule 91), forward, for an unpacked source element type. -/
theorem sread_arrayCopyLe (hV : VVB B) (R : RTyping (simEnv B)) (G : RStoreFuns (simEnv B))
    (A : Aggregates.AggTypes (simEnv B)) {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx}
    {i₁ i₂ n : BitVec 32} {a₁ a₂ : Nat} {ai₁ ai₂ : ArrayInst} {d₂ : DefType} {m : Mutability}
    {t : CValType} (ha₁ : s.arrays[a₁]? = some ai₁) (ha₂ : s.arrays[a₂]? = some ai₂)
    (h : i₁.toNat + n.toNat ≤ ai₁.fields.length ∧ i₂.toNat + n.toNat ≤ ai₂.fields.length)
    (hn0 : n ≠ 0) (hd : f.type? x₂ = some d₂) (he : Expand d₂ (.array (.field m (.val t))))
    (hle : i₁.toNat ≤ i₂.toNat) (hb₁ : ai₁.fields.length < 2 ^ 32)
    (hb₂ : ai₂.fields.length < 2 ^ 32) (hz : TypedV (simEnv B) stateT (stateV hn s f)) :
    SRead (simEnv B) (configV hn ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂,
      constI32 n, .plain (.arrayCopy x₁ x₂)]⟩)
      (adminsToV [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂,
        .plain (.arrayGet none x₂), .plain (.arraySet x₁),
        arrRef a₁, constI32 (i₁ + 1), arrRef a₂, constI32 (i₂ + 1), constI32 (n - 1),
        .plain (.arrayCopy x₁ x₂)]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a_1", .num (.natN a₁)),
    ("i_1", pctV i₁.toNat), ("a_2", .num (.natN a₂)), ("i_2", pctV i₂.toNat),
    ("n", .num (.natN n.toNat)), ("x_1", Encode.toValue x₁), ("x_2", Encode.toValue x₂),
    ("sx?", .opt none), ("mut?", mutV m), ("zt_2", tyV (Ty.val t : CStorageType))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hn₀ : n.toNat ≠ 0 := fun h' => hn0 (BitVec.eq_of_toNat_eq (by simpa using h'))
  have hel := otherwise_of_ruleAt (Aggregates.rd B).arrayCopyLe (readTable_simEnv B) (i := 91)
    (b := .list (adminsToV [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂,
        .plain (.arrayGet none x₂), .plain (.arraySet x₁),
        arrRef a₁, constI32 (i₁ + 1), arrRef a₂, constI32 (i₂ + 1), constI32 (n - 1),
        .plain (.arrayCopy x₁ x₂)])) (by decide) (exc := [88, 89, 90])
    (lhsIn_arrayCopy (hn := hn) (s := s) (f := f) (x₁ := x₁) (x₂ := x₂) (i₁ := i₁) (i₂ := i₂)
      (n := n) (a₁ := a₁) (a₂ := a₂)) (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := sameLhs_inv hw
      rcases (by simpa using hj : j = 88 ∨ j = 89 ∨ j = 90) with rfl | rfl | rfl
      · rw [relRules_of_ruleAt (Aggregates.rd B).arrayCopyOob1 hr']
        exact not_arrayCopyOob₁ G ha₁ h.1
      · rw [relRules_of_ruleAt (Aggregates.rd B).arrayCopyOob2 hr']
        exact not_arrayCopyOob₂ G ha₂ h.2
      · rw [relRules_of_ruleAt (Aggregates.rd B).arrayCopyZero hr']
        exact not_arrayCopyZero hn0)
  have hty := Aggregates.evalExp_type (Aggregates.aggDefs_simEnv B) (State.stateDefs_simEnv B)
    (Aggregates.findDef_none hρ _) hd (e := .varE "z") (ex := .varE "x_2") (by eval_tac)
    (by eval_tac)
  have hex : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.tupE [.callE "type" [.expA (.varE "z"), .expA (.varE "x_2")],
        .caseE "ARRAY" (.caseE "%%" (.tupE [.iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")]),
          .varE "zt_2"]))])
      (.tuple [CT.defType d₂, tyV ((Ty.field m (Ty.val t)).array : CCompType)]) := by
    cases m <;> exact evalExp_tupE_of (evalExps_cons' hty (by eval_tac))
  have hsx : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.iterE (.varE "sx") (.mk .opt [.mk "sx" (.varE "sx?")]))
        (.callE "sx" [.expA (.varE "zt_2")])) (.bool true) :=
    evalExp_eq_true (by eval_tac) (Vec.evalExp_call (Aggregates.findDef_none hρ _)
      (Vec.evalArgs_var rfl Equiv.evalArgs_nil) (applies_sx_val hV t))
  have hi₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i_1") "%") 0) (.numE (.natN 1)))
      (.num (.natN (i₁ + 1).toNat)) := by
    rw [toNat_succ h.1 hb₁ hn0]
    exact evalExp_addNat (evalExp_unpct (by eval_tac)) evalExp_num'
  have hi₂ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i_2") "%") 0) (.numE (.natN 1)))
      (.num (.natN (i₂ + 1).toNat)) := by
    rw [toNat_succ h.2 hb₂ hn0]
    exact evalExp_addNat (evalExp_unpct (by eval_tac)) evalExp_num'
  have hn' : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE "n") .natT .intT)
        (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT) (.num (.natN (n - 1).toNat)) := by
    rw [toNat_sub_one hn0]
    exact evalExp_predNat (by eval_tac) (by omega)
  refine dderives_of_ruleAt (Aggregates.rd B).arrayCopyLe σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i₁ _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i₂ _ hρ) (QuantsOk.cons rfl (R.nat _ _ hρ)
      (QuantsOk.cons rfl (R.idx _ x₁.value.isLt _ hρ) (QuantsOk.cons rfl (R.idx _ x₂.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.sxOpt none _ hρ) (QuantsOk.cons rfl (A.mut_ m _ hρ)
      (QuantsOk.cons rfl (A.storagetype _ _ hρ) QuantsOk.nil)))))))))))
    (evalExp_tup2 (by eval_tac) ?_)
    (Aggregates.prems_three (.elsePr hel) (.rulePr evalArgs_nil hex (A.expand _ _ he))
      (.ifPr (RefsGC.evalExp_and_true (evalExp_leNat (evalExp_unpct (by eval_tac))
        (evalExp_unpct (by eval_tac)) hle) hsx)))
  have e₈ := evalExp_case (op := "CONST") (evalExp_tupE_of (evalExps_cons'
    (evalExp_case (op := "I32") (evalExp_tupE_of evalExps_nil')) (evalExps_cons'
      (evalExp_case (op := "%") (evalExp_tupE_of (evalExps_cons' hi₁ evalExps_nil'))) evalExps_nil')))
  have e₁₀ := evalExp_case (op := "CONST") (evalExp_tupE_of (evalExps_cons'
    (evalExp_case (op := "I32") (evalExp_tupE_of evalExps_nil')) (evalExps_cons'
      (evalExp_case (op := "%") (evalExp_tupE_of (evalExps_cons' hi₂ evalExps_nil'))) evalExps_nil')))
  have e₁₁ := evalExp_case (op := "CONST") (evalExp_tupE_of (evalExps_cons'
    (evalExp_case (op := "I32") (evalExp_tupE_of evalExps_nil')) (evalExps_cons'
      (evalExp_case (op := "%") (evalExp_tupE_of (evalExps_cons' hn' evalExps_nil'))) evalExps_nil')))
  exact evalExp_listE_of (evalExps_cons' (by eval_tac) (evalExps_cons' (by eval_tac)
    (evalExps_cons' (by eval_tac) (evalExps_cons' (by eval_tac) (evalExps_cons' (by eval_tac)
    (evalExps_cons' (by eval_tac) (evalExps_cons' (by eval_tac) (evalExps_cons' e₈
    (evalExps_cons' (by eval_tac) (evalExps_cons' e₁₀ (evalExps_cons' e₁₁
    (evalExps_cons' (by eval_tac) evalExps_nil'))))))))))))

/-- `array.copy-gt` (`Step_read` rule 92), forward, for an unpacked source element type. -/
theorem sread_arrayCopyGt (hV : VVB B) (R : RTyping (simEnv B)) (G : RStoreFuns (simEnv B))
    (A : Aggregates.AggTypes (simEnv B)) {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx}
    {i₁ i₂ n : BitVec 32} {a₁ a₂ : Nat} {ai₁ ai₂ : ArrayInst} {d₂ : DefType} {m : Mutability}
    {t : CValType} (ha₁ : s.arrays[a₁]? = some ai₁) (ha₂ : s.arrays[a₂]? = some ai₂)
    (h : i₁.toNat + n.toNat ≤ ai₁.fields.length ∧ i₂.toNat + n.toNat ≤ ai₂.fields.length)
    (hn0 : n ≠ 0) (hd : f.type? x₂ = some d₂) (he : Expand d₂ (.array (.field m (.val t))))
    (hgt : i₂.toNat < i₁.toNat) (hb₁ : ai₁.fields.length < 2 ^ 32)
    (hb₂ : ai₂.fields.length < 2 ^ 32) (hz : TypedV (simEnv B) stateT (stateV hn s f)) :
    SRead (simEnv B) (configV hn ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂,
      constI32 n, .plain (.arrayCopy x₁ x₂)]⟩)
      (adminsToV [arrRef a₁, constI32 (i₁ + n - 1), arrRef a₂, constI32 (i₂ + n - 1),
        .plain (.arrayGet none x₂), .plain (.arraySet x₁),
        arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 (n - 1),
        .plain (.arrayCopy x₁ x₂)]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a_1", .num (.natN a₁)),
    ("i_1", pctV i₁.toNat), ("a_2", .num (.natN a₂)), ("i_2", pctV i₂.toNat),
    ("n", .num (.natN n.toNat)), ("x_1", Encode.toValue x₁), ("x_2", Encode.toValue x₂),
    ("sx?", .opt none), ("mut?", mutV m), ("zt_2", tyV (Ty.val t : CStorageType))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hn₀ : n.toNat ≠ 0 := fun h' => hn0 (BitVec.eq_of_toNat_eq (by simpa using h'))
  have hel := otherwise_of_ruleAt (Aggregates.rd B).arrayCopyGt (readTable_simEnv B) (i := 92)
    (b := .list (adminsToV [arrRef a₁, constI32 (i₁ + n - 1), arrRef a₂, constI32 (i₂ + n - 1),
        .plain (.arrayGet none x₂), .plain (.arraySet x₁),
        arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 (n - 1),
        .plain (.arrayCopy x₁ x₂)])) (by decide) (exc := [88, 89, 90, 91])
    (lhsIn_arrayCopy (hn := hn) (s := s) (f := f) (x₁ := x₁) (x₂ := x₂) (i₁ := i₁) (i₂ := i₂)
      (n := n) (a₁ := a₁) (a₂ := a₂)) (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := sameLhs_inv hw
      rcases (by simpa using hj : j = 88 ∨ j = 89 ∨ j = 90 ∨ j = 91) with rfl | rfl | rfl | rfl
      · rw [relRules_of_ruleAt (Aggregates.rd B).arrayCopyOob1 hr']
        exact not_arrayCopyOob₁ G ha₁ h.1
      · rw [relRules_of_ruleAt (Aggregates.rd B).arrayCopyOob2 hr']
        exact not_arrayCopyOob₂ G ha₂ h.2
      · rw [relRules_of_ruleAt (Aggregates.rd B).arrayCopyZero hr']
        exact not_arrayCopyZero hn0
      · rw [relRules_of_ruleAt (Aggregates.rd B).arrayCopyLe hr']
        exact not_arrayCopyLe hgt)
  have hty := Aggregates.evalExp_type (Aggregates.aggDefs_simEnv B) (State.stateDefs_simEnv B)
    (Aggregates.findDef_none hρ _) hd (e := .varE "z") (ex := .varE "x_2") (by eval_tac)
    (by eval_tac)
  have hex : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.tupE [.callE "type" [.expA (.varE "z"), .expA (.varE "x_2")],
        .caseE "ARRAY" (.caseE "%%" (.tupE [.iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")]),
          .varE "zt_2"]))])
      (.tuple [CT.defType d₂, tyV ((Ty.field m (Ty.val t)).array : CCompType)]) := by
    cases m <;> exact evalExp_tupE_of (evalExps_cons' hty (by eval_tac))
  have hsx : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.iterE (.varE "sx") (.mk .opt [.mk "sx" (.varE "sx?")]))
        (.callE "sx" [.expA (.varE "zt_2")])) (.bool true) :=
    evalExp_eq_true (by eval_tac) (Vec.evalExp_call (Aggregates.findDef_none hρ _)
      (Vec.evalArgs_var rfl Equiv.evalArgs_nil) (applies_sx_val hV t))
  have hl₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .subOp (.numT .intT) (.cvtE (.binE .addOp (.numT .natT)
        (.projE (.uncaseE (.varE "i_1") "%") 0) (.varE "n")) .natT .intT)
        (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT) (.num (.natN (i₁ + n - 1).toNat)) := by
    rw [toNat_last h.1 hb₁ hn0]
    exact evalExp_predNat (evalExp_addNat (evalExp_unpct (by eval_tac)) (by eval_tac)) (by omega)
  have hl₂ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .subOp (.numT .intT) (.cvtE (.binE .addOp (.numT .natT)
        (.projE (.uncaseE (.varE "i_2") "%") 0) (.varE "n")) .natT .intT)
        (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT) (.num (.natN (i₂ + n - 1).toNat)) := by
    rw [toNat_last h.2 hb₂ hn0]
    exact evalExp_predNat (evalExp_addNat (evalExp_unpct (by eval_tac)) (by eval_tac)) (by omega)
  have hn' : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE "n") .natT .intT)
        (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT) (.num (.natN (n - 1).toNat)) := by
    rw [toNat_sub_one hn0]
    exact evalExp_predNat (by eval_tac) (by omega)
  refine dderives_of_ruleAt (Aggregates.rd B).arrayCopyGt σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i₁ _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i₂ _ hρ) (QuantsOk.cons rfl (R.nat _ _ hρ)
      (QuantsOk.cons rfl (R.idx _ x₁.value.isLt _ hρ) (QuantsOk.cons rfl (R.idx _ x₂.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.sxOpt none _ hρ) (QuantsOk.cons rfl (A.mut_ m _ hρ)
      (QuantsOk.cons rfl (A.storagetype _ _ hρ) QuantsOk.nil)))))))))))
    (evalExp_tup2 (by eval_tac) ?_)
    (Aggregates.prems_three (.elsePr hel) (.rulePr evalArgs_nil hex (A.expand _ _ he)) (.ifPr hsx))
  have e₂ := evalExp_case (op := "CONST") (evalExp_tupE_of (evalExps_cons'
    (evalExp_case (op := "I32") (evalExp_tupE_of evalExps_nil')) (evalExps_cons'
      (evalExp_case (op := "%") (evalExp_tupE_of (evalExps_cons' hl₁ evalExps_nil'))) evalExps_nil')))
  have e₄ := evalExp_case (op := "CONST") (evalExp_tupE_of (evalExps_cons'
    (evalExp_case (op := "I32") (evalExp_tupE_of evalExps_nil')) (evalExps_cons'
      (evalExp_case (op := "%") (evalExp_tupE_of (evalExps_cons' hl₂ evalExps_nil'))) evalExps_nil')))
  have e₁₁ := evalExp_case (op := "CONST") (evalExp_tupE_of (evalExps_cons'
    (evalExp_case (op := "I32") (evalExp_tupE_of evalExps_nil')) (evalExps_cons'
      (evalExp_case (op := "%") (evalExp_tupE_of (evalExps_cons' hn' evalExps_nil'))) evalExps_nil')))
  exact evalExp_listE_of (evalExps_cons' (by eval_tac) (evalExps_cons' e₂
    (evalExps_cons' (by eval_tac) (evalExps_cons' e₄ (evalExps_cons' (by eval_tac)
    (evalExps_cons' (by eval_tac) (evalExps_cons' (by eval_tac) (evalExps_cons' (by eval_tac)
    (evalExps_cons' (by eval_tac) (evalExps_cons' (by eval_tac) (evalExps_cons' e₁₁
    (evalExps_cons' (by eval_tac) evalExps_nil'))))))))))))

end Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg
