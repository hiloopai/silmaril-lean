module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.RefsGC.Aggregate

/-!
# Family R: the iterating aggregate rules, forward

`array.fill-zero/succ` (read 84/85), `array.copy-zero` (read 90), `array.init_elem-zero/succ`
(read 96/97), `array.init_elem-oob2` (read 95) and `array.new_elem-oob` (read 73). The `-zero` and
`-succ` rules use `otherwise`; the earlier rules of the same instruction (`-null`, `-oob*`,
`-zero`) are refuted from their premises, evaluated in the bindings the left-hand side forces.

Core's iteration steps use 32-bit arithmetic (`i + 1`, `j + 1`), SpecTec's unbounded naturals; they
agree when the incremented index stays below `2 ^ 32`, which `i + n ≤ len` gives for arrays and
segments with fewer than `2 ^ 32` entries (hypotheses `hlen`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.RefsGC

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {env : Env} {H : Type} {hn : H → String}

/-- `(i + 1).toNat`, when it does not wrap. -/
theorem toNat_add_one {i : BitVec 32} (h : i.toNat + 1 < 2 ^ 32) : (i + 1).toNat = i.toNat + 1 := by
  simp only [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl]
  omega

/-- `(n - 1).toNat` for `n ≠ 0`. -/
theorem toNat_sub_one {n : BitVec 32} (h : n ≠ 0) : (n - 1).toNat = n.toNat - 1 := by
  have hn : n.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
  simp only [BitVec.toNat_sub, show (1 : BitVec 32).toNat = 1 from rfl]
  omega

/-! ## Refuting the earlier `array.fill` rules -/

/-- `array.fill-null` does not fire on an array reference. -/
theorem not_arrayFillNull {D : Interp} {els : Prop} {s : Store H} {f : Frame} {a : Nat}
    {rest : List Admin} {c : Value} :
    ¬ RuleBody env D els [] [] "%~>%" arrayFillNullRule
      (.tuple [configV hn ⟨s, f, arrRef a :: rest⟩, c]) := by
  rintro ⟨-, ρ₀, σ, -, -, he, -⟩
  obtain ⟨-, hl⟩ := cfgz_inv (lhs_of_concl he)
  have h₀ := evalExps_get (elems_of_list hl) 0 rfl rfl
  obtain ⟨w, -, hw⟩ := evalExp_caseE_iff.1 h₀
  simp [adminToV, refToValue] at hw

/-- The bindings an `array.fill` left-hand side forces. -/
theorem binds_arrayFill {ρ : VarEnv} {a : Nat} {i n : BitVec 32}
    {v : Val} {x : TypeIdx}
    (hl : EvalExp env ρ (.listE [.caseE "REF.ARRAY_ADDR" (.varE "a"),
      .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "i"]),
      .subE (.varE "val") (.varT "val" []) (.varT "instr" []),
      .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .caseE "%" (.tupE [.varE "n"])]),
      .caseE "ARRAY.FILL" (.varE "x")])
      (.list (adminsToV [arrRef a, constI32 i, v.toAdmin, constI32 n, .plain (.arrayFill x)]))) :
    EvalExp env ρ (.varE "a") (.num (.natN a)) ∧ EvalExp env ρ (.varE "i") (pctV i.toNat) ∧
      EvalExp env ρ (.varE "n") (.num (.natN n.toNat)) := by
  have hs := elems_of_list hl
  exact ⟨case_inv (evalExps_get hs 0 rfl rfl), const_var (evalExps_get hs 1 rfl rfl),
    const_pct_var (evalExps_get hs 3 rfl rfl)⟩

/-- `array.fill-oob` does not fire in bounds. -/
theorem not_arrayFillOob (G : RStoreFuns env) {D : Interp} {els : Prop} {s : Store H}
    {f : Frame} {x : TypeIdx} {i n : BitVec 32} {v : Val} {a : Nat} {ai : ArrayInst}
    (ha : s.arrays[a]? = some ai) (h : i.toNat + n.toNat ≤ ai.fields.length) {c : Value} :
    ¬ RuleBody env D els [] [] "%~>%" arrayFillOobRule
      (.tuple [configV hn ⟨s, f, [arrRef a, constI32 i, v.toAdmin, constI32 n,
        .plain (.arrayFill x)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain ⟨hz, hl⟩ := cfgz_inv (lhs_of_concl he)
  obtain ⟨ha', hi, hn'⟩ := binds_arrayFill hl
  have hif := premW_if (hp _ (List.mem_singleton_self _))
  have hb := EvalExp.unique hif (evalExp_cmpNat (op := .gtOp) (evalExp_addNat (evalExp_unpct hi) hn')
    (evalExp_len (evalExp_arrayFields G (valsOnly_scope hb) hz ha' ha)) rfl)
  simp only [List.length_map, Value.bool.injEq] at hb
  have hgt : ai.fields.length < i.toNat + n.toNat := of_decide_eq_true hb.symm
  omega

/-- `array.fill-zero` does not fire on a non-zero count. -/
theorem not_arrayFillZero {D : Interp} {els : Prop} {s : Store H} {f : Frame} {x : TypeIdx}
    {i n : BitVec 32} {v : Val} {a : Nat} (hn0 : n ≠ 0) {c : Value} :
    ¬ RuleBody env D els [] [] "%~>%" arrayFillZeroRule
      (.tuple [configV hn ⟨s, f, [arrRef a, constI32 i, v.toAdmin, constI32 n,
        .plain (.arrayFill x)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, -, -, he, hp⟩
  obtain ⟨-, hl⟩ := cfgz_inv (lhs_of_concl he)
  obtain ⟨-, -, hn'⟩ := binds_arrayFill hl
  have hif := premW_if (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have h0 : Value.num (.natN n.toNat) = .num (.natN 0) := eq_of_evalExp_eq hif hn' evalExp_num'
  simp only [Value.num.injEq, Num.natN.injEq] at h0
  exact hn0 (BitVec.eq_of_toNat_eq (by simpa using h0))

/-- The left-hand side of an `array.fill` step has its constructors among `ARRAY.FILL` and those
of values. -/
theorem lhsIn_arrayFill {s : Store H} {f : Frame} {a : Nat} {i n : BitVec 32} {v : Val}
    {x : TypeIdx} :
    LhsIn (["ARRAY.FILL"] ++ valTags)
      (configV hn ⟨s, f, [arrRef a, constI32 i, v.toAdmin, constI32 n, .plain (.arrayFill x)]⟩) := by
  refine .inr ⟨_, _, rfl, tagsIn_cons (tag_case (by decide)) (tagsIn_cons (tag_case (by decide))
    (tagsIn_cons ?_ (tagsIn_cons (tag_case (by decide)) (tagsIn_cons (tag_case (by decide))
      tagsIn_nil))))⟩
  rw [adminToV_toAdmin]
  exact tag_val (valTags_sub _) v

/-! ## `array.fill-zero`, `array.fill-succ` -/

/-- `array.fill-zero` (rule 84). -/
theorem sread_arrayFillZero (h₀ : HasRuleAt env "Step_read" "%~>%" 84 arrayFillZeroRule)
    (h₈₂ : HasRuleAt env "Step_read" "%~>%" 82 arrayFillNullRule)
    (h₈₃ : HasRuleAt env "Step_read" "%~>%" 83 arrayFillOobRule)
    (hT : ((relRules env "Step_read").map ruleTags).take 103 = readTagTable)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env) {s : Store H} {f : Frame}
    {x : TypeIdx} {i : BitVec 32} {v : Val} {a : Nat} {ai : ArrayInst}
    (ha : s.arrays[a]? = some ai) (h : i.toNat ≤ ai.fields.length)
    (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV
      [arrRef a, constI32 i, v.toAdmin, constI32 0, .plain (.arrayFill x)]))) :
    SRead env (configV hn ⟨s, f, [arrRef a, constI32 i, v.toAdmin, constI32 0,
      .plain (.arrayFill x)]⟩) (adminsToV []) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("i", pctV i.toNat), ("val", adminToV v.toAdmin), ("n", .num (.natN 0)), ("x", Encode.toValue x)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hv : TypedV env valT (adminToV v.toAdmin) :=
    typed_toAdmin R v (typed_head T (typed_tail T (typed_tail T hc)))
  have hel := otherwise_of_ruleAt h₀ hT (i := 84) (b := .list (adminsToV [])) (by decide)
    (exc := [82, 83])
    (lhsIn_arrayFill (hn := hn) (s := s) (f := f) (a := a) (i := i) (n := 0) (v := v) (x := x)) (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := sameLhs_inv hw
      rcases (by simpa using hj : j = 82 ∨ j = 83) with rfl | rfl
      · rw [relRules_of_ruleAt h₈₂ hr']
        exact not_arrayFillNull
      · rw [relRules_of_ruleAt h₈₃ hr']
        exact not_arrayFillOob G ha (by simpa using h))
  exact dderives_of_ruleAt h₀ σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (hv _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
        QuantsOk.nil))))))
    (by eval_tac) (prems_two (.elsePr hel) (.ifPr (evalExp_eq_true (by eval_tac) evalExp_num')))

/-- `array.fill-succ` (rule 85), for an array with fewer than `2 ^ 32` elements. -/
theorem sread_arrayFillSucc (h₀ : HasRuleAt env "Step_read" "%~>%" 85 arrayFillSuccRule)
    (h₈₂ : HasRuleAt env "Step_read" "%~>%" 82 arrayFillNullRule)
    (h₈₃ : HasRuleAt env "Step_read" "%~>%" 83 arrayFillOobRule)
    (h₈₄ : HasRuleAt env "Step_read" "%~>%" 84 arrayFillZeroRule)
    (hT : ((relRules env "Step_read").map ruleTags).take 103 = readTagTable)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env) {s : Store H} {f : Frame}
    {x : TypeIdx} {i n : BitVec 32} {v : Val} {a : Nat} {ai : ArrayInst}
    (ha : s.arrays[a]? = some ai) (h : i.toNat + n.toNat ≤ ai.fields.length) (hn0 : n ≠ 0)
    (hlen : ai.fields.length < 2 ^ 32) (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV
      [arrRef a, constI32 i, v.toAdmin, constI32 n, .plain (.arrayFill x)]))) :
    SRead env (configV hn ⟨s, f, [arrRef a, constI32 i, v.toAdmin, constI32 n,
      .plain (.arrayFill x)]⟩)
      (adminsToV [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x),
        arrRef a, constI32 (i + 1), v.toAdmin, constI32 (n - 1), .plain (.arrayFill x)]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("i", pctV i.toNat), ("val", adminToV v.toAdmin), ("n", .num (.natN n.toNat)),
    ("x", Encode.toValue x)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hv : TypedV env valT (adminToV v.toAdmin) :=
    typed_toAdmin R v (typed_head T (typed_tail T (typed_tail T hc)))
  have hn₀ : n.toNat ≠ 0 := fun h' => hn0 (BitVec.eq_of_toNat_eq (by simpa using h'))
  have hel := otherwise_of_ruleAt h₀ hT (i := 85) (b := .list (adminsToV [arrRef a, constI32 i,
      v.toAdmin, .plain (.arraySet x), arrRef a, constI32 (i + 1), v.toAdmin, constI32 (n - 1),
      .plain (.arrayFill x)])) (by decide) (exc := [82, 83, 84])
      (lhsIn_arrayFill (hn := hn) (s := s) (f := f) (a := a) (i := i) (n := n) (v := v) (x := x)) (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := sameLhs_inv hw
      rcases (by simpa using hj : j = 82 ∨ j = 83 ∨ j = 84) with rfl | rfl | rfl
      · rw [relRules_of_ruleAt h₈₂ hr']
        exact not_arrayFillNull
      · rw [relRules_of_ruleAt h₈₃ hr']
        exact not_arrayFillOob G ha h
      · rw [relRules_of_ruleAt h₈₄ hr']
        exact not_arrayFillZero hn0)
  have hi : EvalExp env (VarEnv.empty.bindVals σ)
      (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0) (.numE (.natN 1)))
      (.num (.natN (i + 1).toNat)) := by
    rw [toNat_add_one (by omega)]
    exact evalExp_addNat (evalExp_unpct (by eval_tac)) evalExp_num'
  have hn' : EvalExp env (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE "n") .natT .intT)
        (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT) (.num (.natN (n - 1).toNat)) := by
    rw [toNat_sub_one hn0]
    exact evalExp_predNat (by eval_tac) (by omega)
  refine dderives_of_ruleAt h₀ σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (hv _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
        QuantsOk.nil))))))
    (evalExp_tup2 (by eval_tac) ?_) (prems_one (.elsePr hel))
  have e₅ := evalExp_case (op := "CONST") (evalExp_tupE_of (evalExps_cons'
    (evalExp_case (op := "I32") (evalExp_tupE_of evalExps_nil')) (evalExps_cons' (evalExp_case (op := "%") (evalExp_tupE_of (evalExps_cons' hi evalExps_nil')))
      evalExps_nil')))
  have e₇ := evalExp_case (op := "CONST") (evalExp_tupE_of (evalExps_cons'
    (evalExp_case (op := "I32") (evalExp_tupE_of evalExps_nil')) (evalExps_cons' (evalExp_case (op := "%") (evalExp_tupE_of (evalExps_cons' hn' evalExps_nil')))
      evalExps_nil')))
  refine evalExp_listE_of (evalExps_cons' (by eval_tac) (evalExps_cons' (by eval_tac)
    (evalExps_cons' (by eval_tac) (evalExps_cons' (by eval_tac) (evalExps_cons' (by eval_tac)
    (evalExps_cons' e₅ (evalExps_cons' (by eval_tac) (evalExps_cons' e₇
    (evalExps_cons' (by eval_tac) evalExps_nil')))))))))

/-! ## `array.copy-zero` -/

/-- The bindings an `array.copy` left-hand side forces. -/
theorem binds_arrayCopy {ρ : VarEnv} {a₁ a₂ : Nat} {i₁ i₂ n : BitVec 32} {x₁ x₂ : TypeIdx}
    (hl : EvalExp env ρ (.listE [.caseE "REF.ARRAY_ADDR" (.varE "a_1"),
      .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "i_1"]),
      .caseE "REF.ARRAY_ADDR" (.varE "a_2"),
      .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "i_2"]),
      .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .caseE "%" (.tupE [.varE "n"])]),
      .caseE "ARRAY.COPY" (.tupE [.varE "x_1", .varE "x_2"])])
      (.list (adminsToV [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n,
        .plain (.arrayCopy x₁ x₂)]))) :
    EvalExp env ρ (.varE "a_1") (.num (.natN a₁)) ∧ EvalExp env ρ (.varE "i_1") (pctV i₁.toNat) ∧
      EvalExp env ρ (.varE "a_2") (.num (.natN a₂)) ∧ EvalExp env ρ (.varE "i_2") (pctV i₂.toNat) ∧
      EvalExp env ρ (.varE "n") (.num (.natN n.toNat)) := by
  have hs := elems_of_list hl
  exact ⟨case_inv (evalExps_get hs 0 rfl rfl), const_var (evalExps_get hs 1 rfl rfl),
    case_inv (evalExps_get hs 2 rfl rfl), const_var (evalExps_get hs 3 rfl rfl),
    const_pct_var (evalExps_get hs 4 rfl rfl)⟩

/-- `array.copy-oob1` does not fire when the destination range is in bounds. -/
theorem not_arrayCopyOob₁ (G : RStoreFuns env) {D : Interp} {els : Prop} {s : Store H}
    {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32} {a₁ a₂ : Nat} {ai₁ : ArrayInst}
    (ha : s.arrays[a₁]? = some ai₁) (h : i₁.toNat + n.toNat ≤ ai₁.fields.length) {c : Value} :
    ¬ RuleBody env D els [] [] "%~>%" arrayCopyOob1Rule
      (.tuple [configV hn ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n,
        .plain (.arrayCopy x₁ x₂)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain ⟨hz, hl⟩ := cfgz_inv (lhs_of_concl he)
  obtain ⟨ha', hi, -, -, hn'⟩ := binds_arrayCopy hl
  have hif := premW_if (hp _ (List.mem_singleton_self _))
  have hb := EvalExp.unique hif (evalExp_cmpNat (op := .gtOp) (evalExp_addNat (evalExp_unpct hi) hn')
    (evalExp_len (evalExp_arrayFields G (valsOnly_scope hb) hz ha' ha)) rfl)
  simp only [List.length_map, Value.bool.injEq] at hb
  have hgt : ai₁.fields.length < i₁.toNat + n.toNat := of_decide_eq_true hb.symm
  omega

/-- `array.copy-oob2` does not fire when the source range is in bounds. -/
theorem not_arrayCopyOob₂ (G : RStoreFuns env) {D : Interp} {els : Prop} {s : Store H}
    {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32} {a₁ a₂ : Nat} {ai₂ : ArrayInst}
    (ha : s.arrays[a₂]? = some ai₂) (h : i₂.toNat + n.toNat ≤ ai₂.fields.length) {c : Value} :
    ¬ RuleBody env D els [] [] "%~>%" arrayCopyOob2Rule
      (.tuple [configV hn ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n,
        .plain (.arrayCopy x₁ x₂)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain ⟨hz, hl⟩ := cfgz_inv (lhs_of_concl he)
  obtain ⟨-, -, ha', hi, hn'⟩ := binds_arrayCopy hl
  have hif := premW_if (hp _ (List.mem_singleton_self _))
  have hb := EvalExp.unique hif (evalExp_cmpNat (op := .gtOp) (evalExp_addNat (evalExp_unpct hi) hn')
    (evalExp_len (evalExp_arrayFields G (valsOnly_scope hb) hz ha' ha)) rfl)
  simp only [List.length_map, Value.bool.injEq] at hb
  have hgt : ai₂.fields.length < i₂.toNat + n.toNat := of_decide_eq_true hb.symm
  omega

/-- `array.copy-zero` (rule 90). -/
theorem sread_arrayCopyZero (h₀ : HasRuleAt env "Step_read" "%~>%" 90 arrayCopyZeroRule)
    (h₈₈ : HasRuleAt env "Step_read" "%~>%" 88 arrayCopyOob1Rule)
    (h₈₉ : HasRuleAt env "Step_read" "%~>%" 89 arrayCopyOob2Rule)
    (hT : ((relRules env "Step_read").map ruleTags).take 103 = readTagTable)
    (R : RTyping env) (G : RStoreFuns env) {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx}
    {i₁ i₂ : BitVec 32} {a₁ a₂ : Nat} {ai₁ ai₂ : ArrayInst} (ha₁ : s.arrays[a₁]? = some ai₁)
    (ha₂ : s.arrays[a₂]? = some ai₂)
    (h : i₁.toNat ≤ ai₁.fields.length ∧ i₂.toNat ≤ ai₂.fields.length)
    (hz : TypedV env stateT (stateV hn s f)) :
    SRead env (configV hn ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 0,
      .plain (.arrayCopy x₁ x₂)]⟩) (adminsToV []) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a_1", .num (.natN a₁)),
    ("i_1", pctV i₁.toNat), ("a_2", .num (.natN a₂)), ("i_2", pctV i₂.toNat),
    ("n", .num (.natN 0)), ("x_1", Encode.toValue x₁), ("x_2", Encode.toValue x₂)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have ha : LhsIn ["ARRAY.COPY", "REF.ARRAY_ADDR", "CONST"]
      (configV hn ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 0,
        .plain (.arrayCopy x₁ x₂)]⟩) :=
    .inr ⟨_, _, rfl, tagsIn_cons (tag_case (by decide)) (tagsIn_cons (tag_case (by decide))
      (tagsIn_cons (tag_case (by decide)) (tagsIn_cons (tag_case (by decide))
      (tagsIn_cons (tag_case (by decide)) (tagsIn_cons (tag_case (by decide)) tagsIn_nil)))))⟩
  have hel := otherwise_of_ruleAt h₀ hT (i := 90) (b := .list (adminsToV [])) (by decide)
    (exc := [88, 89]) ha (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := sameLhs_inv hw
      rcases (by simpa using hj : j = 88 ∨ j = 89) with rfl | rfl
      · rw [relRules_of_ruleAt h₈₈ hr']
        exact not_arrayCopyOob₁ G ha₁ (by simpa using h.1)
      · rw [relRules_of_ruleAt h₈₉ hr']
        exact not_arrayCopyOob₂ G ha₂ (by simpa using h.2))
  exact dderives_of_ruleAt h₀ σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i₁ _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i₂ _ hρ) (QuantsOk.cons rfl (R.nat _ _ hρ)
      (QuantsOk.cons rfl (R.idx _ x₁.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.idx _ x₂.value.isLt _ hρ) QuantsOk.nil))))))))
    (by eval_tac) (prems_two (.elsePr hel) (.ifPr (evalExp_eq_true (by eval_tac) evalExp_num')))

/-! ## Element segments -/

/-- The references of `$elem(z, y)`. -/
theorem evalExp_elemRefs (G : RStoreFuns env) {ρ : VarEnv} {s : Store H} {f : Frame}
    {y : ElemIdx} {ea : Nat} {ei : ElemInst} (hvo : ValsOnly ρ) (he : s.elem? f y = some (ea, ei))
    (hz : EvalExp env ρ (.varE "z") (stateV hn s f))
    (hy : EvalExp env ρ (.varE "y") (Encode.toValue y)) :
    EvalExp env ρ (.dotE (.callE "elem" [.expA (.varE "z"), .expA (.varE "y")]) "REFS")
      (.list (ei.refs.map refToValue)) :=
  evalExp_dot (G.elem hn ρ _ _ s f y ea ei hvo he hz hy) rfl

/-- `array.new_elem-oob` (rule 73). -/
theorem sread_arrayNewElemOob (h₀ : HasRuleAt env "Step_read" "%~>%" 73 arrayNewElemOobRule)
    (R : RTyping env) (G : RStoreFuns env) {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx}
    {i n : BitVec 32} {ea : Nat} {ei : ElemInst} (he : s.elem? f y = some (ea, ei))
    (h : ei.refs.length < i.toNat + n.toNat) (hz : TypedV env stateT (stateV hn s f)) :
    SRead env (configV hn ⟨s, f, [constI32 i, constI32 n, .plain (.arrayNewElem x y)]⟩)
      (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat),
    ("n", .num (.natN n.toNat)), ("x", Encode.toValue x), ("y", Encode.toValue y)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  exact dderives_of_ruleAt h₀ σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.i32 i _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.idx _ y.value.isLt _ hρ) QuantsOk.nil)))))
    (by eval_tac)
    (prems_one (.ifPr (evalExp_gtNat (evalExp_addNat (evalExp_unpct (by eval_tac)) (by eval_tac))
      (evalExp_len (evalExp_elemRefs G (by exact ⟨rfl, rfl, rfl⟩) he (by eval_tac) (by eval_tac))) (by simpa using h))))

/-- `array.init_elem-oob2` (rule 95). -/
theorem sread_arrayInitElemOob₂ (h₀ : HasRuleAt env "Step_read" "%~>%" 95 arrayInitElemOob2Rule)
    (R : RTyping env) (G : RStoreFuns env) {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx}
    {i j n : BitVec 32} {a ea : Nat} {ei : ElemInst} (he : s.elem? f y = some (ea, ei))
    (h : ei.refs.length < j.toNat + n.toNat) (hz : TypedV env stateT (stateV hn s f)) :
    SRead env (configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
      .plain (.arrayInitElem x y)]⟩) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("i", pctV i.toNat), ("j", pctV j.toNat), ("n", .num (.natN n.toNat)),
    ("x", Encode.toValue x), ("y", Encode.toValue y)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  exact dderives_of_ruleAt h₀ σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (R.i32 j _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.idx _ y.value.isLt _ hρ) QuantsOk.nil)))))))
    (by eval_tac)
    (prems_one (.ifPr (evalExp_gtNat (evalExp_addNat (evalExp_unpct (by eval_tac)) (by eval_tac))
      (evalExp_len (evalExp_elemRefs G (by exact ⟨rfl, rfl, rfl⟩) he (by eval_tac) (by eval_tac))) (by simpa using h))))

/-- The bindings an `array.init_elem` left-hand side forces. -/
theorem binds_arrayInitElem {ρ : VarEnv} {a : Nat} {i j n : BitVec 32} {x : TypeIdx}
    {y : ElemIdx}
    (hl : EvalExp env ρ (.listE [.caseE "REF.ARRAY_ADDR" (.varE "a"),
      .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "i"]),
      .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "j"]),
      .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .caseE "%" (.tupE [.varE "n"])]),
      .caseE "ARRAY.INIT_ELEM" (.tupE [.varE "x", .varE "y"])])
      (.list (adminsToV [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitElem x y)]))) :
    EvalExp env ρ (.varE "a") (.num (.natN a)) ∧ EvalExp env ρ (.varE "i") (pctV i.toNat) ∧
      EvalExp env ρ (.varE "j") (pctV j.toNat) ∧ EvalExp env ρ (.varE "n") (.num (.natN n.toNat)) ∧
      EvalExp env ρ (.varE "y") (Encode.toValue y) := by
  have hs := elems_of_list hl
  have h₄ := elems_of_tup (case_inv (evalExps_get hs 4 rfl rfl))
  exact ⟨case_inv (evalExps_get hs 0 rfl rfl), const_var (evalExps_get hs 1 rfl rfl),
    const_var (evalExps_get hs 2 rfl rfl), const_pct_var (evalExps_get hs 3 rfl rfl),
    (evalExps_cons_inv (evalExps_cons_inv h₄).2).1⟩

/-- `array.init_elem-oob1` does not fire when the array range is in bounds. -/
theorem not_arrayInitElemOob₁ (G : RStoreFuns env) {D : Interp} {els : Prop} {s : Store H}
    {f : Frame} {x : TypeIdx} {y : ElemIdx} {i j n : BitVec 32} {a : Nat} {ai : ArrayInst}
    (ha : s.arrays[a]? = some ai) (h : i.toNat + n.toNat ≤ ai.fields.length) {c : Value} :
    ¬ RuleBody env D els [] [] "%~>%" arrayInitElemOob1Rule
      (.tuple [configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitElem x y)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain ⟨hz, hl⟩ := cfgz_inv (lhs_of_concl he)
  obtain ⟨ha', hi, -, hn', -⟩ := binds_arrayInitElem hl
  have hif := premW_if (hp _ (List.mem_singleton_self _))
  have hb := EvalExp.unique hif (evalExp_cmpNat (op := .gtOp) (evalExp_addNat (evalExp_unpct hi) hn')
    (evalExp_len (evalExp_arrayFields G (valsOnly_scope hb) hz ha' ha)) rfl)
  simp only [List.length_map, Value.bool.injEq] at hb
  have hgt : ai.fields.length < i.toNat + n.toNat := of_decide_eq_true hb.symm
  omega

/-- `array.init_elem-oob2` does not fire when the segment range is in bounds. -/
theorem not_arrayInitElemOob₂ (G : RStoreFuns env) {D : Interp} {els : Prop} {s : Store H}
    {f : Frame} {x : TypeIdx} {y : ElemIdx} {i j n : BitVec 32} {a ea : Nat} {ei : ElemInst}
    (he' : s.elem? f y = some (ea, ei)) (h : j.toNat + n.toNat ≤ ei.refs.length) {c : Value} :
    ¬ RuleBody env D els [] [] "%~>%" arrayInitElemOob2Rule
      (.tuple [configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitElem x y)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain ⟨hz, hl⟩ := cfgz_inv (lhs_of_concl he)
  obtain ⟨-, -, hj, hn', hy⟩ := binds_arrayInitElem hl
  have hif := premW_if (hp _ (List.mem_singleton_self _))
  have hb := EvalExp.unique hif (evalExp_cmpNat (op := .gtOp) (evalExp_addNat (evalExp_unpct hj) hn')
    (evalExp_len (evalExp_elemRefs G (valsOnly_scope hb) he' hz hy)) rfl)
  simp only [List.length_map, Value.bool.injEq] at hb
  have hgt : ei.refs.length < j.toNat + n.toNat := of_decide_eq_true hb.symm
  omega

/-- `array.init_elem-zero` (rule 96). -/
theorem sread_arrayInitElemZero (h₀ : HasRuleAt env "Step_read" "%~>%" 96 arrayInitElemZeroRule)
    (h₉₄ : HasRuleAt env "Step_read" "%~>%" 94 arrayInitElemOob1Rule)
    (h₉₅ : HasRuleAt env "Step_read" "%~>%" 95 arrayInitElemOob2Rule)
    (hT : ((relRules env "Step_read").map ruleTags).take 103 = readTagTable)
    (R : RTyping env) (G : RStoreFuns env) {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx}
    {i j : BitVec 32} {a ea : Nat} {ai : ArrayInst} {ei : ElemInst}
    (ha : s.arrays[a]? = some ai) (he : s.elem? f y = some (ea, ei))
    (h : i.toNat ≤ ai.fields.length ∧ j.toNat ≤ ei.refs.length)
    (hz : TypedV env stateT (stateV hn s f)) :
    SRead env (configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 0,
      .plain (.arrayInitElem x y)]⟩) (adminsToV []) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("i", pctV i.toNat), ("j", pctV j.toNat), ("n", .num (.natN 0)),
    ("x", Encode.toValue x), ("y", Encode.toValue y)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hl : LhsIn ["ARRAY.INIT_ELEM", "REF.ARRAY_ADDR", "CONST"]
      (configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 0,
        .plain (.arrayInitElem x y)]⟩) :=
    .inr ⟨_, _, rfl, tagsIn_cons (tag_case (by decide)) (tagsIn_cons (tag_case (by decide))
      (tagsIn_cons (tag_case (by decide)) (tagsIn_cons (tag_case (by decide))
      (tagsIn_cons (tag_case (by decide)) tagsIn_nil))))⟩
  have hel := otherwise_of_ruleAt h₀ hT (i := 96) (b := .list (adminsToV [])) (by decide)
    (exc := [94, 95]) hl (by decide) (by
      intro k hk _ r' hr' w hw
      obtain ⟨c, rfl⟩ := sameLhs_inv hw
      rcases (by simpa using hk : k = 94 ∨ k = 95) with rfl | rfl
      · rw [relRules_of_ruleAt h₉₄ hr']
        exact not_arrayInitElemOob₁ G ha (by simpa using h.1)
      · rw [relRules_of_ruleAt h₉₅ hr']
        exact not_arrayInitElemOob₂ G he (by simpa using h.2))
  exact dderives_of_ruleAt h₀ σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (R.i32 j _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.idx _ y.value.isLt _ hρ) QuantsOk.nil)))))))
    (by eval_tac) (prems_two (.elsePr hel) (.ifPr (evalExp_eq_true (by eval_tac) evalExp_num')))

end Silmaril.Wasm.SpecTec.Sim.RefsGC
