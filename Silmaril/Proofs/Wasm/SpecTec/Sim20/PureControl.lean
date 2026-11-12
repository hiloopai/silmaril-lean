module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureBasic

/-!
# Control rules of wasm-2.0 `Step_pure`, rule by rule

For each rule `r` of the control family, at the image of the V2 left-hand side of the
constructor that transcribes `r`: rule `r` fires (under the backend reading `FiresB`) with
right-hand side `w` **iff** the constructor's side conditions hold and `w` is the image of the
constructor's right-hand side. Each `*_iff` is the pair of `*_inv` (SpecTec → V2) and `*_fires`
(V2 → SpecTec); only `*_fires` needs the typing hypotheses, which type the rule's quantified
variables as the declarative reading requires.

Covered here: `unreachable` (0), `nop` (1), `drop` (2), `select-true`/`-false` (3, 4),
`if-true`/`-false` (5, 6), `label-vals` (7), `br_if-true`/`-false` (10, 11),
`br_table-lt`/`-ge` (12, 13), `frame-vals` (14), `trap-label` (18), `trap-frame` (19).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Pure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV evalExp_imm_iff)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk TypedV ValsOnly evalExp_tup2 evalExp_tup3 evalExp_list1
  evalExp_case)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (FiresB ruleConcl)

variable (B : Builtins)

/-! ## Encodings -/

/-- A value as an administrative instruction is encoded as the value. -/
theorem adminToV_toAdmin (v : Val) : adminToV v.toAdmin = valV v := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | (_ | _ | _) <;> rfl

/-- `vals vs` is encoded value by value. -/
theorem adminsToV_vals (vs : List Val) : adminsToV (vals vs) = vs.map valV := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    show adminToV v.toAdmin :: adminsToV (vals vs) = valV v :: vs.map valV
    rw [adminToV_toAdmin, ih]

/-- The encoding keeps the length of a value sequence. -/
theorem adminsToV_vals_length (vs : List Val) : (adminsToV (vals vs)).length = vs.length := by
  rw [adminsToV_vals, List.length_map]

/-! ## `unreachable`, `nop` -/

/-- **`Step_pure/unreachable` is `PureStep.unreachable`.** -/
theorem unreachable_iff {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 0 (.tuple [.list (adminsToV [.plain .unreachable]), w]) ↔
      w = .list (adminsToV [.trap]) := by
  have ev : ∀ ρ : VarEnv, EvalExp (simEnv20 B) ρ (ruleConcl unreachableRule)
      (.tuple [.list (adminsToV [.plain .unreachable]), .list (adminsToV [.trap])]) := fun _ =>
    evalExp_tup2 (evalExp_list1 evalExp_caseNil) (evalExp_list1 evalExp_caseNil)
  constructor
  · intro hf
    obtain ⟨σ, -, he, -⟩ := firesB20_inv (hasRuleAt_unreachable B) hf
    have hu : Value.tuple [.list (adminsToV [.plain .unreachable]), w] =
        .tuple [.list (adminsToV [.plain .unreachable]), .list (adminsToV [.trap])] :=
      EvalExp.unique he (ev _)
    simpa using hu
  · rintro rfl
    exact firesB20_of (hasRuleAt_unreachable B) [] QuantsOk.nil (ev _) prems_nil

/-- **`Step_pure/nop` is `PureStep.nop`.** -/
theorem nop_iff {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 1 (.tuple [.list (adminsToV [.plain .nop]), w]) ↔
      w = .list (adminsToV []) := by
  have ev : ∀ ρ : VarEnv, EvalExp (simEnv20 B) ρ (ruleConcl nopRule)
      (.tuple [.list (adminsToV [.plain .nop]), .list (adminsToV [])]) := fun _ =>
    evalExp_tup2 (evalExp_list1 evalExp_caseNil) evalExp_list0
  constructor
  · intro hf
    obtain ⟨σ, -, he, -⟩ := firesB20_inv (hasRuleAt_nop B) hf
    have hu : Value.tuple [.list (adminsToV [.plain .nop]), w] =
        .tuple [.list (adminsToV [.plain .nop]), .list (adminsToV [])] := EvalExp.unique he (ev _)
    simpa using hu
  · rintro rfl
    exact firesB20_of (hasRuleAt_nop B) [] QuantsOk.nil (ev _) prems_nil

/-! ## `drop` -/

/-- The conclusion of `drop`, evaluated. -/
theorem eval_drop {env : Env} {ρ : VarEnv} {u : Value} (fu : ρ.findVal? "val" = some u) :
    EvalExp env ρ (ruleConcl dropRule) (.tuple [.list [u, caseNilV "DROP"], .list []]) :=
  evalExp_tup2 (evalExp_list2 (evalExp_sub (evalExp_var fu)) evalExp_caseNil) evalExp_list0

/-- `drop`, read back. -/
theorem drop_inv {v : Val} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 2
      (.tuple [.list (adminsToV [v.toAdmin, .plain .drop]), w])) :
    w = .list (adminsToV []) := by
  obtain ⟨σ, hq, he, -⟩ := firesB20_inv (hasRuleAt_drop B) hf
  obtain ⟨u, fu⟩ := quant_val (x := "val") (t := valT) hq (by simp)
  have hu : Value.tuple [.list (adminsToV [v.toAdmin, .plain .drop]), w] =
      .tuple [.list [u, caseNilV "DROP"], .list []] := EvalExp.unique he (eval_drop fu)
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hu
  exact hu.2

/-- `drop`, fired. -/
theorem drop_fires {v : Val} (hv : TypedV (simEnv20 B) valT (valV v)) :
    FiresB (simEnv20 B) "Step_pure" 2
      (.tuple [.list (adminsToV [v.toAdmin, .plain .drop]), .list (adminsToV [])]) := by
  have fu : (VarEnv.empty.bindVals [("val", valV v)]).findVal? "val" = some (valV v) := rfl
  have he : EvalExp (simEnv20 B) (VarEnv.empty.bindVals [("val", valV v)]) (ruleConcl dropRule)
      (.tuple [.list (adminsToV [v.toAdmin, .plain .drop]), .list (adminsToV [])]) := by
    rw [show adminsToV [v.toAdmin, .plain .drop] = [valV v, caseNilV "DROP"] by
      simp [adminsToV, adminToV_toAdmin]; rfl]
    exact eval_drop fu
  exact firesB20_of (hasRuleAt_drop B) _ (QuantsOk.cons fu (hv _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)
    he prems_nil

/-- **`Step_pure/drop` is `PureStep.drop`.** -/
theorem drop_iff {v : Val} (hv : TypedV (simEnv20 B) valT (valV v)) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 2
        (.tuple [.list (adminsToV [v.toAdmin, .plain .drop]), w]) ↔
      w = .list (adminsToV []) :=
  ⟨drop_inv B, fun h => h ▸ drop_fires B hv⟩

/-! ## `select` -/

/-- The annotation of `SELECT`. -/
def selAnnot (ts : Option (List V2.ValType)) : Option (List Value) := ts.map (·.map valTypeV)

/-- `SELECT`'s encoding through `selAnnot`. -/
theorem instrToV_select (ts : Option (List V2.ValType)) :
    instrToV (.select ts) = .case "SELECT" (.opt ((selAnnot ts).map .list)) := by
  cases ts <;> rfl

/-- The left-hand side of the `select` rules, encoded. -/
theorem adminsToV_select (v₁ v₂ : Val) (c : BitVec 32) (ts : Option (List V2.ValType)) :
    adminsToV [v₁.toAdmin, v₂.toAdmin, constI32 c, .plain (.select ts)] =
      [valV v₁, valV v₂, .case "CONST" (.tuple [caseNilV "I32", pctV c.toNat]),
        .case "SELECT" (.opt ((selAnnot ts).map .list))] := by
  show [adminToV v₁.toAdmin, adminToV v₂.toAdmin, adminToV (constI32 c),
    instrToV (.select ts)] = _
  rw [adminToV_toAdmin, adminToV_toAdmin, instrToV_select]
  rfl

/-- The conclusions of `select-true`/`select-false`, evaluated. -/
theorem eval_select {env : Env} {ρ : VarEnv} {u₁ u₂ c : Value} {o : Option (List Value)}
    (f₁ : ρ.findVal? "val_1" = some u₁) (f₂ : ρ.findVal? "val_2" = some u₂)
    (fc : ρ.findVal? "c" = some c) (ft : ρ.findVal? "t*?" = some (.opt (o.map .list))) :
    EvalExp env ρ (ruleConcl selectTrueRule)
        (.tuple [.list [u₁, u₂, .case "CONST" (.tuple [caseNilV "I32", c]),
          .case "SELECT" (.opt (o.map .list))], .list [u₁]]) ∧
      EvalExp env ρ (ruleConcl selectFalseRule)
        (.tuple [.list [u₁, u₂, .case "CONST" (.tuple [caseNilV "I32", c]),
          .case "SELECT" (.opt (o.map .list))], .list [u₂]]) := by
  have hs := Silmaril.Wasm.SpecTec.Sim.IntNumeric.evalExp_selectAnnot (env := env) ft
  constructor
  · exact evalExp_tup2 (evalExp_list4 (evalExp_sub (evalExp_var f₁)) (evalExp_sub (evalExp_var f₂))
      (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var fc))) (evalExp_case hs))
      (evalExp_list1 (evalExp_sub (evalExp_var f₁)))
  · exact evalExp_tup2 (evalExp_list4 (evalExp_sub (evalExp_var f₁)) (evalExp_sub (evalExp_var f₂))
      (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var fc))) (evalExp_case hs))
      (evalExp_list1 (evalExp_sub (evalExp_var f₂)))

/-- A value of type `valtype*?` is an option of lists. -/
theorem hasTyp_optList {env : Env} {ρ : VarEnv} {t : Typ} {v : Value}
    (h : HasTyp env ρ (.iterT (.iterT t .list) .opt) v) :
    ∃ o : Option (List Value), v = .opt (o.map .list) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [hasTyp] at hn
  | succ n =>
    cases v with
    | opt o =>
      cases o with
      | none => exact ⟨none, rfl⟩
      | some w =>
        obtain ⟨l, rfl⟩ := hasTyp_list_isList ⟨n, by simpa [hasTyp, Value.asOpt?] using hn⟩
        exact ⟨some l, rfl⟩
    | _ => simp [hasTyp, Value.asOpt?] at hn

/-- `select-true`, read back. -/
theorem selectTrue_inv {v₁ v₂ : Val} {c : BitVec 32} {ts : Option (List V2.ValType)} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 3
      (.tuple [.list (adminsToV [v₁.toAdmin, v₂.toAdmin, constI32 c, .plain (.select ts)]), w])) :
    c ≠ 0 ∧ w = .list (adminsToV [v₁.toAdmin]) := by
  obtain ⟨σ, hq, he, hp⟩ := firesB20_inv (hasRuleAt_selectTrue B) hf
  obtain ⟨u₁, f₁⟩ := quant_val (x := "val_1") (t := valT) hq (by simp)
  obtain ⟨u₂, f₂⟩ := quant_val (x := "val_2") (t := valT) hq (by simp)
  obtain ⟨vc, fc⟩ := quant_val (x := "c") (t := i32T) hq (by simp)
  obtain ⟨va, fa, ha⟩ := hq "t*?" valtypesOptT (by simp)
  obtain ⟨o, rfl⟩ := hasTyp_optList ha
  have hu := EvalExp.unique he (eval_select f₁ f₂ fc fa).1
  rw [adminsToV_select] at hu
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨rfl, -, rfl, -⟩, rfl⟩ := hu
  have hcmp := immCmp_of_eval (op := .neOp) fc (ifPrem (hp _ (List.mem_singleton_self _)))
  exact ⟨ne_zero_of_cmp hcmp, by simp [adminsToV, adminToV_toAdmin]⟩

/-- `select-false`, read back. -/
theorem selectFalse_inv {v₁ v₂ : Val} {c : BitVec 32} {ts : Option (List V2.ValType)} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 4
      (.tuple [.list (adminsToV [v₁.toAdmin, v₂.toAdmin, constI32 c, .plain (.select ts)]), w])) :
    c = 0 ∧ w = .list (adminsToV [v₂.toAdmin]) := by
  obtain ⟨σ, hq, he, hp⟩ := firesB20_inv (hasRuleAt_selectFalse B) hf
  obtain ⟨u₁, f₁⟩ := quant_val (x := "val_1") (t := valT) hq (by simp)
  obtain ⟨u₂, f₂⟩ := quant_val (x := "val_2") (t := valT) hq (by simp)
  obtain ⟨vc, fc⟩ := quant_val (x := "c") (t := i32T) hq (by simp)
  obtain ⟨va, fa, ha⟩ := hq "t*?" valtypesOptT (by simp)
  obtain ⟨o, rfl⟩ := hasTyp_optList ha
  have hu := EvalExp.unique he (eval_select f₁ f₂ fc fa).2
  rw [adminsToV_select] at hu
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨-, rfl, rfl, -⟩, rfl⟩ := hu
  have hcmp := immCmp_of_eval (op := .eqOp) fc (ifPrem (hp _ (List.mem_singleton_self _)))
  exact ⟨eq_zero_of_cmp hcmp, by simp [adminsToV, adminToV_toAdmin]⟩

/-- The typings the `select` rules need. -/
structure SelectTyped (v₁ v₂ : Val) (c : BitVec 32) (ts : Option (List V2.ValType)) : Prop where
  h₁ : TypedV (simEnv20 B) valT (valV v₁)
  h₂ : TypedV (simEnv20 B) valT (valV v₂)
  hc : TypedV (simEnv20 B) i32T (pctV c.toNat)
  ht : TypedV (simEnv20 B) valtypesOptT (.opt ((selAnnot ts).map .list))

/-- The scope of the `select` rules at an encoded left-hand side. -/
def selectScope (v₁ v₂ : Val) (c : BitVec 32) (ts : Option (List V2.ValType)) : VarEnv :=
  VarEnv.empty.bindVals [("val_1", valV v₁), ("val_2", valV v₂), ("c", pctV c.toNat),
    ("t*?", .opt ((selAnnot ts).map .list))]

/-- The quantifiers of the `select` rules are typed in their scope. -/
theorem selectTyped_quants {v₁ v₂ : Val} {c : BitVec 32} {ts : Option (List V2.ValType)}
    (T : SelectTyped B v₁ v₂ c ts) :
    QuantsOk (simEnv20 B) (selectScope v₁ v₂ c ts)
      (match selectTrueRule with | .ruleD _ qs _ _ _ => qs) :=
  QuantsOk.cons rfl (T.h₁ _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (T.h₂ _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons rfl (T.hc _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (T.ht _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil)))

/-- `select-true`, fired. -/
theorem selectTrue_fires {v₁ v₂ : Val} {c : BitVec 32} {ts : Option (List V2.ValType)}
    (T : SelectTyped B v₁ v₂ c ts) (hc0 : c ≠ 0) :
    FiresB (simEnv20 B) "Step_pure" 3
      (.tuple [.list (adminsToV [v₁.toAdmin, v₂.toAdmin, constI32 c, .plain (.select ts)]),
        .list (adminsToV [v₁.toAdmin])]) := by
  have he := (eval_select (env := simEnv20 B) (ρ := selectScope v₁ v₂ c ts) rfl rfl rfl rfl).1
  rw [← adminsToV_select, show [valV v₁] = adminsToV [v₁.toAdmin] by
    simp [adminsToV, adminToV_toAdmin]] at he
  exact firesB20_of (hasRuleAt_selectTrue B) _ (selectTyped_quants B T) he
    (prems_one (.ifPr (evalExp_immCmp rfl (cmp_ne_zero hc0))))

/-- `select-false`, fired. -/
theorem selectFalse_fires {v₁ v₂ : Val} {ts : Option (List V2.ValType)}
    (T : SelectTyped B v₁ v₂ 0 ts) :
    FiresB (simEnv20 B) "Step_pure" 4
      (.tuple [.list (adminsToV [v₁.toAdmin, v₂.toAdmin, constI32 0, .plain (.select ts)]),
        .list (adminsToV [v₂.toAdmin])]) := by
  have he := (eval_select (env := simEnv20 B) (ρ := selectScope v₁ v₂ 0 ts) rfl rfl rfl rfl).2
  rw [← adminsToV_select, show [valV v₂] = adminsToV [v₂.toAdmin] by
    simp [adminsToV, adminToV_toAdmin]] at he
  exact firesB20_of (hasRuleAt_selectFalse B) _ (selectTyped_quants B T) he
    (prems_one (.ifPr (evalExp_immCmp rfl cmp_eq_zero)))

/-- **`Step_pure/select-true` is `PureStep.selectTrue`.** -/
theorem selectTrue_iff {v₁ v₂ : Val} {c : BitVec 32} {ts : Option (List V2.ValType)}
    (T : SelectTyped B v₁ v₂ c ts) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 3
        (.tuple [.list (adminsToV [v₁.toAdmin, v₂.toAdmin, constI32 c, .plain (.select ts)]), w]) ↔
      c ≠ 0 ∧ w = .list (adminsToV [v₁.toAdmin]) :=
  ⟨selectTrue_inv B, fun ⟨hc, hw⟩ => hw ▸ selectTrue_fires B T hc⟩

/-- **`Step_pure/select-false` is `PureStep.selectFalse`.** -/
theorem selectFalse_iff {v₁ v₂ : Val} {c : BitVec 32} {ts : Option (List V2.ValType)}
    (T : SelectTyped B v₁ v₂ c ts) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 4
        (.tuple [.list (adminsToV [v₁.toAdmin, v₂.toAdmin, constI32 c, .plain (.select ts)]), w]) ↔
      c = 0 ∧ w = .list (adminsToV [v₂.toAdmin]) :=
  ⟨selectFalse_inv B, fun ⟨hc, hw⟩ => by subst hc; exact hw ▸ selectFalse_fires B T⟩


/-! ## `if` -/

/-- The left-hand side of the `if` rules, encoded. -/
theorem adminsToV_if (c : BitVec 32) (bt : V2.BlockType) (b₁ b₂ : List V2.Instr) :
    adminsToV [constI32 c, .plain (.if_ bt b₁ b₂)] =
      [.case "CONST" (.tuple [caseNilV "I32", pctV c.toNat]),
        .case "IF%%ELSE%" (.tuple [blockTypeV bt, .list (instrsToV b₁), .list (instrsToV b₂)])] :=
  rfl

/-- The conclusions of `if-true`/`if-false`, evaluated. -/
theorem eval_if {env : Env} {ρ : VarEnv} {c bt : Value} {l₁ l₂ : List Value}
    (fc : ρ.findVal? "c" = some c) (fb : ρ.findVal? "bt" = some bt)
    (f₁ : ρ.findVal? "instr_1*" = some (.list l₁)) (f₂ : ρ.findVal? "instr_2*" = some (.list l₂)) :
    EvalExp env ρ (ruleConcl ifTrueRule)
        (.tuple [.list [.case "CONST" (.tuple [caseNilV "I32", c]),
          .case "IF%%ELSE%" (.tuple [bt, .list l₁, .list l₂])],
          .list [.case "BLOCK" (.tuple [bt, .list l₁])]]) ∧
      EvalExp env ρ (ruleConcl ifFalseRule)
        (.tuple [.list [.case "CONST" (.tuple [caseNilV "I32", c]),
          .case "IF%%ELSE%" (.tuple [bt, .list l₁, .list l₂])],
          .list [.case "BLOCK" (.tuple [bt, .list l₂])]]) := by
  have e₁ := evalExp_iter (env := env) (x := "instr_1") (by decide) f₁
  have e₂ := evalExp_iter (env := env) (x := "instr_2") (by decide) f₂
  constructor
  · exact evalExp_tup2 (evalExp_list2 (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var fc)))
      (evalExp_case (evalExp_tup3 (evalExp_var fb) e₁ e₂)))
      (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fb) e₁)))
  · exact evalExp_tup2 (evalExp_list2 (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var fc)))
      (evalExp_case (evalExp_tup3 (evalExp_var fb) e₁ e₂)))
      (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fb) e₂)))

/-- `if-true`, read back. -/
theorem ifTrue_inv {c : BitVec 32} {bt : V2.BlockType} {b₁ b₂ : List V2.Instr} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 5
      (.tuple [.list (adminsToV [constI32 c, .plain (.if_ bt b₁ b₂)]), w])) :
    c ≠ 0 ∧ w = .list (adminsToV [.plain (.block bt b₁)]) := by
  obtain ⟨σ, hq, he, hp⟩ := firesB20_inv (hasRuleAt_ifTrue B) hf
  obtain ⟨vc, fc⟩ := quant_val (x := "c") (t := i32T) hq (by simp)
  obtain ⟨vb, fb⟩ := quant_val (x := "bt") (t := blocktypeT) hq (by simp)
  obtain ⟨l₁, f₁⟩ := quant_list (x := "instr_1*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨l₂, f₂⟩ := quant_list (x := "instr_2*") (t := .varT "instr" []) hq (by simp)
  have hu := EvalExp.unique he (eval_if fc fb f₁ f₂).1
  rw [adminsToV_if] at hu
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := hu
  have hcmp := immCmp_of_eval (op := .neOp) fc (ifPrem (hp _ (List.mem_singleton_self _)))
  exact ⟨ne_zero_of_cmp hcmp, rfl⟩

/-- `if-false`, read back. -/
theorem ifFalse_inv {c : BitVec 32} {bt : V2.BlockType} {b₁ b₂ : List V2.Instr} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 6
      (.tuple [.list (adminsToV [constI32 c, .plain (.if_ bt b₁ b₂)]), w])) :
    c = 0 ∧ w = .list (adminsToV [.plain (.block bt b₂)]) := by
  obtain ⟨σ, hq, he, hp⟩ := firesB20_inv (hasRuleAt_ifFalse B) hf
  obtain ⟨vc, fc⟩ := quant_val (x := "c") (t := i32T) hq (by simp)
  obtain ⟨vb, fb⟩ := quant_val (x := "bt") (t := blocktypeT) hq (by simp)
  obtain ⟨l₁, f₁⟩ := quant_list (x := "instr_1*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨l₂, f₂⟩ := quant_list (x := "instr_2*") (t := .varT "instr" []) hq (by simp)
  have hu := EvalExp.unique he (eval_if fc fb f₁ f₂).2
  rw [adminsToV_if] at hu
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := hu
  have hcmp := immCmp_of_eval (op := .eqOp) fc (ifPrem (hp _ (List.mem_singleton_self _)))
  exact ⟨eq_zero_of_cmp hcmp, rfl⟩

/-- The typings the `if` rules need. -/
structure IfTyped (c : BitVec 32) (bt : V2.BlockType) (b₁ b₂ : List V2.Instr) : Prop where
  hc : TypedV (simEnv20 B) i32T (pctV c.toNat)
  hb : TypedV (simEnv20 B) blocktypeT (blockTypeV bt)
  h₁ : TypedV (simEnv20 B) instrsT (.list (instrsToV b₁))
  h₂ : TypedV (simEnv20 B) instrsT (.list (instrsToV b₂))

/-- The scope of the `if` rules at an encoded left-hand side. -/
def ifScope (c : BitVec 32) (bt : V2.BlockType) (b₁ b₂ : List V2.Instr) : VarEnv :=
  VarEnv.empty.bindVals [("c", pctV c.toNat), ("bt", blockTypeV bt),
    ("instr_1*", .list (instrsToV b₁)), ("instr_2*", .list (instrsToV b₂))]

/-- The quantifiers of the `if` rules are typed in their scope. -/
theorem ifTyped_quants {c : BitVec 32} {bt : V2.BlockType} {b₁ b₂ : List V2.Instr}
    (T : IfTyped B c bt b₁ b₂) :
    QuantsOk (simEnv20 B) (ifScope c bt b₁ b₂)
      (match ifTrueRule with | .ruleD _ qs _ _ _ => qs) :=
  QuantsOk.cons rfl (T.hc _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (T.hb _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons rfl (T.h₁ _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (T.h₂ _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil)))

/-- **`Step_pure/if-true` is `PureStep.ifTrue`.** -/
theorem ifTrue_iff {c : BitVec 32} {bt : V2.BlockType} {b₁ b₂ : List V2.Instr}
    (T : IfTyped B c bt b₁ b₂) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 5
        (.tuple [.list (adminsToV [constI32 c, .plain (.if_ bt b₁ b₂)]), w]) ↔
      c ≠ 0 ∧ w = .list (adminsToV [.plain (.block bt b₁)]) :=
  ⟨ifTrue_inv B, fun ⟨hc, hw⟩ => hw ▸ firesB20_of (hasRuleAt_ifTrue B) _ (ifTyped_quants B T)
    (eval_if (ρ := ifScope c bt b₁ b₂) rfl rfl rfl rfl).1
    (prems_one (.ifPr (evalExp_immCmp rfl (cmp_ne_zero hc))))⟩

/-- **`Step_pure/if-false` is `PureStep.ifFalse`.** -/
theorem ifFalse_iff {c : BitVec 32} {bt : V2.BlockType} {b₁ b₂ : List V2.Instr}
    (T : IfTyped B c bt b₁ b₂) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 6
        (.tuple [.list (adminsToV [constI32 c, .plain (.if_ bt b₁ b₂)]), w]) ↔
      c = 0 ∧ w = .list (adminsToV [.plain (.block bt b₂)]) :=
  ⟨ifFalse_inv B, fun ⟨hc, hw⟩ => by
    subst hc
    exact hw ▸ firesB20_of (hasRuleAt_ifFalse B) _ (ifTyped_quants B T)
      (eval_if (ρ := ifScope 0 bt b₁ b₂) rfl rfl rfl rfl).2
      (prems_one (.ifPr (evalExp_immCmp rfl cmp_eq_zero)))⟩

/-! ## `br_if` -/

/-- The conclusions of `br_if-true`/`br_if-false`, evaluated. -/
theorem eval_brIf {env : Env} {ρ : VarEnv} {c l : Value}
    (fc : ρ.findVal? "c" = some c) (fl : ρ.findVal? "l" = some l) :
    EvalExp env ρ (ruleConcl brIfTrueRule)
        (.tuple [.list [.case "CONST" (.tuple [caseNilV "I32", c]), .case "BR_IF" l],
          .list [.case "BR" l]]) ∧
      EvalExp env ρ (ruleConcl brIfFalseRule)
        (.tuple [.list [.case "CONST" (.tuple [caseNilV "I32", c]), .case "BR_IF" l], .list []]) :=
  ⟨evalExp_tup2 (evalExp_list2 (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var fc)))
      (evalExp_case (evalExp_var fl))) (evalExp_list1 (evalExp_case (evalExp_var fl))),
    evalExp_tup2 (evalExp_list2 (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var fc)))
      (evalExp_case (evalExp_var fl))) evalExp_list0⟩

/-- `br_if-true`, read back. -/
theorem brIfTrue_inv {c : BitVec 32} {l : LabelIdx} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 10
      (.tuple [.list (adminsToV [constI32 c, .plain (.brIf l)]), w])) :
    c ≠ 0 ∧ w = .list (adminsToV [.plain (.br l)]) := by
  obtain ⟨σ, hq, he, hp⟩ := firesB20_inv (hasRuleAt_brIfTrue B) hf
  obtain ⟨vc, fc⟩ := quant_val (x := "c") (t := i32T) hq (by simp)
  obtain ⟨vl, fl⟩ := quant_val (x := "l") (t := labelidxT) hq (by simp)
  have hu := EvalExp.unique he (eval_brIf fc fl).1
  simp only [adminsToV, adminToV, instrToV, valV, numV, numTypeV, Value.tuple.injEq,
    Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and, and_true] at hu
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hu
  have hcmp := immCmp_of_eval (op := .neOp) fc (ifPrem (hp _ (List.mem_singleton_self _)))
  exact ⟨ne_zero_of_cmp hcmp, rfl⟩

/-- `br_if-false`, read back. -/
theorem brIfFalse_inv {c : BitVec 32} {l : LabelIdx} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 11
      (.tuple [.list (adminsToV [constI32 c, .plain (.brIf l)]), w])) :
    c = 0 ∧ w = .list (adminsToV []) := by
  obtain ⟨σ, hq, he, hp⟩ := firesB20_inv (hasRuleAt_brIfFalse B) hf
  obtain ⟨vc, fc⟩ := quant_val (x := "c") (t := i32T) hq (by simp)
  obtain ⟨vl, fl⟩ := quant_val (x := "l") (t := labelidxT) hq (by simp)
  have hu := EvalExp.unique he (eval_brIf fc fl).2
  simp only [adminsToV, adminToV, instrToV, valV, numV, numTypeV, Value.tuple.injEq,
    Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and, and_true] at hu
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hu
  have hcmp := immCmp_of_eval (op := .eqOp) fc (ifPrem (hp _ (List.mem_singleton_self _)))
  exact ⟨eq_zero_of_cmp hcmp, rfl⟩

/-- The quantifiers of the `br_if` rules, typed in their scope. -/
theorem brIf_quants {c : BitVec 32} {l : LabelIdx} (hc : TypedV (simEnv20 B) i32T (pctV c.toNat))
    (hl : TypedV (simEnv20 B) labelidxT (idxV l)) :
    QuantsOk (simEnv20 B) (VarEnv.empty.bindVals [("c", pctV c.toNat), ("l", idxV l)])
      (match brIfTrueRule with | .ruleD _ qs _ _ _ => qs) :=
  QuantsOk.cons rfl (hc _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hl _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)

/-- **`Step_pure/br_if-true` is `PureStep.brIfTrue`.** -/
theorem brIfTrue_iff {c : BitVec 32} {l : LabelIdx} (hc : TypedV (simEnv20 B) i32T (pctV c.toNat))
    (hl : TypedV (simEnv20 B) labelidxT (idxV l)) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 10
        (.tuple [.list (adminsToV [constI32 c, .plain (.brIf l)]), w]) ↔
      c ≠ 0 ∧ w = .list (adminsToV [.plain (.br l)]) :=
  ⟨brIfTrue_inv B, fun ⟨h0, hw⟩ => hw ▸ firesB20_of (hasRuleAt_brIfTrue B) _ (brIf_quants B hc hl)
    (eval_brIf rfl rfl).1 (prems_one (.ifPr (evalExp_immCmp rfl (cmp_ne_zero h0))))⟩

/-- **`Step_pure/br_if-false` is `PureStep.brIfFalse`.** -/
theorem brIfFalse_iff {c : BitVec 32} {l : LabelIdx}
    (hc : TypedV (simEnv20 B) i32T (pctV c.toNat)) (hl : TypedV (simEnv20 B) labelidxT (idxV l))
    {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 11
        (.tuple [.list (adminsToV [constI32 c, .plain (.brIf l)]), w]) ↔
      c = 0 ∧ w = .list (adminsToV []) :=
  ⟨brIfFalse_inv B, fun ⟨h0, hw⟩ => by
    subst h0
    exact hw ▸ firesB20_of (hasRuleAt_brIfFalse B) _ (brIf_quants B hc hl) (eval_brIf rfl rfl).2
      (prems_one (.ifPr (evalExp_immCmp rfl cmp_eq_zero)))⟩

/-! ## `br_table` -/

/-- The left-hand side of the `br_table` rules, evaluated. -/
theorem eval_brTableLhs {env : Env} {ρ : VarEnv} {i l' : Value} {ls : List Value}
    (fi : ρ.findVal? "i" = some i) (fls : ρ.findVal? "l*" = some (.list ls))
    (fl' : ρ.findVal? "l'" = some l') :
    EvalExp env ρ (.listE [.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "i"]),
        .caseE "BR_TABLE" (.tupE [.iterE (.varE "l") (.mk .list [.mk "l" (.varE "l*")]),
          .varE "l'"])])
      (.list [.case "CONST" (.tuple [caseNilV "I32", i]), .case "BR_TABLE" (.tuple [.list ls, l'])]) :=
  evalExp_list2 (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var fi)))
    (evalExp_case (evalExp_tup2 (evalExp_iter (by decide) fls) (evalExp_var fl')))

/-- The `br_table` quantifiers, bound and read back at an encoded left-hand side. -/
theorem brTable_scope {i : BitVec 32} {ls : List LabelIdx} {l' : LabelIdx} {ρ : VarEnv}
    {qs : List Param} (hq : QuantsOk (simEnv20 B) ρ qs)
    (hi : Param.expP "i" i32T ∈ qs) (hls : Param.expP "l*" labelidxsT ∈ qs)
    (hl' : Param.expP "l'" labelidxT ∈ qs)
    (he : ∀ vi vl' xs, ρ.findVal? "i" = some vi → ρ.findVal? "l*" = some (.list xs) →
      ρ.findVal? "l'" = some vl' →
      Value.list (adminsToV [constI32 i, .plain (.brTable ls l')]) =
        .list [.case "CONST" (.tuple [caseNilV "I32", vi]), .case "BR_TABLE" (.tuple [.list xs, vl'])]) :
    ρ.findVal? "i" = some (pctV i.toNat) ∧ ρ.findVal? "l*" = some (.list (ls.map idxV)) := by
  obtain ⟨vi, fi⟩ := quant_val hq hi
  obtain ⟨xs, fls⟩ := quant_list hq hls
  obtain ⟨vl', fl'⟩ := quant_val hq hl'
  have hu := he vi vl' xs fi fls fl'
  simp only [adminsToV, adminToV, instrToV, valV, numV, numTypeV, Value.list.injEq,
    List.cons.injEq, Value.case.injEq, Value.tuple.injEq, true_and, and_true] at hu
  obtain ⟨rfl, rfl, -⟩ := hu
  exact ⟨fi, fls⟩

/-- `br_table-lt`, read back. -/
theorem brTableLt_inv {i : BitVec 32} {ls : List LabelIdx} {l' : LabelIdx} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 12
      (.tuple [.list (adminsToV [constI32 i, .plain (.brTable ls l')]), w])) :
    ∃ l, ls[i.toNat]? = some l ∧ w = .list (adminsToV [.plain (.br l)]) := by
  obtain ⟨σ, hq, he, -⟩ := firesB20_inv (hasRuleAt_brTableLt B) hf
  obtain ⟨hL, hR⟩ := evalExp_tup2_inv he
  obtain ⟨fi, fls⟩ := brTable_scope B hq (by simp) (by simp) (by simp)
    fun _ _ _ fi fls fl' => EvalExp.unique hL (eval_brTableLhs fi fls fl')
  obtain ⟨ws, hws, rfl⟩ := evalExp_listE_iff.1 hR
  obtain ⟨u, us, rfl, hu, hus⟩ := Equiv.Validation.evalExps_cons_iff.1 hws
  obtain ⟨rfl⟩ := Equiv.Validation.evalExps_nil_iff.1 hus
  obtain ⟨u', hu', rfl⟩ := evalExp_caseE_iff.1 hu
  obtain ⟨xs, k, hxs, hk, hidx⟩ := evalExp_idxE_iff.1 hu'
  have ek : k = i.toNat := by
    have := EvalExp.unique hk ((evalExp_imm_iff fi).2 ⟨[], rfl⟩)
    simpa using this
  have exs : xs = .list (ls.map idxV) := EvalExp.unique hxs (evalExp_iter (by decide) fls)
  subst ek exs
  obtain ⟨l, hl, rfl⟩ : ∃ l, ls[i.toNat]? = some l ∧ idxV l = u' := by
    simpa [Value.idx?, List.getElem?_map] using hidx
  exact ⟨l, hl, rfl⟩


/-- The typings the `br_table` rules need. -/
structure BrTableTyped (i : BitVec 32) (ls : List LabelIdx) (l' : LabelIdx) : Prop where
  hi : TypedV (simEnv20 B) i32T (pctV i.toNat)
  hls : TypedV (simEnv20 B) labelidxsT (.list (ls.map idxV))
  hl' : TypedV (simEnv20 B) labelidxT (idxV l')

/-- The scope of the `br_table` rules at an encoded left-hand side. -/
def brTableScope (i : BitVec 32) (ls : List LabelIdx) (l' : LabelIdx) : VarEnv :=
  VarEnv.empty.bindVals [("i", pctV i.toNat), ("l*", .list (ls.map idxV)), ("l'", idxV l')]

/-- The quantifiers of the `br_table` rules are typed in their scope. -/
theorem brTable_quants {i : BitVec 32} {ls : List LabelIdx} {l' : LabelIdx}
    (T : BrTableTyped B i ls l') :
    QuantsOk (simEnv20 B) (brTableScope i ls l')
      (match brTableLtRule with | .ruleD _ qs _ _ _ => qs) :=
  QuantsOk.cons rfl (T.hi _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (T.hls _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons rfl (T.hl' _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))

/-- `br_table-lt`, fired. -/
theorem brTableLt_fires {i : BitVec 32} {ls : List LabelIdx} {l l' : LabelIdx}
    (T : BrTableTyped B i ls l') (hl : ls[i.toNat]? = some l) :
    FiresB (simEnv20 B) "Step_pure" 12
      (.tuple [.list (adminsToV [constI32 i, .plain (.brTable ls l')]),
        .list (adminsToV [.plain (.br l)])]) := by
  have els : EvalExp (simEnv20 B) (brTableScope i ls l')
      (.iterE (.varE "l") (.mk .list [.mk "l" (.varE "l*")])) (.list (ls.map idxV)) :=
    evalExp_iter (by decide) rfl
  have hlt : i.toNat < ls.length := (List.getElem?_eq_some_iff.1 hl).1
  have hidx : (Value.list (ls.map idxV)).idx? i.toNat = some (idxV l) := by
    simp [Value.idx?, List.getElem?_map, hl]
  refine firesB20_of (hasRuleAt_brTableLt B) _ (brTable_quants B T)
    (evalExp_tup2 (eval_brTableLhs rfl rfl rfl) (evalExp_list1 (evalExp_case
      (evalExp_idxE_iff.2 ⟨_, _, els, (evalExp_imm_iff rfl).2 ⟨[], rfl⟩, hidx⟩))))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, (evalExp_imm_iff rfl).2 ⟨[], rfl⟩,
      evalExp_lenE_iff.2 ⟨_, els, rfl⟩, ?_⟩)))
  simp [cmpValues, Num.cmp, Res.ofOption, hlt]

/-- **`Step_pure/br_table-lt` is `PureStep.brTableLt`.** -/
theorem brTableLt_iff {i : BitVec 32} {ls : List LabelIdx} {l' : LabelIdx}
    (T : BrTableTyped B i ls l') {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 12
        (.tuple [.list (adminsToV [constI32 i, .plain (.brTable ls l')]), w]) ↔
      ∃ l, ls[i.toNat]? = some l ∧ w = .list (adminsToV [.plain (.br l)]) :=
  ⟨brTableLt_inv B, fun ⟨_, hl, hw⟩ => hw ▸ brTableLt_fires B T hl⟩

/-- `i >= |l*|`, read back. -/
theorem ge_of_cmp {env : Env} {ρ : VarEnv} {i : Nat} {ls : List Value}
    (fi : ρ.findVal? "i" = some (pctV i)) (fls : ρ.findVal? "l*" = some (.list ls))
    (h : EvalExp env ρ (.cmpE .geOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
      (.lenE (.iterE (.varE "l") (.mk .list [.mk "l" (.varE "l*")])))) (.bool true)) :
    ls.length ≤ i := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
  have e₁ : v₁ = .num (.natN i) := EvalExp.unique h₁ ((evalExp_imm_iff fi).2 ⟨[], rfl⟩)
  have e₂ : v₂ = .num (.natN ls.length) :=
    EvalExp.unique h₂ (evalExp_lenE_iff.2 ⟨_, evalExp_iter (by decide) fls, rfl⟩)
  subst e₁ e₂
  simpa [cmpValues, Num.cmp, Res.ofOption] using hc

/-- `br_table-ge`, read back. -/
theorem brTableGe_inv {i : BitVec 32} {ls : List LabelIdx} {l' : LabelIdx} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 13
      (.tuple [.list (adminsToV [constI32 i, .plain (.brTable ls l')]), w])) :
    ls.length ≤ i.toNat ∧ w = .list (adminsToV [.plain (.br l')]) := by
  obtain ⟨σ, hq, he, hp⟩ := firesB20_inv (hasRuleAt_brTableGe B) hf
  obtain ⟨vl', fl'⟩ := quant_val (x := "l'") (t := labelidxT) hq (by simp)
  obtain ⟨fi, fls⟩ := brTable_scope B hq (by simp) (by simp) (by simp)
    fun _ _ _ fi fls fl' => EvalExp.unique (evalExp_tup2_inv he).1 (eval_brTableLhs fi fls fl')
  have hu := EvalExp.unique he (evalExp_tup2 (eval_brTableLhs fi fls fl')
    (evalExp_list1 (evalExp_case (evalExp_var fl'))))
  simp only [adminsToV, adminToV, instrToV, valV, numV, numTypeV, Value.tuple.injEq,
    Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and, and_true] at hu
  obtain ⟨⟨-, rfl⟩, rfl⟩ := hu
  have hge := ge_of_cmp fi fls (ifPrem (hp _ (List.mem_singleton_self _)))
  exact ⟨by simpa using hge, rfl⟩

/-- `br_table-ge`, fired. -/
theorem brTableGe_fires {i : BitVec 32} {ls : List LabelIdx} {l' : LabelIdx}
    (T : BrTableTyped B i ls l') (hge : ls.length ≤ i.toNat) :
    FiresB (simEnv20 B) "Step_pure" 13
      (.tuple [.list (adminsToV [constI32 i, .plain (.brTable ls l')]),
        .list (adminsToV [.plain (.br l')])]) := by
  have els : EvalExp (simEnv20 B) (brTableScope i ls l')
      (.iterE (.varE "l") (.mk .list [.mk "l" (.varE "l*")])) (.list (ls.map idxV)) :=
    evalExp_iter (by decide) rfl
  refine firesB20_of (hasRuleAt_brTableGe B) _ (brTable_quants B T)
    (evalExp_tup2 (eval_brTableLhs rfl rfl rfl) (evalExp_list1 (evalExp_case (evalExp_var rfl))))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, (evalExp_imm_iff rfl).2 ⟨[], rfl⟩,
      evalExp_lenE_iff.2 ⟨_, els, rfl⟩, ?_⟩)))
  simp [cmpValues, Num.cmp, Res.ofOption, hge]

/-- **`Step_pure/br_table-ge` is `PureStep.brTableGe`.** -/
theorem brTableGe_iff {i : BitVec 32} {ls : List LabelIdx} {l' : LabelIdx}
    (T : BrTableTyped B i ls l') {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 13
        (.tuple [.list (adminsToV [constI32 i, .plain (.brTable ls l')]), w]) ↔
      ls.length ≤ i.toNat ∧ w = .list (adminsToV [.plain (.br l')]) :=
  ⟨brTableGe_inv B, fun ⟨hge, hw⟩ => hw ▸ brTableGe_fires B T hge⟩

/-! ## `label-vals`, `frame-vals` -/

/-- The conclusion of `label-vals`, evaluated. -/
theorem eval_labelVals {env : Env} {ρ : VarEnv} {n : Value} {cont vs : List Value}
    (fn : ρ.findVal? "n" = some n) (fc : ρ.findVal? "instr*" = some (.list cont))
    (fv : ρ.findVal? "val*" = some (.list vs)) :
    EvalExp env ρ (ruleConcl labelValsRule)
      (.tuple [.list [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list vs])], .list vs]) :=
  evalExp_tup2 (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
    (evalExp_iter (by decide) fc) (evalExp_vals (by decide) fv)))) (evalExp_vals (by decide) fv)

/-- `label-vals`, read back. -/
theorem labelVals_inv {n : Nat} {cont : List V2.Instr} {vs : List Val} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 7
      (.tuple [.list (adminsToV [.label n cont (vals vs)]), w])) :
    w = .list (adminsToV (vals vs)) := by
  obtain ⟨σ, hq, he, -⟩ := firesB20_inv (hasRuleAt_labelVals B) hf
  obtain ⟨vn, fn⟩ := quant_val (x := "n") (t := nT) hq (by simp)
  obtain ⟨cs, fc⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨xs, fv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq (by simp)
  have hu := EvalExp.unique he (eval_labelVals fn fc fv)
  simp only [adminsToV, adminToV, Value.tuple.injEq, Value.list.injEq, List.cons.injEq,
    Value.case.injEq, true_and, and_true] at hu
  obtain ⟨⟨-, -, rfl⟩, rfl⟩ := hu
  rfl

/-- **`Step_pure/label-vals` is `PureStep.labelVals`.** -/
theorem labelVals_iff {n : Nat} {cont : List V2.Instr} {vs : List Val}
    (hn : TypedV (simEnv20 B) nT (.num (.natN n)))
    (hc : TypedV (simEnv20 B) instrsT (.list (instrsToV cont)))
    (hv : TypedV (simEnv20 B) valsT (.list (adminsToV (vals vs)))) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 7
        (.tuple [.list (adminsToV [.label n cont (vals vs)]), w]) ↔
      w = .list (adminsToV (vals vs)) :=
  ⟨labelVals_inv B, fun hw => hw ▸ firesB20_of (hasRuleAt_labelVals B)
    [("n", .num (.natN n)), ("instr*", .list (instrsToV cont)), ("val*", .list (adminsToV (vals vs)))]
    (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hc _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (hv _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))
    (eval_labelVals rfl rfl rfl) prems_nil⟩

/-- The conclusion of `frame-vals`, evaluated. -/
theorem eval_frameVals {env : Env} {ρ : VarEnv} {f : Value} {vs : List Value}
    (fn : ρ.findVal? "n" = some (.num (.natN vs.length))) (ff : ρ.findVal? "f" = some f)
    (fv : ρ.findVal? "val*" = some (.list vs)) :
    EvalExp env ρ (ruleConcl frameValsRule)
      (.tuple [.list [.case "FRAME_%{%}%" (.tuple [.num (.natN vs.length), f, .list vs])],
        .list vs]) :=
  evalExp_tup2 (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) (evalExp_var ff)
    (evalExp_valsN (by decide) fn fv)))) (evalExp_valsN (by decide) fn fv)

/-- `frame-vals`, read back. -/
theorem frameVals_inv {n : Nat} {fr : Frame} {vs : List Val} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 14
      (.tuple [.list (adminsToV [.frame n fr (vals vs)]), w])) :
    vs.length = n ∧ w = .list (adminsToV (vals vs)) := by
  obtain ⟨σ, hq, he, -⟩ := firesB20_inv (hasRuleAt_frameVals B) hf
  obtain ⟨vf, ff⟩ := quant_val (x := "f") (t := frameT) hq (by simp)
  obtain ⟨xs, fv, fn, -⟩ := evalExp_valsN_inv (by decide) (evalExp_tup2_inv he).2
  have hu := EvalExp.unique he (eval_frameVals fn ff fv)
  simp only [adminsToV, adminToV, Value.tuple.injEq, Value.list.injEq, List.cons.injEq,
    Value.case.injEq, Value.num.injEq, Num.natN.injEq, true_and, and_true] at hu
  obtain ⟨⟨hn, -, rfl⟩, rfl⟩ := hu
  exact ⟨by rw [hn, adminsToV_vals_length], rfl⟩

/-- `frame-vals`, fired. -/
theorem frameVals_fires {fr : Frame} {vs : List Val}
    (hn : TypedV (simEnv20 B) nT (.num (.natN vs.length)))
    (hfr : TypedV (simEnv20 B) frameT (frameV fr))
    (hv : TypedV (simEnv20 B) valsT (.list (adminsToV (vals vs)))) :
    FiresB (simEnv20 B) "Step_pure" 14
      (.tuple [.list (adminsToV [.frame vs.length fr (vals vs)]), .list (adminsToV (vals vs))]) := by
  have hl : (adminsToV (vals vs)).length = vs.length := adminsToV_vals_length vs
  have fn : (VarEnv.empty.bindVals [("n", .num (.natN vs.length)), ("f", frameV fr),
      ("val*", .list (adminsToV (vals vs)))]).findVal? "n" =
      some (.num (.natN (adminsToV (vals vs)).length)) := by
    rw [hl]; rfl
  have he := eval_frameVals (env := simEnv20 B) fn rfl rfl
  rw [hl] at he
  exact firesB20_of (hasRuleAt_frameVals B) _ (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons rfl (hfr _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hv _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))) he prems_nil

/-- **`Step_pure/frame-vals` is `PureStep.frameVals`.** -/
theorem frameVals_iff {n : Nat} {fr : Frame} {vs : List Val}
    (hn : TypedV (simEnv20 B) nT (.num (.natN n))) (hfr : TypedV (simEnv20 B) frameT (frameV fr))
    (hv : TypedV (simEnv20 B) valsT (.list (adminsToV (vals vs)))) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 14
        (.tuple [.list (adminsToV [.frame n fr (vals vs)]), w]) ↔
      vs.length = n ∧ w = .list (adminsToV (vals vs)) :=
  ⟨frameVals_inv B, fun ⟨hl, hw⟩ => by
    subst hl hw
    exact frameVals_fires B hn hfr hv⟩

/-! ## `trap-label`, `trap-frame` -/

/-- `trap-label`, read back. -/
theorem trapLabel_inv {n : Nat} {cont : List V2.Instr} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 18
      (.tuple [.list (adminsToV [.label n cont [.trap]]), w])) :
    w = .list (adminsToV [.trap]) := by
  obtain ⟨σ, hq, he, -⟩ := firesB20_inv (hasRuleAt_trapLabel B) hf
  obtain ⟨vn, fn⟩ := quant_val (x := "n") (t := nT) hq (by simp)
  obtain ⟨cs, fc⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq (by simp)
  have hu := EvalExp.unique he (evalExp_tup2 (evalExp_list1 (evalExp_case (evalExp_tup3
    (evalExp_var fn) (evalExp_iter (by decide) fc) (evalExp_list1 evalExp_caseNil))))
    (evalExp_list1 evalExp_caseNil))
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hu
  exact hu.2

/-- **`Step_pure/trap-label` is `PureStep.trapLabel`.** -/
theorem trapLabel_iff {n : Nat} {cont : List V2.Instr}
    (hn : TypedV (simEnv20 B) nT (.num (.natN n)))
    (hc : TypedV (simEnv20 B) instrsT (.list (instrsToV cont))) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 18
        (.tuple [.list (adminsToV [.label n cont [.trap]]), w]) ↔
      w = .list (adminsToV [.trap]) :=
  ⟨trapLabel_inv B, fun hw => hw ▸ firesB20_of (hasRuleAt_trapLabel B)
    [("n", .num (.natN n)), ("instr'*", .list (instrsToV cont))]
    (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hc _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var rfl)
      (evalExp_iter (by decide) rfl) (evalExp_list1 evalExp_caseNil))))
      (evalExp_list1 evalExp_caseNil)) prems_nil⟩

/-- `trap-frame`, read back. -/
theorem trapFrame_inv {n : Nat} {fr : Frame} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 19
      (.tuple [.list (adminsToV [.frame n fr [.trap]]), w])) :
    w = .list (adminsToV [.trap]) := by
  obtain ⟨σ, hq, he, -⟩ := firesB20_inv (hasRuleAt_trapFrame B) hf
  obtain ⟨vn, fn⟩ := quant_val (x := "n") (t := nT) hq (by simp)
  obtain ⟨vf, ff⟩ := quant_val (x := "f") (t := frameT) hq (by simp)
  have hu := EvalExp.unique he (evalExp_tup2 (evalExp_list1 (evalExp_case (evalExp_tup3
    (evalExp_var fn) (evalExp_var ff) (evalExp_list1 evalExp_caseNil))))
    (evalExp_list1 evalExp_caseNil))
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hu
  exact hu.2

/-- **`Step_pure/trap-frame` is `PureStep.trapFrame`.** -/
theorem trapFrame_iff {n : Nat} {fr : Frame} (hn : TypedV (simEnv20 B) nT (.num (.natN n)))
    (hfr : TypedV (simEnv20 B) frameT (frameV fr)) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 19
        (.tuple [.list (adminsToV [.frame n fr [.trap]]), w]) ↔
      w = .list (adminsToV [.trap]) :=
  ⟨trapFrame_inv B, fun hw => hw ▸ firesB20_of (hasRuleAt_trapFrame B)
    [("n", .num (.natN n)), ("f", frameV fr)]
    (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hfr _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var rfl)
      (evalExp_var rfl) (evalExp_list1 evalExp_caseNil))))
      (evalExp_list1 evalExp_caseNil)) prems_nil⟩

end Silmaril.Wasm.SpecTec.Sim20.Pure
