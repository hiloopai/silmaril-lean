module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureSplit
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Exn.Invert

/-!
# The concatenation rules of wasm-2.0 `Step_pure`, rule by rule

`br-zero` (8), `br-succ` (9), `return-frame` (15), `return-label` (16) and `trap-vals` (17).
Each left-hand side is a concatenation `val* M instr*`; the V2 constructor that transcribes the
rule fixes one split of a code sequence, the IL rule another, and `split_unique` (with the marker
`M` not a value and every IL `val` a value head) identifies them.

Each `*_iff` is stated at the image of an arbitrary V2 code sequence of the constructor's shape,
with the value prefix written as one sequence `us`; where the rule splits that prefix further
(`val'* val^n`), the iff says how. Each `*_step` turns the right-hand side of the iff into the V2
step, so `*_iff` and `*_step` together give both simulation directions. Only the V2 → SpecTec half
needs typing hypotheses, for the rule's quantified variables.

The tails `instr*` are quantified at the IL type `instr*`, while V2 allows any administrative tail
(`rest : List Admin`): the typing hypothesis on the tail (`TypedV instrsT (.list (adminsToV rest))`)
is where the two differ, and only the V2 → SpecTec half uses it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Pure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV evalExp_imm_iff)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk TypedV ValsOnly evalExp_tup2 evalExp_tup3 evalExp_list1
  evalExp_case evalExp_cat evalExp_ne_nil evalExp_or)
open Silmaril.Wasm.SpecTec.Sim.Exn (evalExp_case_inv evalExp_cat_inv evalExp_list1_inv
  evalExp_list1_len evalExp_tup3_inv)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (FiresB ruleConcl)

variable (B : Builtins)

/-! ## Evaluation helpers -/

/-- A `*` iteration of a subsort coercion over a bound list. -/
theorem evalExp_subIter {env : Env} {ρ : VarEnv} {x y : IL.Id} {t₁ t₂ : Typ} (hx : x ≠ "_")
    {vs : List Value} (h : ρ.findVal? y = some (.list vs)) :
    EvalExp env ρ (.iterE (.subE (.varE x) t₁ t₂) (.mk .list [.mk x (.varE y)])) (.list vs) :=
  Equiv.Execution.evalExp_iterBody_var (d := 1)
    (fun σ w hw => by simp [evalExp, hw, Res.ofOption]) hx h

/-- The numeral `%(k)`. -/
theorem evalExp_pct {env : Env} {ρ : VarEnv} (k : Nat) :
    EvalExp env ρ (.caseE "%" (.tupE [.numE (.natN k)])) (pctV k) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_numE_iff.2 rfl) evalExps_nil, rfl⟩)

/-- The successor index `%(l!%.0 + 1)` of `br-succ`. -/
theorem evalExp_succIdx {env : Env} {ρ : VarEnv} {k : Nat} (hl : ρ.findVal? "l" = some (pctV k)) :
    EvalExp env ρ (.caseE "%" (.tupE [.binE .addOp (.numT .natT)
      (.projE (.uncaseE (.varE "l") "%") 0) (.numE (.natN 1))])) (pctV (k + 1)) := by
  have hp : EvalExp env ρ (.projE (.uncaseE (.varE "l") "%") 0) (.num (.natN k)) :=
    (evalExp_imm_iff hl).2 ⟨[], rfl⟩
  have h₁ : EvalExp env ρ (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "l") "%") 0)
      (.numE (.natN 1))) (.num (.natN (k + 1))) := by
    refine evalExp_binE_iff.2 ⟨_, hp, .inr ⟨?_, _, evalExp_numE_iff.2 rfl, ?_⟩⟩
    · simp [boolShort]
    · simp [binValues, Num.bin, Res.ofOption]
  exact evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons h₁ evalExps_nil, rfl⟩)

/-- A quantified `*` variable is bound to a typed list. -/
theorem quant_listT {env : Env} {ρ : VarEnv} {qs : List Param} {x : IL.Id} {t : Typ}
    (hq : QuantsOk env ρ qs) (hm : Param.expP x (.iterT t .list) ∈ qs) :
    ∃ l, ρ.findVal? x = some (.list l) ∧ HasTyp env ρ (.iterT t .list) (.list l) := by
  obtain ⟨v, hv, ht⟩ := hq x _ hm
  obtain ⟨l, rfl⟩ := hasTyp_list_isList ht
  exact ⟨l, hv, ht⟩

/-- `val* =/= [] \/ instr* =/= []`, read back. -/
theorem or_of_eval {env : Env} {ρ : VarEnv} {ws is : List Value}
    (fv : ρ.findVal? "val*" = some (.list ws)) (fi : ρ.findVal? "instr*" = some (.list is))
    (h : EvalExp env ρ (.binE .orOp .boolT
      (.cmpE .neOp .boolT (Equiv.Execution.iterPat "val" "val*") (.listE []))
      (.cmpE .neOp .boolT (Equiv.Execution.iterPat "instr" "instr*") (.listE []))) (.bool true)) :
    ws ≠ [] ∨ is ≠ [] := by
  have e : EvalExp env ρ (.binE .orOp .boolT
      (.cmpE .neOp .boolT (Equiv.Execution.iterPat "val" "val*") (.listE []))
      (.cmpE .neOp .boolT (Equiv.Execution.iterPat "instr" "instr*") (.listE [])))
      (.bool (decide (ws ≠ [] ∨ is ≠ []))) :=
    evalExp_or (evalExp_ne_nil (Equiv.Execution.evalExp_iterPat (by decide) fv))
      (evalExp_ne_nil (Equiv.Execution.evalExp_iterPat (by decide) fi))
  exact of_decide_eq_true (Value.bool.inj (EvalExp.unique e h))

/-- Typing of a value sequence from typing of its values. -/
theorem typedV_vals {env : Env} {vs : List Val} (h : ∀ v ∈ vs, TypedV env valT (valV v)) :
    TypedV env valsT (.list (adminsToV (vals vs))) := fun ρ hρ => by
  refine hasTyp_iterT_list_iff.2 ⟨_, rfl, hasTypList_iff.2 fun u hu => ?_⟩
  rw [adminsToV_vals] at hu
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
  exact h v hv ρ hρ

/-- The image of a label. -/
theorem adminsToV_label (n : Nat) (cont : List V2.Instr) (body : List Admin) :
    adminsToV [.label n cont body] =
      [.case "LABEL_%{%}%" (.tuple [.num (.natN n), .list (instrsToV cont), .list (adminsToV body)])] :=
  rfl

/-- The image of a frame. -/
theorem adminsToV_frame (n : Nat) (fr : Frame) (body : List Admin) :
    adminsToV [.frame n fr body] =
      [.case "FRAME_%{%}%" (.tuple [.num (.natN n), frameV fr, .list (adminsToV body)])] :=
  rfl

/-- The image of `val* M rest`, in the shape `split_unique` reads. -/
theorem adminsToV_marked (us : List Val) (m : Admin) (rest : List Admin) :
    adminsToV (vals us ++ [m] ++ rest) = adminsToV (vals us) ++ adminToV m :: adminsToV rest := by
  rw [adminsToV_append, adminsToV_append, List.append_assoc]
  rfl

/-- `pctV` is injective. -/
theorem pctV_inj {a b : Nat} (h : pctV a = pctV b) : a = b := by
  simp only [pctV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.num.injEq,
    Num.natN.injEq, and_true, true_and] at h
  exact h

/-- Read back a typed IL value prefix `ws₁ ++ ws` against a V2 image `vals us ++ M ++ rest`. -/
theorem marked_split {us : List Val} {m : Admin} {rest : List Admin}
    {ws rs : List Value} {x : Value}
    (h : adminsToV (vals us ++ [m] ++ rest) = ws ++ x :: rs)
    (hws : ∀ u ∈ ws, ValHead u) (hm : ¬ ValHead (adminToV m)) (hx : ¬ ValHead x) :
    adminsToV (vals us) = ws ∧ adminToV m = x ∧ adminsToV rest = rs := by
  rw [adminsToV_marked] at h
  exact split_unique (valHead_vals us) hws hm hx h

/-! ## `trap-vals` (17) -/

/-- The conclusion of `trap-vals`, evaluated. -/
theorem eval_trapVals {env : Env} {ρ : VarEnv} {ws rs : List Value}
    (fv : ρ.findVal? "val*" = some (.list ws)) (fi : ρ.findVal? "instr*" = some (.list rs)) :
    EvalExp env ρ (ruleConcl trapValsRule)
      (.tuple [.list (ws ++ caseNilV "TRAP" :: rs), .list [caseNilV "TRAP"]]) :=
  evalExp_tup2 (evalExp_cat (evalExp_subIter (by decide) fv)
    (evalExp_cat (evalExp_list1 evalExp_caseNil) (evalExp_subIter (by decide) fi)))
    (evalExp_list1 evalExp_caseNil)

/-- `trap-vals`, read back. -/
theorem trapVals_inv {vs : List Val} {rest : List Admin} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 17
      (.tuple [.list (adminsToV (vals vs ++ [.trap] ++ rest)), w])) :
    (vs ≠ [] ∨ rest ≠ []) ∧ w = .list (adminsToV [.trap]) := by
  obtain ⟨σ, hq, he, hp⟩ := firesB20_inv (hasRuleAt_trapVals B) hf
  obtain ⟨ws, fv, htv⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨rs, fi⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (by simp)
  have hu := EvalExp.unique he (eval_trapVals fv fi)
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hu
  obtain ⟨hl, rfl⟩ := hu
  obtain ⟨h₁, -, h₃⟩ := marked_split (Value.list.inj hl)
    (valHeads_of_typed (valsOnly_bindVals σ) htv) not_valHead_trap not_valHead_trap
  have hor := or_of_eval fv fi (ifPrem (hp _ (List.mem_singleton_self _)))
  refine ⟨?_, rfl⟩
  rcases hor with h | h
  · left
    rintro rfl
    exact h h₁.symm
  · right
    rintro rfl
    exact h h₃.symm

/-- `trap-vals`, fired. -/
theorem trapVals_fires {vs : List Val} {rest : List Admin} (hne : vs ≠ [] ∨ rest ≠ [])
    (hv : TypedV (simEnv20 B) valsT (.list (adminsToV (vals vs))))
    (hr : TypedV (simEnv20 B) instrsT (.list (adminsToV rest))) :
    FiresB (simEnv20 B) "Step_pure" 17
      (.tuple [.list (adminsToV (vals vs ++ [.trap] ++ rest)), .list (adminsToV [.trap])]) := by
  let σ : List (IL.Id × Value) :=
    [("val*", .list (adminsToV (vals vs))), ("instr*", .list (adminsToV rest))]
  have fv : (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list (adminsToV (vals vs))) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "instr*" = some (.list (adminsToV rest)) := rfl
  have he := eval_trapVals (env := simEnv20 B) fv fi
  rw [adminsToV_marked]
  have hne' : decide (adminsToV (vals vs) ≠ [] ∨ adminsToV rest ≠ []) = true := by
    rw [adminsToV_vals, adminsToV_eq_map rest]
    simpa [List.map_eq_nil_iff] using hne
  have hpr : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) (.binE .orOp .boolT
      (.cmpE .neOp .boolT (Equiv.Execution.iterPat "val" "val*") (.listE []))
      (.cmpE .neOp .boolT (Equiv.Execution.iterPat "instr" "instr*") (.listE []))) (.bool true) :=
    hne' ▸ evalExp_or (evalExp_ne_nil (Equiv.Execution.evalExp_iterPat (by decide) fv))
      (evalExp_ne_nil (Equiv.Execution.evalExp_iterPat (by decide) fi))
  exact firesB20_of (hasRuleAt_trapVals B) σ (QuantsOk.cons fv (hv _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons fi (hr _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)) he (prems_one (.ifPr hpr))

/-- **`Step_pure/trap-vals` is `PureStep.trapVals`.** -/
theorem trapVals_iff {vs : List Val} {rest : List Admin}
    (hv : TypedV (simEnv20 B) valsT (.list (adminsToV (vals vs))))
    (hr : TypedV (simEnv20 B) instrsT (.list (adminsToV rest))) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 17
        (.tuple [.list (adminsToV (vals vs ++ [.trap] ++ rest)), w]) ↔
      (vs ≠ [] ∨ rest ≠ []) ∧ w = .list (adminsToV [.trap]) :=
  ⟨trapVals_inv B, fun ⟨hne, hw⟩ => hw ▸ trapVals_fires B hne hv hr⟩

/-! ## `return-label` (16) -/

/-- The conclusion of `return-label`, evaluated. -/
theorem eval_returnLabel {env : Env} {ρ : VarEnv} {n : Value} {cs ws rs : List Value}
    (fn : ρ.findVal? "n" = some n) (fc : ρ.findVal? "instr'*" = some (.list cs))
    (fv : ρ.findVal? "val*" = some (.list ws)) (fi : ρ.findVal? "instr*" = some (.list rs)) :
    EvalExp env ρ (ruleConcl returnLabelRule)
      (.tuple [.list [.case "LABEL_%{%}%" (.tuple [n, .list cs,
        .list (ws ++ [caseNilV "RETURN"] ++ rs)])], .list (ws ++ [caseNilV "RETURN"])]) :=
  evalExp_tup2 (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
    (evalExp_iter (by decide) fc) (evalExp_cat (evalExp_cat (evalExp_subIter (by decide) fv)
      (evalExp_list1 evalExp_caseNil)) (evalExp_subIter (by decide) fi)))))
    (evalExp_cat (evalExp_subIter (by decide) fv) (evalExp_list1 evalExp_caseNil))

/-- `return-label`, read back. -/
theorem returnLabel_inv {n : Nat} {cont : List V2.Instr} {vs : List Val} {rest : List Admin}
    {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 16
      (.tuple [.list (adminsToV [.label n cont (vals vs ++ [.plain .return_] ++ rest)]), w])) :
    w = .list (adminsToV (vals vs ++ [.plain .return_])) := by
  obtain ⟨σ, hq, he, -⟩ := firesB20_inv (hasRuleAt_returnLabel B) hf
  obtain ⟨vn, fn⟩ := quant_val (x := "n") (t := nT) hq (by simp)
  obtain ⟨cs, fc⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws, fv, htv⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨rs, fi⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (by simp)
  have hu := EvalExp.unique he (eval_returnLabel fn fc fv fi)
  rw [adminsToV_label] at hu
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨-, -, hb⟩, rfl⟩ := hu
  obtain ⟨h₁, -, -⟩ := marked_split (m := .plain .return_) (by simpa using hb)
    (valHeads_of_typed (valsOnly_bindVals σ) htv) not_valHead_return not_valHead_return
  rw [adminsToV_append, h₁]
  rfl

/-- `return-label`, fired. -/
theorem returnLabel_fires {n : Nat} {cont : List V2.Instr} {vs : List Val} {rest : List Admin}
    (hn : TypedV (simEnv20 B) nT (.num (.natN n)))
    (hc : TypedV (simEnv20 B) instrsT (.list (instrsToV cont)))
    (hv : TypedV (simEnv20 B) valsT (.list (adminsToV (vals vs))))
    (hr : TypedV (simEnv20 B) instrsT (.list (adminsToV rest))) :
    FiresB (simEnv20 B) "Step_pure" 16
      (.tuple [.list (adminsToV [.label n cont (vals vs ++ [.plain .return_] ++ rest)]),
        .list (adminsToV (vals vs ++ [.plain .return_]))]) := by
  let σ : List (IL.Id × Value) := [("n", .num (.natN n)), ("instr'*", .list (instrsToV cont)),
    ("val*", .list (adminsToV (vals vs))), ("instr*", .list (adminsToV rest))]
  have he := eval_returnLabel (env := simEnv20 B) (ρ := VarEnv.empty.bindVals σ) rfl rfl rfl rfl
  have e₁ : adminsToV (vals vs ++ [.plain .return_] ++ rest) =
      adminsToV (vals vs) ++ [caseNilV "RETURN"] ++ adminsToV rest := by
    rw [adminsToV_append, adminsToV_append]; rfl
  have e₂ : adminsToV (vals vs ++ [.plain .return_]) = adminsToV (vals vs) ++ [caseNilV "RETURN"] := by
    rw [adminsToV_append]; rfl
  rw [adminsToV_label, e₁, e₂]
  exact firesB20_of (hasRuleAt_returnLabel B) σ (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons rfl (hc _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hv _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (hr _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))) he prems_nil

/-- **`Step_pure/return-label` is `PureStep.returnLabel`.** -/
theorem returnLabel_iff {n : Nat} {cont : List V2.Instr} {vs : List Val} {rest : List Admin}
    (hn : TypedV (simEnv20 B) nT (.num (.natN n)))
    (hc : TypedV (simEnv20 B) instrsT (.list (instrsToV cont)))
    (hv : TypedV (simEnv20 B) valsT (.list (adminsToV (vals vs))))
    (hr : TypedV (simEnv20 B) instrsT (.list (adminsToV rest))) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 16
        (.tuple [.list (adminsToV [.label n cont (vals vs ++ [.plain .return_] ++ rest)]), w]) ↔
      w = .list (adminsToV (vals vs ++ [.plain .return_])) :=
  ⟨returnLabel_inv B, fun hw => hw ▸ returnLabel_fires B hn hc hv hr⟩

/-- A label conclusion `[LABEL_nv{cs} b], W` read against a V2 label image. -/
theorem label_concl_inj {n : Nat} {cont : List V2.Instr} {body : List Admin} {w nv W : Value}
    {cs b : List Value}
    (h : Value.tuple [.list (adminsToV [.label n cont body]), w] =
      .tuple [.list [.case "LABEL_%{%}%" (.tuple [nv, .list cs, .list b])], W]) :
    .num (.natN n) = nv ∧ instrsToV cont = cs ∧ adminsToV body = b ∧ w = W := by
  have h' : (.num (.natN n) = nv ∧ instrsToV cont = cs ∧ adminsToV body = b) ∧ w = W := by
    simpa only [adminsToV_label, Value.tuple.injEq, Value.list.injEq, List.cons.injEq,
      Value.case.injEq, true_and, and_true] using h
  exact ⟨h'.1.1, h'.1.2.1, h'.1.2.2, h'.2⟩

/-! ## `br-zero` (8) -/

/-- `vals` distributes over `++`. -/
theorem vals_append (vs' vs : List Val) : vals (vs' ++ vs) = vals vs' ++ vals vs :=
  List.map_append ..

/-- Typing of the two halves of a typed value sequence. -/
theorem typedV_vals_split {env : Env} {vs' vs : List Val}
    (h : ∀ v ∈ vs' ++ vs, TypedV env valT (valV v)) :
    TypedV env valsT (.list (adminsToV (vals vs'))) ∧
      TypedV env valsT (.list (adminsToV (vals vs))) :=
  ⟨typedV_vals fun v hv => h v (List.mem_append_left _ hv),
    typedV_vals fun v hv => h v (List.mem_append_right _ hv)⟩

/-- Value heads of `ws₁ ++ ws`, from the typings of both. -/
theorem valHeads_append {σ : List (IL.Id × Value)} {ws₁ ws : List Value}
    (h₁ : HasTyp (simEnv20 B) (VarEnv.empty.bindVals σ) valsT (.list ws₁))
    (h : HasTyp (simEnv20 B) (VarEnv.empty.bindVals σ) valsT (.list ws)) :
    ∀ u ∈ ws₁ ++ ws, ValHead u := fun u hu =>
  (List.mem_append.1 hu).elim (valHeads_of_typed (valsOnly_bindVals σ) h₁ u)
    (valHeads_of_typed (valsOnly_bindVals σ) h u)

/-- `BR l`'s image. -/
theorem adminToV_br (l : LabelIdx) : adminToV (.plain (.br l)) = .case "BR" (pctV l.toNat) := rfl

/-- The conclusion of `br-zero`, evaluated. -/
theorem eval_brZero {env : Env} {ρ : VarEnv} {cs ws₁ ws rs : List Value}
    (fn : ρ.findVal? "n" = some (.num (.natN ws.length)))
    (fc : ρ.findVal? "instr'*" = some (.list cs)) (fv₁ : ρ.findVal? "val'*" = some (.list ws₁))
    (fv : ρ.findVal? "val*" = some (.list ws)) (fi : ρ.findVal? "instr*" = some (.list rs)) :
    EvalExp env ρ (ruleConcl brZeroRule)
      (.tuple [.list [.case "LABEL_%{%}%" (.tuple [.num (.natN ws.length), .list cs,
        .list (ws₁ ++ ws ++ [.case "BR" (pctV 0)] ++ rs)])], .list (ws ++ cs)]) :=
  evalExp_tup2 (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
    (evalExp_iter (by decide) fc) (evalExp_cat (evalExp_cat (evalExp_cat
      (evalExp_subIter (by decide) fv₁) (evalExp_valsN (by decide) fn fv))
      (evalExp_list1 (evalExp_case (evalExp_pct 0)))) (evalExp_subIter (by decide) fi)))))
    (evalExp_cat (evalExp_valsN (by decide) fn fv) (evalExp_subIter (by decide) fc))

/-- `br-zero`, read back. -/
theorem brZero_inv {n : Nat} {cont : List V2.Instr} {us : List Val} {l : LabelIdx}
    {rest : List Admin} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 8
      (.tuple [.list (adminsToV [.label n cont (vals us ++ [.plain (.br l)] ++ rest)]), w])) :
    l.toNat = 0 ∧ ∃ vs' vs, us = vs' ++ vs ∧ vs.length = n ∧
      w = .list (adminsToV (vals vs ++ expression cont)) := by
  obtain ⟨σ, hq, he, -⟩ := firesB20_inv (hasRuleAt_brZero B) hf
  obtain ⟨cs, fc⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws₁, fv₁, ht₁⟩ := quant_listT (x := "val'*") (t := .varT "val" []) hq (by simp)
  obtain ⟨ws', fv', ht⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨rs, fi⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨v₁, v₂, h₁, -, -⟩ := evalExp_catE_iff.1 (evalExp_tup2_inv he).2
  obtain ⟨ws, fv, fn, -⟩ := evalExp_valsN_inv (by decide) h₁
  have ew : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  have hu : .num (.natN n) = Value.num (.natN ws.length) ∧ instrsToV cont = cs ∧
      adminsToV (vals us ++ [.plain (.br l)] ++ rest) = ws₁ ++ ws ++ [.case "BR" (pctV 0)] ++ rs ∧
      w = .list (ws ++ cs) := label_concl_inj (EvalExp.unique he (eval_brZero fn fc fv₁ fv fi))
  have hs : adminsToV (vals us) = ws₁ ++ ws ∧ adminToV (.plain (.br l)) = .case "BR" (pctV 0) ∧
      adminsToV rest = rs := marked_split (by simpa using hu.2.2.1)
    (valHeads_append B ht₁ (ew ▸ ht)) not_valHead_br not_valHead_br
  have hl : l.toNat = 0 := pctV_inj (Value.case.inj hs.2.1).2
  obtain ⟨vs', vs, hus, -, hvs⟩ : ∃ vs' vs, us = vs' ++ vs ∧ vs'.map valV = ws₁ ∧
      vs.map valV = ws := map_valV_eq_append (adminsToV_vals us ▸ hs.1)
  have hlen : vs.length = n := by rw [Silmaril.Wasm.SpecTec.Sim.Bwd.natN_inj hu.1, ← hvs, List.length_map]
  have hw : w = .list (adminsToV (vals vs ++ expression cont)) := by
    rw [hu.2.2.2, adminsToV_append, adminsToV_vals, adminsToV_expression, hvs, hu.2.1]
  exact ⟨hl, vs', vs, hus, hlen, hw⟩

/-- `br-zero`, fired. -/
theorem brZero_fires {cont : List V2.Instr} {vs' vs : List Val} {l : LabelIdx}
    {rest : List Admin} (hl : l.toNat = 0)
    (hn : TypedV (simEnv20 B) nT (.num (.natN vs.length)))
    (hc : TypedV (simEnv20 B) instrsT (.list (instrsToV cont)))
    (hv' : TypedV (simEnv20 B) valsT (.list (adminsToV (vals vs'))))
    (hv : TypedV (simEnv20 B) valsT (.list (adminsToV (vals vs))))
    (hr : TypedV (simEnv20 B) instrsT (.list (adminsToV rest))) :
    FiresB (simEnv20 B) "Step_pure" 8
      (.tuple [.list (adminsToV [.label vs.length cont (vals (vs' ++ vs) ++ [.plain (.br l)] ++ rest)]),
        .list (adminsToV (vals vs ++ expression cont))]) := by
  let σ : List (IL.Id × Value) := [("n", .num (.natN vs.length)),
    ("instr'*", .list (instrsToV cont)), ("val'*", .list (adminsToV (vals vs'))),
    ("val*", .list (adminsToV (vals vs))), ("instr*", .list (adminsToV rest))]
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" =
      some (.num (.natN (adminsToV (vals vs)).length)) := by
    rw [adminsToV_vals_length]; rfl
  have he := eval_brZero (env := simEnv20 B) fn rfl rfl rfl rfl
  rw [adminsToV_vals_length] at he
  have eb : adminsToV (vals (vs' ++ vs) ++ [.plain (.br l)] ++ rest) =
      adminsToV (vals vs') ++ adminsToV (vals vs) ++ [.case "BR" (pctV 0)] ++ adminsToV rest := by
    rw [vals_append, adminsToV_append, adminsToV_append, adminsToV_append, ← hl]
    rfl
  rw [adminsToV_label, eb, adminsToV_append, adminsToV_expression]
  exact firesB20_of (hasRuleAt_brZero B) σ (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons rfl (hc _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hv' _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (hv _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hr _ ⟨rfl, rfl, rfl⟩)
        QuantsOk.nil))))) he prems_nil

/-- **`Step_pure/br-zero` is `PureStep.brZero`**, at a value prefix `us` that the rule splits
as `val'* val^n`. -/
theorem brZero_iff {n : Nat} {cont : List V2.Instr} {us : List Val} {l : LabelIdx}
    {rest : List Admin} (hn : TypedV (simEnv20 B) nT (.num (.natN n)))
    (hc : TypedV (simEnv20 B) instrsT (.list (instrsToV cont)))
    (hus : ∀ v ∈ us, TypedV (simEnv20 B) valT (valV v))
    (hr : TypedV (simEnv20 B) instrsT (.list (adminsToV rest))) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 8
        (.tuple [.list (adminsToV [.label n cont (vals us ++ [.plain (.br l)] ++ rest)]), w]) ↔
      l.toNat = 0 ∧ ∃ vs' vs, us = vs' ++ vs ∧ vs.length = n ∧
        w = .list (adminsToV (vals vs ++ expression cont)) := by
  refine ⟨brZero_inv B, ?_⟩
  rintro ⟨hl, vs', vs, rfl, rfl, rfl⟩
  obtain ⟨hv', hv⟩ := typedV_vals_split hus
  exact brZero_fires B hl hn hc hv' hv hr

/-- The V2 step of `br-zero`, from the right-hand side of `brZero_iff`. -/
theorem brZero_step (P : Silmaril.Wasm.Numerics.Profile) {n : Nat} {cont : List V2.Instr}
    {vs' vs : List Val} {l : LabelIdx} {rest : List Admin} (hl : l.toNat = 0)
    (hn : vs.length = n) :
    PureStep P [.label n cont (vals (vs' ++ vs) ++ [.plain (.br l)] ++ rest)]
      (vals vs ++ expression cont) := by
  rw [vals_append]
  exact .brZero hl hn

/-! ## `br-succ` (9) -/

/-- The conclusion of `br-succ`, evaluated. -/
theorem eval_brSucc {env : Env} {ρ : VarEnv} {nv : Value} {k : Nat} {cs ws rs : List Value}
    (fn : ρ.findVal? "n" = some nv) (fc : ρ.findVal? "instr'*" = some (.list cs))
    (fv : ρ.findVal? "val*" = some (.list ws)) (fl : ρ.findVal? "l" = some (pctV k))
    (fi : ρ.findVal? "instr*" = some (.list rs)) :
    EvalExp env ρ (ruleConcl brSuccRule)
      (.tuple [.list [.case "LABEL_%{%}%" (.tuple [nv, .list cs,
        .list (ws ++ [.case "BR" (pctV (k + 1))] ++ rs)])],
        .list (ws ++ [.case "BR" (pctV k)])]) :=
  evalExp_tup2 (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
    (evalExp_iter (by decide) fc) (evalExp_cat (evalExp_cat (evalExp_subIter (by decide) fv)
      (evalExp_list1 (evalExp_case (evalExp_succIdx fl)))) (evalExp_subIter (by decide) fi)))))
    (evalExp_cat (evalExp_subIter (by decide) fv) (evalExp_list1 (evalExp_case (evalExp_var fl))))

/-- `labelPred` subtracts one. -/
theorem labelPred_toNat (l : LabelIdx) : (labelPred l).toNat = l.toNat - 1 := rfl

/-- `br-succ`, read back. -/
theorem brSucc_inv {n : Nat} {cont : List V2.Instr} {vs : List Val} {l : LabelIdx}
    {rest : List Admin} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 9
      (.tuple [.list (adminsToV [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)]), w])) :
    0 < l.toNat ∧ w = .list (adminsToV (vals vs ++ [.plain (.br (labelPred l))])) := by
  obtain ⟨σ, hq, he, -⟩ := firesB20_inv (hasRuleAt_brSucc B) hf
  obtain ⟨vn, fn⟩ := quant_val (x := "n") (t := nT) hq (by simp)
  obtain ⟨cs, fc⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws, fv, ht⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨lv, fl, hlt⟩ := hq "l" labelidxT (by simp)
  obtain ⟨k, hk⟩ : ∃ k, lv = pctV k := labelidx_inv (valsOnly_bindVals σ) hlt
  obtain ⟨rs, fi⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (by simp)
  have hu : .num (.natN n) = vn ∧ instrsToV cont = cs ∧
      adminsToV (vals vs ++ [.plain (.br l)] ++ rest) = ws ++ [.case "BR" (pctV (k + 1))] ++ rs ∧
      w = .list (ws ++ [.case "BR" (pctV k)]) :=
    label_concl_inj (EvalExp.unique he (eval_brSucc fn fc fv (hk ▸ fl) fi))
  have hs : adminsToV (vals vs) = ws ∧ adminToV (.plain (.br l)) = .case "BR" (pctV (k + 1)) ∧
      adminsToV rest = rs := marked_split (by simpa using hu.2.2.1)
    (valHeads_of_typed (valsOnly_bindVals σ) ht) not_valHead_br not_valHead_br
  have hl : l.toNat = k + 1 := pctV_inj (Value.case.inj hs.2.1).2
  have hw : w = .list (adminsToV (vals vs ++ [.plain (.br (labelPred l))])) := by
    rw [hu.2.2.2, adminsToV_append, hs.1]
    show Value.list (ws ++ [.case "BR" (pctV k)]) = .list (ws ++ [.case "BR" (pctV (l.toNat - 1))])
    rw [hl, Nat.add_sub_cancel]
  exact ⟨by omega, hw⟩

/-- `br-succ`, fired. -/
theorem brSucc_fires {n : Nat} {cont : List V2.Instr} {vs : List Val} {l : LabelIdx}
    {rest : List Admin} (hpos : 0 < l.toNat)
    (hn : TypedV (simEnv20 B) nT (.num (.natN n)))
    (hc : TypedV (simEnv20 B) instrsT (.list (instrsToV cont)))
    (hv : TypedV (simEnv20 B) valsT (.list (adminsToV (vals vs))))
    (hl : TypedV (simEnv20 B) labelidxT (pctV (l.toNat - 1)))
    (hr : TypedV (simEnv20 B) instrsT (.list (adminsToV rest))) :
    FiresB (simEnv20 B) "Step_pure" 9
      (.tuple [.list (adminsToV [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)]),
        .list (adminsToV (vals vs ++ [.plain (.br (labelPred l))]))]) := by
  let σ : List (IL.Id × Value) := [("n", .num (.natN n)), ("instr'*", .list (instrsToV cont)),
    ("val*", .list (adminsToV (vals vs))), ("l", pctV (l.toNat - 1)),
    ("instr*", .list (adminsToV rest))]
  have he := eval_brSucc (env := simEnv20 B) (ρ := VarEnv.empty.bindVals σ) rfl rfl rfl rfl rfl
  rw [Nat.sub_add_cancel hpos] at he
  have eb : adminsToV (vals vs ++ [.plain (.br l)] ++ rest) =
      adminsToV (vals vs) ++ [.case "BR" (pctV l.toNat)] ++ adminsToV rest := by
    rw [adminsToV_append, adminsToV_append]; rfl
  have er : adminsToV (vals vs ++ [.plain (.br (labelPred l))]) =
      adminsToV (vals vs) ++ [.case "BR" (pctV (l.toNat - 1))] := by
    rw [adminsToV_append]; rfl
  rw [adminsToV_label, eb, er]
  exact firesB20_of (hasRuleAt_brSucc B) σ (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons rfl (hc _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hv _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (hl _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hr _ ⟨rfl, rfl, rfl⟩)
        QuantsOk.nil))))) he prems_nil

/-- **`Step_pure/br-succ` is `PureStep.brSucc`.** -/
theorem brSucc_iff {n : Nat} {cont : List V2.Instr} {vs : List Val} {l : LabelIdx}
    {rest : List Admin} (hn : TypedV (simEnv20 B) nT (.num (.natN n)))
    (hc : TypedV (simEnv20 B) instrsT (.list (instrsToV cont)))
    (hv : TypedV (simEnv20 B) valsT (.list (adminsToV (vals vs))))
    (hl : TypedV (simEnv20 B) labelidxT (pctV (l.toNat - 1)))
    (hr : TypedV (simEnv20 B) instrsT (.list (adminsToV rest))) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 9
        (.tuple [.list (adminsToV [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)]), w]) ↔
      0 < l.toNat ∧ w = .list (adminsToV (vals vs ++ [.plain (.br (labelPred l))])) :=
  ⟨brSucc_inv B, fun ⟨hpos, hw⟩ => hw ▸ brSucc_fires B hpos hn hc hv hl hr⟩

/-! ## `return-frame` (15) -/

/-- The conclusion of `return-frame`, evaluated. -/
theorem eval_returnFrame {env : Env} {ρ : VarEnv} {fv' : Value} {ws₁ ws rs : List Value}
    (fn : ρ.findVal? "n" = some (.num (.natN ws.length))) (ff : ρ.findVal? "f" = some fv')
    (fv₁ : ρ.findVal? "val'*" = some (.list ws₁)) (fv : ρ.findVal? "val*" = some (.list ws))
    (fi : ρ.findVal? "instr*" = some (.list rs)) :
    EvalExp env ρ (ruleConcl returnFrameRule)
      (.tuple [.list [.case "FRAME_%{%}%" (.tuple [.num (.natN ws.length), fv',
        .list (ws₁ ++ ws ++ [caseNilV "RETURN"] ++ rs)])], .list ws]) :=
  evalExp_tup2 (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
    (evalExp_var ff) (evalExp_cat (evalExp_cat (evalExp_cat
      (evalExp_subIter (by decide) fv₁) (evalExp_valsN (by decide) fn fv))
      (evalExp_list1 evalExp_caseNil)) (evalExp_subIter (by decide) fi)))))
    (evalExp_valsN (by decide) fn fv)

/-- `return-frame`, read back. -/
theorem returnFrame_inv {n : Nat} {fr : Frame} {us : List Val} {rest : List Admin} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 15
      (.tuple [.list (adminsToV [.frame n fr (vals us ++ [.plain .return_] ++ rest)]), w])) :
    ∃ vs' vs, us = vs' ++ vs ∧ vs.length = n ∧ w = .list (adminsToV (vals vs)) := by
  obtain ⟨σ, hq, he, -⟩ := firesB20_inv (hasRuleAt_returnFrame B) hf
  obtain ⟨vf, ff⟩ := quant_val (x := "f") (t := frameT) hq (by simp)
  obtain ⟨ws₁, fv₁, ht₁⟩ := quant_listT (x := "val'*") (t := .varT "val" []) hq (by simp)
  obtain ⟨ws', fv', ht⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨rs, fi⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws, fv, fn, -⟩ := evalExp_valsN_inv (by decide) (evalExp_tup2_inv he).2
  obtain rfl : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  have hu := EvalExp.unique he (eval_returnFrame fn ff fv₁ fv fi)
  rw [adminsToV_frame] at hu
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq,
    Value.num.injEq, Num.natN.injEq, true_and, and_true] at hu
  obtain ⟨⟨hn, -, hb⟩, rfl⟩ := hu
  obtain ⟨h₁, -, -⟩ := marked_split (m := .plain .return_) (x := caseNilV "RETURN")
    (by simpa using hb) (valHeads_append B ht₁ ht) not_valHead_return not_valHead_return
  rw [adminsToV_vals] at h₁
  obtain ⟨vs', vs, rfl, -, hvs⟩ := map_valV_eq_append h₁
  exact ⟨vs', vs, rfl, by rw [hn, ← hvs, List.length_map], by rw [adminsToV_vals, hvs]⟩

/-- `return-frame`, fired. -/
theorem returnFrame_fires {fr : Frame} {vs' vs : List Val} {rest : List Admin}
    (hn : TypedV (simEnv20 B) nT (.num (.natN vs.length)))
    (hfr : TypedV (simEnv20 B) frameT (frameV fr))
    (hv' : TypedV (simEnv20 B) valsT (.list (adminsToV (vals vs'))))
    (hv : TypedV (simEnv20 B) valsT (.list (adminsToV (vals vs))))
    (hr : TypedV (simEnv20 B) instrsT (.list (adminsToV rest))) :
    FiresB (simEnv20 B) "Step_pure" 15
      (.tuple [.list (adminsToV [.frame vs.length fr (vals (vs' ++ vs) ++ [.plain .return_] ++ rest)]),
        .list (adminsToV (vals vs))]) := by
  let σ : List (IL.Id × Value) := [("n", .num (.natN vs.length)), ("f", frameV fr),
    ("val'*", .list (adminsToV (vals vs'))), ("val*", .list (adminsToV (vals vs))),
    ("instr*", .list (adminsToV rest))]
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" =
      some (.num (.natN (adminsToV (vals vs)).length)) := by
    rw [adminsToV_vals_length]; rfl
  have he := eval_returnFrame (env := simEnv20 B) fn rfl rfl rfl rfl
  rw [adminsToV_vals_length] at he
  have eb : adminsToV (vals (vs' ++ vs) ++ [.plain .return_] ++ rest) =
      adminsToV (vals vs') ++ adminsToV (vals vs) ++ [caseNilV "RETURN"] ++ adminsToV rest := by
    rw [vals_append, adminsToV_append, adminsToV_append, adminsToV_append]
    rfl
  rw [adminsToV_frame, eb]
  exact firesB20_of (hasRuleAt_returnFrame B) σ (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons rfl (hfr _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hv' _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (hv _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hr _ ⟨rfl, rfl, rfl⟩)
        QuantsOk.nil))))) he prems_nil

/-- **`Step_pure/return-frame` is `PureStep.returnFrame`**, at a value prefix `us` that the rule
splits as `val'* val^n`. -/
theorem returnFrame_iff {n : Nat} {fr : Frame} {us : List Val} {rest : List Admin}
    (hn : TypedV (simEnv20 B) nT (.num (.natN n))) (hfr : TypedV (simEnv20 B) frameT (frameV fr))
    (hus : ∀ v ∈ us, TypedV (simEnv20 B) valT (valV v))
    (hr : TypedV (simEnv20 B) instrsT (.list (adminsToV rest))) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 15
        (.tuple [.list (adminsToV [.frame n fr (vals us ++ [.plain .return_] ++ rest)]), w]) ↔
      ∃ vs' vs, us = vs' ++ vs ∧ vs.length = n ∧ w = .list (adminsToV (vals vs)) := by
  refine ⟨returnFrame_inv B, ?_⟩
  rintro ⟨vs', vs, rfl, rfl, rfl⟩
  obtain ⟨hv', hv⟩ := typedV_vals_split hus
  exact returnFrame_fires B hn hfr hv' hv hr

/-- The V2 step of `return-frame`, from the right-hand side of `returnFrame_iff`. -/
theorem returnFrame_step (P : Silmaril.Wasm.Numerics.Profile) {n : Nat} {fr : Frame}
    {vs' vs : List Val} {rest : List Admin} (hn : vs.length = n) :
    PureStep P [.frame n fr (vals (vs' ++ vs) ++ [.plain .return_] ++ rest)] (vals vs) := by
  rw [vals_append]
  exact .returnFrame hn

/-! ## Backward simulation, per rule

Whenever one of the five rules fires at the image of a V2 code sequence of its shape, the V2
machine takes the transcribed step to a code sequence whose image is the rule's right-hand side.
No typing hypothesis is needed in this direction. -/

/-- `br-zero` (8), backward. -/
theorem brZero_bwd (P : Silmaril.Wasm.Numerics.Profile) {n : Nat} {cont : List V2.Instr}
    {us : List Val} {l : LabelIdx} {rest : List Admin} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 8
      (.tuple [.list (adminsToV [.label n cont (vals us ++ [.plain (.br l)] ++ rest)]), w])) :
    ∃ is', w = .list (adminsToV is') ∧
      PureStep P [.label n cont (vals us ++ [.plain (.br l)] ++ rest)] is' := by
  obtain ⟨hl, vs', vs, rfl, hn, hw⟩ := brZero_inv B hf
  exact ⟨_, hw, brZero_step P hl hn⟩

/-- `br-succ` (9), backward. -/
theorem brSucc_bwd (P : Silmaril.Wasm.Numerics.Profile) {n : Nat} {cont : List V2.Instr}
    {vs : List Val} {l : LabelIdx} {rest : List Admin} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 9
      (.tuple [.list (adminsToV [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)]), w])) :
    ∃ is', w = .list (adminsToV is') ∧
      PureStep P [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)] is' := by
  obtain ⟨hpos, hw⟩ := brSucc_inv B hf
  exact ⟨_, hw, .brSucc hpos⟩

/-- `return-frame` (15), backward. -/
theorem returnFrame_bwd (P : Silmaril.Wasm.Numerics.Profile) {n : Nat} {fr : Frame}
    {us : List Val} {rest : List Admin} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 15
      (.tuple [.list (adminsToV [.frame n fr (vals us ++ [.plain .return_] ++ rest)]), w])) :
    ∃ is', w = .list (adminsToV is') ∧
      PureStep P [.frame n fr (vals us ++ [.plain .return_] ++ rest)] is' := by
  obtain ⟨vs', vs, rfl, hn, hw⟩ := returnFrame_inv B hf
  exact ⟨_, hw, returnFrame_step P hn⟩

/-- `return-label` (16), backward. -/
theorem returnLabel_bwd (P : Silmaril.Wasm.Numerics.Profile) {n : Nat} {cont : List V2.Instr}
    {vs : List Val} {rest : List Admin} {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 16
      (.tuple [.list (adminsToV [.label n cont (vals vs ++ [.plain .return_] ++ rest)]), w])) :
    ∃ is', w = .list (adminsToV is') ∧
      PureStep P [.label n cont (vals vs ++ [.plain .return_] ++ rest)] is' :=
  ⟨_, returnLabel_inv B hf, .returnLabel⟩

/-- `trap-vals` (17), backward. -/
theorem trapVals_bwd (P : Silmaril.Wasm.Numerics.Profile) {vs : List Val} {rest : List Admin}
    {w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 17
      (.tuple [.list (adminsToV (vals vs ++ [.trap] ++ rest)), w])) :
    ∃ is', w = .list (adminsToV is') ∧ PureStep P (vals vs ++ [.trap] ++ rest) is' := by
  obtain ⟨hne, hw⟩ := trapVals_inv B hf
  exact ⟨_, hw, .trapVals hne⟩

end Silmaril.Wasm.SpecTec.Sim20.Pure
