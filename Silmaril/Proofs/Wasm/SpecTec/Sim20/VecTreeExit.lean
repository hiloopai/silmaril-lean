module

public import Silmaril.Wasm.SpecTec.Sim20.VecWhole.Thms

/-!
# Label and frame exits, branches, returns and traps in the corrected vector script

Round 8's `VecWhole.wholeStepVec` covers straight-line vector code only: no rule that leaves a
label or a frame, and no trap. This module fires those rules of `Step_pure` in `simEnv20V B`,
with every quantifier typed there. The vector errata change only type definitions, so the nine
rules sit at the indices they have in the 2.0 script (`hasRuleAt_*V`, kernel `rfl`), and their
conclusions are evaluated 's environment-generic lemmas (`Pure.eval_labelVals`, …), as
in `simEnv20T` (`StoreGood.spureT_brZero`, …, `StoreDeep.spureT_labelVals`):

* exits: **`spureV_labelVals`** (7), **`spureV_frameVals`** (14);
* branches and returns: `spureV_brZero` (8), `spureV_brSucc` (9), `spureV_returnFrame` (15),
  `spureV_returnLabel` (16);
* traps: **`spureV_trapVals`** (17), **`spureV_trapLabel`** (18), **`spureV_trapFrame`** (19).

The quantifier types are `n`, `frame`, `labelidx`, `val*` and `instr*`. The value prefixes are
typed by `VecWhole.typedV_valsV`, the label index by moving round 3's typing across both errata
(`typedV_labelidxV`). The others are hypotheses, in `simEnv20V B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecTree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim (TypedV SPure QuantsOk dderives_of_ruleAt evalExp_or evalExp_ne_nil
  evalExp_tup2 evalExp_case evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)

set_option maxRecDepth 100000

variable (B : Builtins)

/-! ## The rules, at their 2.0 indices -/

theorem hasRuleAt_labelValsV : HasRuleAt (simEnv20V B) "Step_pure" "%~>%" 7 Pure.labelValsRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_brZeroV : HasRuleAt (simEnv20V B) "Step_pure" "%~>%" 8 Pure.brZeroRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_brSuccV : HasRuleAt (simEnv20V B) "Step_pure" "%~>%" 9 Pure.brSuccRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_frameValsV : HasRuleAt (simEnv20V B) "Step_pure" "%~>%" 14 Pure.frameValsRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_returnFrameV :
    HasRuleAt (simEnv20V B) "Step_pure" "%~>%" 15 Pure.returnFrameRule := ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_returnLabelV :
    HasRuleAt (simEnv20V B) "Step_pure" "%~>%" 16 Pure.returnLabelRule := ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_trapValsV : HasRuleAt (simEnv20V B) "Step_pure" "%~>%" 17 Pure.trapValsRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_trapLabelV : HasRuleAt (simEnv20V B) "Step_pure" "%~>%" 18 Pure.trapLabelRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_trapFrameV : HasRuleAt (simEnv20V B) "Step_pure" "%~>%" 19 Pure.trapFrameRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

variable {B}

/-- A value prefix, typed in `simEnv20V B`. -/
theorem typedV_valsTV (vs : List Val) :
    TypedV (simEnv20V B) Pure.valsT (.list (adminsToV (vals vs))) :=
  VecWhole.typedV_valsV vs

theorem ffT_labelidx : VecAgree.ffT Pure.labelidxT := by
  simp [VecAgree.ffT, Sim.Round7.Script.evTyp, Sim.Round7.Script.evArgs,
    ElseAgree.GoodT, ElseAgree.tyEvB, VecAgree.fams]

/-- A label index, typed in `simEnv20V B`. -/
theorem typedV_labelidxV (l : LabelIdx) : TypedV (simEnv20V B) Pure.labelidxT (pctV l.toNat) :=
  VecAgree.typedV_TtoV ffT_labelidx (VecAgree.vOk_of_vokB _ rfl)
    (StoreAgree.typedV_to20T (by decide) (Whole.typedV_labelidx20 l))

/-! ## Exits -/

/-- **`label-vals` in `simEnv20V`.** -/
theorem spureV_labelVals {n : Nat} {cont : List V2.Instr} {vs : List Val}
    (hn : TypedV (simEnv20V B) Pure.nT (.num (.natN n)))
    (hc : TypedV (simEnv20V B) Pure.instrsT (.list (instrsToV cont))) :
    SPure (simEnv20V B) (adminsToV [.label n cont (vals vs)]) (adminsToV (vals vs)) :=
  dderives_of_ruleAt (hasRuleAt_labelValsV B)
    [("n", .num (.natN n)), ("instr*", .list (instrsToV cont)), ("val*", .list (adminsToV (vals vs)))]
    (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hc _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (typedV_valsTV vs _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))
    (Pure.eval_labelVals rfl rfl rfl) Sim.Exn.prems_nil

/-- **`frame-vals` in `simEnv20V`.** -/
theorem spureV_frameVals {fr : Frame} {vs : List Val}
    (hn : TypedV (simEnv20V B) Pure.nT (.num (.natN vs.length)))
    (hfr : TypedV (simEnv20V B) Pure.frameT (frameV fr)) :
    SPure (simEnv20V B) (adminsToV [.frame vs.length fr (vals vs)]) (adminsToV (vals vs)) := by
  have hl : (adminsToV (vals vs)).length = vs.length := Pure.adminsToV_vals_length vs
  have fn : (VarEnv.empty.bindVals [("n", .num (.natN vs.length)), ("f", frameV fr),
      ("val*", .list (adminsToV (vals vs)))]).findVal? "n" =
      some (.num (.natN (adminsToV (vals vs)).length)) := by
    rw [hl]; rfl
  have he := Pure.eval_frameVals (env := simEnv20V B) fn rfl rfl
  rw [hl] at he
  exact dderives_of_ruleAt (hasRuleAt_frameValsV B) _ (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons rfl (hfr _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (typedV_valsTV vs _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))) he Sim.Exn.prems_nil

/-! ## Branches and returns -/

/-- **`br-zero` in `simEnv20V`.** -/
theorem spureV_brZero {cont : List V2.Instr} {vs' vs : List Val} {l : LabelIdx}
    {rest : List Admin} (hl : l.toNat = 0)
    (hn : TypedV (simEnv20V B) Pure.nT (.num (.natN vs.length)))
    (hc : TypedV (simEnv20V B) Pure.instrsT (.list (instrsToV cont)))
    (hr : TypedV (simEnv20V B) Pure.instrsT (.list (adminsToV rest))) :
    SPure (simEnv20V B)
      (adminsToV [.label vs.length cont (vals (vs' ++ vs) ++ [.plain (.br l)] ++ rest)])
      (adminsToV (vals vs ++ expression cont)) := by
  let σ : List (IL.Id × Value) := [("n", .num (.natN vs.length)),
    ("instr'*", .list (instrsToV cont)), ("val'*", .list (adminsToV (vals vs'))),
    ("val*", .list (adminsToV (vals vs))), ("instr*", .list (adminsToV rest))]
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" =
      some (.num (.natN (adminsToV (vals vs)).length)) := by
    rw [Pure.adminsToV_vals_length]; rfl
  have he := Pure.eval_brZero (env := simEnv20V B) fn rfl rfl rfl rfl
  rw [Pure.adminsToV_vals_length] at he
  have eb : adminsToV (vals (vs' ++ vs) ++ [.plain (.br l)] ++ rest) =
      adminsToV (vals vs') ++ adminsToV (vals vs) ++ [.case "BR" (pctV 0)] ++ adminsToV rest := by
    rw [Pure.vals_append, Pure.adminsToV_append, Pure.adminsToV_append, Pure.adminsToV_append, ← hl]
    rfl
  rw [Pure.adminsToV_label, eb, Pure.adminsToV_append, Pure.adminsToV_expression]
  exact dderives_of_ruleAt (hasRuleAt_brZeroV B) σ (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons rfl (hc _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (typedV_valsTV vs' _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (typedV_valsTV vs _ ⟨rfl, rfl, rfl⟩)
        (QuantsOk.cons rfl (hr _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))))) he Sim.Exn.prems_nil

/-- **`br-succ` in `simEnv20V`.** -/
theorem spureV_brSucc {n : Nat} {cont : List V2.Instr} {vs : List Val} {l : LabelIdx}
    {rest : List Admin} (hpos : 0 < l.toNat)
    (hn : TypedV (simEnv20V B) Pure.nT (.num (.natN n)))
    (hc : TypedV (simEnv20V B) Pure.instrsT (.list (instrsToV cont)))
    (hr : TypedV (simEnv20V B) Pure.instrsT (.list (adminsToV rest))) :
    SPure (simEnv20V B) (adminsToV [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)])
      (adminsToV (vals vs ++ [.plain (.br (labelPred l))])) := by
  have hl : TypedV (simEnv20V B) Pure.labelidxT (pctV (l.toNat - 1)) :=
    typedV_labelidxV (labelPred l)
  let σ : List (IL.Id × Value) := [("n", .num (.natN n)), ("instr'*", .list (instrsToV cont)),
    ("val*", .list (adminsToV (vals vs))), ("l", pctV (l.toNat - 1)),
    ("instr*", .list (adminsToV rest))]
  have he := Pure.eval_brSucc (env := simEnv20V B) (ρ := VarEnv.empty.bindVals σ) rfl rfl rfl rfl rfl
  rw [Nat.sub_add_cancel hpos] at he
  have eb : adminsToV (vals vs ++ [.plain (.br l)] ++ rest) =
      adminsToV (vals vs) ++ [.case "BR" (pctV l.toNat)] ++ adminsToV rest := by
    rw [Pure.adminsToV_append, Pure.adminsToV_append]; rfl
  have er : adminsToV (vals vs ++ [.plain (.br (labelPred l))]) =
      adminsToV (vals vs) ++ [.case "BR" (pctV (l.toNat - 1))] := by
    rw [Pure.adminsToV_append]; rfl
  rw [Pure.adminsToV_label, eb, er]
  exact dderives_of_ruleAt (hasRuleAt_brSuccV B) σ (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons rfl (hc _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (typedV_valsTV vs _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (hl _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hr _ ⟨rfl, rfl, rfl⟩)
        QuantsOk.nil))))) he Sim.Exn.prems_nil

/-- **`return-frame` in `simEnv20V`.** -/
theorem spureV_returnFrame {fr : Frame} {vs' vs : List Val} {rest : List Admin}
    (hn : TypedV (simEnv20V B) Pure.nT (.num (.natN vs.length)))
    (hfr : TypedV (simEnv20V B) Pure.frameT (frameV fr))
    (hr : TypedV (simEnv20V B) Pure.instrsT (.list (adminsToV rest))) :
    SPure (simEnv20V B)
      (adminsToV [.frame vs.length fr (vals (vs' ++ vs) ++ [.plain .return_] ++ rest)])
      (adminsToV (vals vs)) := by
  let σ : List (IL.Id × Value) := [("n", .num (.natN vs.length)), ("f", frameV fr),
    ("val'*", .list (adminsToV (vals vs'))), ("val*", .list (adminsToV (vals vs))),
    ("instr*", .list (adminsToV rest))]
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" =
      some (.num (.natN (adminsToV (vals vs)).length)) := by
    rw [Pure.adminsToV_vals_length]; rfl
  have he := Pure.eval_returnFrame (env := simEnv20V B) fn rfl rfl rfl rfl
  rw [Pure.adminsToV_vals_length] at he
  have eb : adminsToV (vals (vs' ++ vs) ++ [.plain .return_] ++ rest) =
      adminsToV (vals vs') ++ adminsToV (vals vs) ++ [caseNilV "RETURN"] ++ adminsToV rest := by
    rw [Pure.vals_append, Pure.adminsToV_append, Pure.adminsToV_append, Pure.adminsToV_append]
    rfl
  rw [Pure.adminsToV_frame, eb]
  exact dderives_of_ruleAt (hasRuleAt_returnFrameV B) σ (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons rfl (hfr _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (typedV_valsTV vs' _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (typedV_valsTV vs _ ⟨rfl, rfl, rfl⟩)
        (QuantsOk.cons rfl (hr _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))))) he Sim.Exn.prems_nil

/-- **`return-label` in `simEnv20V`.** -/
theorem spureV_returnLabel {n : Nat} {cont : List V2.Instr} {vs : List Val} {rest : List Admin}
    (hn : TypedV (simEnv20V B) Pure.nT (.num (.natN n)))
    (hc : TypedV (simEnv20V B) Pure.instrsT (.list (instrsToV cont)))
    (hr : TypedV (simEnv20V B) Pure.instrsT (.list (adminsToV rest))) :
    SPure (simEnv20V B) (adminsToV [.label n cont (vals vs ++ [.plain .return_] ++ rest)])
      (adminsToV (vals vs ++ [.plain .return_])) := by
  let σ : List (IL.Id × Value) := [("n", .num (.natN n)), ("instr'*", .list (instrsToV cont)),
    ("val*", .list (adminsToV (vals vs))), ("instr*", .list (adminsToV rest))]
  have he := Pure.eval_returnLabel (env := simEnv20V B) (ρ := VarEnv.empty.bindVals σ)
    rfl rfl rfl rfl
  have e₁ : adminsToV (vals vs ++ [.plain .return_] ++ rest) =
      adminsToV (vals vs) ++ [caseNilV "RETURN"] ++ adminsToV rest := by
    rw [Pure.adminsToV_append, Pure.adminsToV_append]; rfl
  have e₂ : adminsToV (vals vs ++ [.plain .return_]) =
      adminsToV (vals vs) ++ [caseNilV "RETURN"] := by
    rw [Pure.adminsToV_append]; rfl
  rw [Pure.adminsToV_label, e₁, e₂]
  exact dderives_of_ruleAt (hasRuleAt_returnLabelV B) σ (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons rfl (hc _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (typedV_valsTV vs _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (hr _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))) he Sim.Exn.prems_nil

/-! ## Traps -/

/-- **`trap-vals` in `simEnv20V`.** -/
theorem spureV_trapVals {vs : List Val} {rest : List Admin} (hne : vs ≠ [] ∨ rest ≠ [])
    (hr : TypedV (simEnv20V B) Pure.instrsT (.list (adminsToV rest))) :
    SPure (simEnv20V B) (adminsToV (vals vs ++ [.trap] ++ rest)) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) :=
    [("val*", .list (adminsToV (vals vs))), ("instr*", .list (adminsToV rest))]
  have fv : (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list (adminsToV (vals vs))) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "instr*" = some (.list (adminsToV rest)) := rfl
  have he := Pure.eval_trapVals (env := simEnv20V B) fv fi
  rw [Pure.adminsToV_marked]
  have hne' : decide (adminsToV (vals vs) ≠ [] ∨ adminsToV rest ≠ []) = true := by
    rw [Pure.adminsToV_vals, Pure.adminsToV_eq_map rest]
    simpa [List.map_eq_nil_iff] using hne
  have hpr : EvalExp (simEnv20V B) (VarEnv.empty.bindVals σ) (.binE .orOp .boolT
      (.cmpE .neOp .boolT (Equiv.Execution.iterPat "val" "val*") (.listE []))
      (.cmpE .neOp .boolT (Equiv.Execution.iterPat "instr" "instr*") (.listE []))) (.bool true) :=
    hne' ▸ evalExp_or (evalExp_ne_nil (Equiv.Execution.evalExp_iterPat (by decide) fv))
      (evalExp_ne_nil (Equiv.Execution.evalExp_iterPat (by decide) fi))
  exact dderives_of_ruleAt (hasRuleAt_trapValsV B) σ
    (QuantsOk.cons fv (typedV_valsTV vs _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons fi (hr _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)) he
    (Sim.prems_one (.ifPr hpr))

/-- **`trap-label` in `simEnv20V`.** -/
theorem spureV_trapLabel {n : Nat} {cont : List V2.Instr}
    (hn : TypedV (simEnv20V B) Pure.nT (.num (.natN n)))
    (hc : TypedV (simEnv20V B) Pure.instrsT (.list (instrsToV cont))) :
    SPure (simEnv20V B) (adminsToV [.label n cont [.trap]]) (adminsToV [.trap]) :=
  dderives_of_ruleAt (hasRuleAt_trapLabelV B)
    [("n", .num (.natN n)), ("instr'*", .list (instrsToV cont))]
    (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hc _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_list1 (evalExp_case (Sim.evalExp_tup3 (evalExp_var rfl)
      (Pure.evalExp_iter (by decide) rfl) (evalExp_list1 Pure.evalExp_caseNil))))
      (evalExp_list1 Pure.evalExp_caseNil)) Sim.Exn.prems_nil

/-- **`trap-frame` in `simEnv20V`.** -/
theorem spureV_trapFrame {n : Nat} {fr : Frame}
    (hn : TypedV (simEnv20V B) Pure.nT (.num (.natN n)))
    (hfr : TypedV (simEnv20V B) Pure.frameT (frameV fr)) :
    SPure (simEnv20V B) (adminsToV [.frame n fr [.trap]]) (adminsToV [.trap]) :=
  dderives_of_ruleAt (hasRuleAt_trapFrameV B) [("n", .num (.natN n)), ("f", frameV fr)]
    (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hfr _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_list1 (evalExp_case (Sim.evalExp_tup3 (evalExp_var rfl)
      (evalExp_var rfl) (evalExp_list1 Pure.evalExp_caseNil))))
      (evalExp_list1 Pure.evalExp_caseNil)) Sim.Exn.prems_nil

end Silmaril.Wasm.SpecTec.Sim20.VecTree
