module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreGoodTyp

/-!
# The five concatenation rules of `Step_pure` in `simEnv20T`, with stores in the tail

`br-zero` (8), `br-succ` (9), `return-frame` (15), `return-label` (16) and `trap-vals` (17)
quantify the code after their redex as `instr*`. Once administrative stores are admitted, that
tail may hold a scalar store, which is an `instr` of `simEnv20T` only. Round 3's firings
(`Pure.brZero_fires`, …) are stated in `simEnv20`, so they are restated here in `simEnv20T`:
the same assignment, the conclusion evaluated by the same environment-generic lemmas
(`Pure.eval_brZero`, …), every quantifier typed in `simEnv20T`, and the rule found in
`simEnv20T` by `rfl` (`hasRuleAt_*T`; the `STORE` errata leave `Step_pure` unchanged).

Each result is a `Step_pure` derivation of `simEnv20T` (`spureT_brZero`, …), so with
`StoreRun.sstepT_pure` it is a step of the corrected script.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreGood

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim (TypedV SPure QuantsOk dderives_of_ruleAt evalExp_or evalExp_ne_nil)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)

set_option maxRecDepth 100000

variable (B : Builtins)

/-! ## Provenance in `simEnv20T` -/

theorem hasRuleAt_brZeroT : HasRuleAt (simEnv20T B) "Step_pure" "%~>%" 8 Pure.brZeroRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_brSuccT : HasRuleAt (simEnv20T B) "Step_pure" "%~>%" 9 Pure.brSuccRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_returnFrameT :
    HasRuleAt (simEnv20T B) "Step_pure" "%~>%" 15 Pure.returnFrameRule := ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_returnLabelT :
    HasRuleAt (simEnv20T B) "Step_pure" "%~>%" 16 Pure.returnLabelRule := ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt_trapValsT : HasRuleAt (simEnv20T B) "Step_pure" "%~>%" 17 Pure.trapValsRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

variable {B}

/-! ## Quantifier typing moved to `simEnv20T` -/

theorem typedV_valsT20T (vs : List Val) :
    TypedV (simEnv20T B) Pure.valsT (.list (adminsToV (vals vs))) :=
  StoreAgree.typedV_list_to20T (by decide) (Whole.typedV_valsT_vals20 vs)

theorem typedV_nT20T {n : Nat} (h : TypedV (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) Pure.nT (.num (.natN n))) :
    TypedV (simEnv20T B) Pure.nT (.num (.natN n)) :=
  StoreAgree.typedV_to20T (by decide) h

theorem typedV_instrsT20T {cont : List V2.Instr}
    (h : TypedV (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) Pure.instrsT (.list (instrsToV cont))) :
    TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV cont)) :=
  StoreAgree.typedV_list_to20T (by decide) h

/-! ## The five rules -/

/-- **`br-zero` in `simEnv20T`.** -/
theorem spureT_brZero {cont : List V2.Instr} {vs' vs : List Val} {l : LabelIdx}
    {rest : List Admin} (hl : l.toNat = 0)
    (hn : TypedV (simEnv20T B) Pure.nT (.num (.natN vs.length)))
    (hc : TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV cont)))
    (hr : TypedV (simEnv20T B) Pure.instrsT (.list (adminsToV rest))) :
    SPure (simEnv20T B)
      (adminsToV [.label vs.length cont (vals (vs' ++ vs) ++ [.plain (.br l)] ++ rest)])
      (adminsToV (vals vs ++ expression cont)) := by
  let σ : List (IL.Id × Value) := [("n", .num (.natN vs.length)),
    ("instr'*", .list (instrsToV cont)), ("val'*", .list (adminsToV (vals vs'))),
    ("val*", .list (adminsToV (vals vs))), ("instr*", .list (adminsToV rest))]
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" =
      some (.num (.natN (adminsToV (vals vs)).length)) := by
    rw [Pure.adminsToV_vals_length]; rfl
  have he := Pure.eval_brZero (env := simEnv20T B) fn rfl rfl rfl rfl
  rw [Pure.adminsToV_vals_length] at he
  have eb : adminsToV (vals (vs' ++ vs) ++ [.plain (.br l)] ++ rest) =
      adminsToV (vals vs') ++ adminsToV (vals vs) ++ [.case "BR" (pctV 0)] ++ adminsToV rest := by
    rw [Pure.vals_append, Pure.adminsToV_append, Pure.adminsToV_append, Pure.adminsToV_append, ← hl]
    rfl
  rw [Pure.adminsToV_label, eb, Pure.adminsToV_append, Pure.adminsToV_expression]
  exact dderives_of_ruleAt (hasRuleAt_brZeroT B) σ (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons rfl (hc _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (typedV_valsT20T vs' _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (typedV_valsT20T vs _ ⟨rfl, rfl, rfl⟩)
        (QuantsOk.cons rfl (hr _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))))) he Sim.Exn.prems_nil

/-- **`br-succ` in `simEnv20T`.** -/
theorem spureT_brSucc {n : Nat} {cont : List V2.Instr} {vs : List Val} {l : LabelIdx}
    {rest : List Admin} (hpos : 0 < l.toNat)
    (hn : TypedV (simEnv20T B) Pure.nT (.num (.natN n)))
    (hc : TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV cont)))
    (hr : TypedV (simEnv20T B) Pure.instrsT (.list (adminsToV rest))) :
    SPure (simEnv20T B) (adminsToV [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)])
      (adminsToV (vals vs ++ [.plain (.br (labelPred l))])) := by
  have hl : TypedV (simEnv20T B) Pure.labelidxT (pctV (l.toNat - 1)) :=
    StoreAgree.typedV_to20T (by decide) (Whole.typedV_labelidx20 (labelPred l))
  let σ : List (IL.Id × Value) := [("n", .num (.natN n)), ("instr'*", .list (instrsToV cont)),
    ("val*", .list (adminsToV (vals vs))), ("l", pctV (l.toNat - 1)),
    ("instr*", .list (adminsToV rest))]
  have he := Pure.eval_brSucc (env := simEnv20T B) (ρ := VarEnv.empty.bindVals σ) rfl rfl rfl rfl rfl
  rw [Nat.sub_add_cancel hpos] at he
  have eb : adminsToV (vals vs ++ [.plain (.br l)] ++ rest) =
      adminsToV (vals vs) ++ [.case "BR" (pctV l.toNat)] ++ adminsToV rest := by
    rw [Pure.adminsToV_append, Pure.adminsToV_append]; rfl
  have er : adminsToV (vals vs ++ [.plain (.br (labelPred l))]) =
      adminsToV (vals vs) ++ [.case "BR" (pctV (l.toNat - 1))] := by
    rw [Pure.adminsToV_append]; rfl
  rw [Pure.adminsToV_label, eb, er]
  exact dderives_of_ruleAt (hasRuleAt_brSuccT B) σ (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons rfl (hc _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (typedV_valsT20T vs _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (hl _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hr _ ⟨rfl, rfl, rfl⟩)
        QuantsOk.nil))))) he Sim.Exn.prems_nil

/-- **`return-frame` in `simEnv20T`.** -/
theorem spureT_returnFrame {fr : Frame} {vs' vs : List Val} {rest : List Admin}
    (hn : TypedV (simEnv20T B) Pure.nT (.num (.natN vs.length)))
    (hfr : TypedV (simEnv20T B) Pure.frameT (frameV fr))
    (hr : TypedV (simEnv20T B) Pure.instrsT (.list (adminsToV rest))) :
    SPure (simEnv20T B)
      (adminsToV [.frame vs.length fr (vals (vs' ++ vs) ++ [.plain .return_] ++ rest)])
      (adminsToV (vals vs)) := by
  let σ : List (IL.Id × Value) := [("n", .num (.natN vs.length)), ("f", frameV fr),
    ("val'*", .list (adminsToV (vals vs'))), ("val*", .list (adminsToV (vals vs))),
    ("instr*", .list (adminsToV rest))]
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" =
      some (.num (.natN (adminsToV (vals vs)).length)) := by
    rw [Pure.adminsToV_vals_length]; rfl
  have he := Pure.eval_returnFrame (env := simEnv20T B) fn rfl rfl rfl rfl
  rw [Pure.adminsToV_vals_length] at he
  have eb : adminsToV (vals (vs' ++ vs) ++ [.plain .return_] ++ rest) =
      adminsToV (vals vs') ++ adminsToV (vals vs) ++ [caseNilV "RETURN"] ++ adminsToV rest := by
    rw [Pure.vals_append, Pure.adminsToV_append, Pure.adminsToV_append, Pure.adminsToV_append]
    rfl
  rw [Pure.adminsToV_frame, eb]
  exact dderives_of_ruleAt (hasRuleAt_returnFrameT B) σ (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons rfl (hfr _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (typedV_valsT20T vs' _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (typedV_valsT20T vs _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hr _ ⟨rfl, rfl, rfl⟩)
        QuantsOk.nil))))) he Sim.Exn.prems_nil

/-- **`return-label` in `simEnv20T`.** -/
theorem spureT_returnLabel {n : Nat} {cont : List V2.Instr} {vs : List Val} {rest : List Admin}
    (hn : TypedV (simEnv20T B) Pure.nT (.num (.natN n)))
    (hc : TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV cont)))
    (hr : TypedV (simEnv20T B) Pure.instrsT (.list (adminsToV rest))) :
    SPure (simEnv20T B) (adminsToV [.label n cont (vals vs ++ [.plain .return_] ++ rest)])
      (adminsToV (vals vs ++ [.plain .return_])) := by
  let σ : List (IL.Id × Value) := [("n", .num (.natN n)), ("instr'*", .list (instrsToV cont)),
    ("val*", .list (adminsToV (vals vs))), ("instr*", .list (adminsToV rest))]
  have he := Pure.eval_returnLabel (env := simEnv20T B) (ρ := VarEnv.empty.bindVals σ) rfl rfl rfl rfl
  have e₁ : adminsToV (vals vs ++ [.plain .return_] ++ rest) =
      adminsToV (vals vs) ++ [caseNilV "RETURN"] ++ adminsToV rest := by
    rw [Pure.adminsToV_append, Pure.adminsToV_append]; rfl
  have e₂ : adminsToV (vals vs ++ [.plain .return_]) = adminsToV (vals vs) ++ [caseNilV "RETURN"] := by
    rw [Pure.adminsToV_append]; rfl
  rw [Pure.adminsToV_label, e₁, e₂]
  exact dderives_of_ruleAt (hasRuleAt_returnLabelT B) σ (QuantsOk.cons rfl (hn _ ⟨rfl, rfl, rfl⟩)
    (QuantsOk.cons rfl (hc _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (typedV_valsT20T vs _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons rfl (hr _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))) he Sim.Exn.prems_nil

/-- **`trap-vals` in `simEnv20T`.** -/
theorem spureT_trapVals {vs : List Val} {rest : List Admin} (hne : vs ≠ [] ∨ rest ≠ [])
    (hr : TypedV (simEnv20T B) Pure.instrsT (.list (adminsToV rest))) :
    SPure (simEnv20T B) (adminsToV (vals vs ++ [.trap] ++ rest)) (adminsToV [.trap]) := by
  let σ : List (IL.Id × Value) :=
    [("val*", .list (adminsToV (vals vs))), ("instr*", .list (adminsToV rest))]
  have fv : (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list (adminsToV (vals vs))) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "instr*" = some (.list (adminsToV rest)) := rfl
  have he := Pure.eval_trapVals (env := simEnv20T B) fv fi
  rw [Pure.adminsToV_marked]
  have hne' : decide (adminsToV (vals vs) ≠ [] ∨ adminsToV rest ≠ []) = true := by
    rw [Pure.adminsToV_vals, Pure.adminsToV_eq_map rest]
    simpa [List.map_eq_nil_iff] using hne
  have hpr : EvalExp (simEnv20T B) (VarEnv.empty.bindVals σ) (.binE .orOp .boolT
      (.cmpE .neOp .boolT (Equiv.Execution.iterPat "val" "val*") (.listE []))
      (.cmpE .neOp .boolT (Equiv.Execution.iterPat "instr" "instr*") (.listE []))) (.bool true) :=
    hne' ▸ evalExp_or (evalExp_ne_nil (Equiv.Execution.evalExp_iterPat (by decide) fv))
      (evalExp_ne_nil (Equiv.Execution.evalExp_iterPat (by decide) fi))
  exact dderives_of_ruleAt (hasRuleAt_trapValsT B) σ
    (QuantsOk.cons fv (typedV_valsT20T vs _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons fi (hr _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)) he
    (Sim.prems_one (.ifPr hpr))

end Silmaril.Wasm.SpecTec.Sim20.StoreGood
