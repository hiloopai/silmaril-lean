module

public import Silmaril.Wasm.SpecTec.Sim20.VecTyp.Thms

/-!
# The context rules of `Step` in the corrected vector script `simEnv20V`

The vector errata (`VecFix.fixedV20`) change only type definitions, so `Step`'s rules 2, 3 and 4
are `StepFix.ctxtInstrsFix`, `ctxtLabelFix` and `ctxtFrameFix` in `simEnv20V B` too
(`hasRuleAt_*FixV`, kernel `rfl`). The proofs of `StoreFix.sstepT_ctxtInstrs`,
`StoreRun.sstepT_ctxtLabel` and `sstepT_ctxtFrame` then go through at `simEnv20V B`, with every
quantified value typed there:

* **`sstepV_ctxtInstrs`**, **`sstepV_ctxtLabel`**, **`sstepV_ctxtFrame`**.

The typing inversions  (`Whole.typedV_adminLabel20_iff`, `typedV_adminFrame20_iff`,
`typedV_stateV_iff`) are restated at `simEnv20V B` (`typedV_adminLabelV_iff`,
`typedV_adminFrameV_iff`, `typedV_stateVV_iff`): the `LABEL_` and `FRAME_` cases of the corrected
`admininstr`, and the type `state`, are the original ones.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecWhole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (evalExp_iterPat)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk SStep cfgV stV TypedV ValsOnly stateT storeT frameT nT
  instrsT dderives_of_ruleAt evalExp_tup2 evalExp_tup3 evalExp_case evalExp_list1 evalExp_cat
  evalExp_ne_nil evalExp_or prems_one prems_two)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (ctxtInstrsFix ctxtLabelFix ctxtFrameFix valsTy adminsTy
  valsE iterV stE)
open Silmaril.Wasm.SpecTec.Sim20.Whole (evalExp_subIterPat)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V variantCases adminFixV20 findTyp_admin20V)

set_option maxRecDepth 100000

variable (B : Builtins)

/-! ## The context rules are unchanged -/

theorem hasRuleAt_ctxtInstrsFixV : HasRuleAt (simEnv20V B) "Step" "%~>%" 2 ctxtInstrsFix :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_ctxtLabelFixV : HasRuleAt (simEnv20V B) "Step" "%~>%" 3 ctxtLabelFix :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_ctxtFrameFixV : HasRuleAt (simEnv20V B) "Step" "%~>%" 4 ctxtFrameFix :=
  ⟨_, _, _, rfl, rfl, rfl⟩

variable {B}

/-! ## The three lifts -/

/-- **`Step/ctxt-instrs`** in `simEnv20V` (the proof of `StoreFix.sstepT_ctxtInstrs`). -/
theorem sstepV_ctxtInstrs {z z' : Value} {vs is is' rest : List Value}
    (hz : TypedV (simEnv20V B) stateT z) (hz' : TypedV (simEnv20V B) stateT z')
    (hvs : TypedV (simEnv20V B) valsTy (.list vs)) (his : TypedV (simEnv20V B) adminsTy (.list is))
    (his' : TypedV (simEnv20V B) adminsTy (.list is'))
    (hrest : TypedV (simEnv20V B) adminsTy (.list rest)) (hne : vs ≠ [] ∨ rest ≠ [])
    (hs : SStep (simEnv20V B) (cfgV z is) (cfgV z' is')) :
    SStep (simEnv20V B) (cfgV z (vs ++ is ++ rest)) (cfgV z' (vs ++ is' ++ rest)) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("val*", .list vs), ("instr*", .list is),
    ("instr_1*", .list rest), ("z'", z'), ("instr'*", .list is')]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fv : ρ.findVal? "val*" = some (.list vs) := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have fr : ρ.findVal? "instr_1*" = some (.list rest) := rfl
  have fz' : ρ.findVal? "z'" = some z' := rfl
  have fi' : ρ.findVal? "instr'*" = some (.list is') := rfl
  have hq : QuantsOk (simEnv20V B) ρ [.expP "z" stateT, .expP "val*" valsTy,
      .expP "instr*" adminsTy, .expP "instr_1*" adminsTy, .expP "z'" stateT,
      .expP "instr'*" adminsTy] :=
    QuantsOk.cons fz (hz ρ hρ)
      (QuantsOk.cons fv (hvs ρ hρ)
      (QuantsOk.cons fi (his ρ hρ)
      (QuantsOk.cons fr (hrest ρ hρ)
      (QuantsOk.cons fz' (hz' ρ hρ)
      (QuantsOk.cons fi' (his' ρ hρ) QuantsOk.nil)))))
  have ev : EvalExp (simEnv20V B) ρ valsE (.list vs) := evalExp_subIterPat (by decide) fv
  have ev' : EvalExp (simEnv20V B) ρ (iterV "val" "val*") (.list vs) :=
    evalExp_iterPat (by decide) fv
  have ei : EvalExp (simEnv20V B) ρ (iterV "instr" "instr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ei' : EvalExp (simEnv20V B) ρ (iterV "instr'" "instr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have er : EvalExp (simEnv20V B) ρ (iterV "instr_1" "instr_1*") (.list rest) :=
    evalExp_iterPat (by decide) fr
  have hor : EvalExp (simEnv20V B) ρ (.binE .orOp .boolT
      (.cmpE .neOp .boolT (iterV "val" "val*") (.listE []))
      (.cmpE .neOp .boolT (iterV "instr_1" "instr_1*") (.listE [])))
      (.bool (decide (vs ≠ [] ∨ rest ≠ []))) :=
    evalExp_or (evalExp_ne_nil ev') (evalExp_ne_nil er)
  have hd : decide (vs ≠ [] ∨ rest ≠ []) = true := decide_eq_true hne
  have hg : SStep (simEnv20V B) (cfgV z (vs ++ (is ++ rest))) (cfgV z' (vs ++ (is' ++ rest))) :=
    dderives_of_ruleAt (hasRuleAt_ctxtInstrsFixV B) _ hq
      (evalExp_tup2
        (evalExp_case (op := "%;%")
          (evalExp_tup2 (evalExp_var fz) (evalExp_cat ev (evalExp_cat ei er))))
        (evalExp_case (op := "%;%")
          (evalExp_tup2 (evalExp_var fz') (evalExp_cat ev (evalExp_cat ei' er)))))
      (prems_two
        (.rulePr Equiv.evalArgs_nil
          (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei))
            (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz') ei'))) hs)
        (.ifPr (hd ▸ hor)))
  simpa only [List.append_assoc] using hg

/-- **`Step/ctxt-label`** in `simEnv20V` (the proof of `StoreRun.sstepT_ctxtLabel`). -/
theorem sstepV_ctxtLabel {z z' n : Value} {cont is is' : List Value}
    (hz : TypedV (simEnv20V B) stateT z) (hz' : TypedV (simEnv20V B) stateT z')
    (hn : TypedV (simEnv20V B) nT n) (hc : TypedV (simEnv20V B) instrsT (.list cont))
    (his : TypedV (simEnv20V B) adminsTy (.list is))
    (his' : TypedV (simEnv20V B) adminsTy (.list is'))
    (hs : SStep (simEnv20V B) (cfgV z is) (cfgV z' is')) :
    SStep (simEnv20V B) (cfgV z [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is])])
      (cfgV z' [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is'])]) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("n", n), ("instr_0*", .list cont),
    ("instr*", .list is), ("z'", z'), ("instr'*", .list is')]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fn : ρ.findVal? "n" = some n := rfl
  have fc : ρ.findVal? "instr_0*" = some (.list cont) := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have fz' : ρ.findVal? "z'" = some z' := rfl
  have fi' : ρ.findVal? "instr'*" = some (.list is') := rfl
  have hq : QuantsOk (simEnv20V B) ρ [.expP "z" stateT, .expP "n" nT, .expP "instr_0*" instrsT,
      .expP "instr*" adminsTy, .expP "z'" stateT, .expP "instr'*" adminsTy] :=
    QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons fc (hc ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons fz' (hz' ρ hρ)
      (QuantsOk.cons fi' (his' ρ hρ) QuantsOk.nil)))))
  have ec : EvalExp (simEnv20V B) ρ (iterV "instr_0" "instr_0*") (.list cont) :=
    evalExp_iterPat (by decide) fc
  have ei : EvalExp (simEnv20V B) ρ (iterV "instr" "instr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ei' : EvalExp (simEnv20V B) ρ (iterV "instr'" "instr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  exact dderives_of_ruleAt (hasRuleAt_ctxtLabelFixV B) _ hq
    (evalExp_tup2
      (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) (evalExp_list1
        (evalExp_case (op := "LABEL_%{%}%") (evalExp_tup3 (evalExp_var fn) ec ei)))))
      (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz') (evalExp_list1
        (evalExp_case (op := "LABEL_%{%}%") (evalExp_tup3 (evalExp_var fn) ec ei'))))))
    (prems_one (.rulePr Equiv.evalArgs_nil
      (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei))
        (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz') ei'))) hs))

/-- **`Step/ctxt-frame`** in `simEnv20V` (the proof of `StoreRun.sstepT_ctxtFrame`). -/
theorem sstepV_ctxtFrame {s s' f fr fr' n : Value} {is is' : List Value}
    (hs₁ : TypedV (simEnv20V B) storeT s) (hs₂ : TypedV (simEnv20V B) storeT s')
    (hf : TypedV (simEnv20V B) frameT f) (hfr : TypedV (simEnv20V B) frameT fr)
    (hfr' : TypedV (simEnv20V B) frameT fr') (hn : TypedV (simEnv20V B) nT n)
    (his : TypedV (simEnv20V B) adminsTy (.list is))
    (his' : TypedV (simEnv20V B) adminsTy (.list is'))
    (hst : SStep (simEnv20V B) (cfgV (stV s fr) is) (cfgV (stV s' fr') is')) :
    SStep (simEnv20V B) (cfgV (stV s f) [.case "FRAME_%{%}%" (.tuple [n, fr, .list is])])
      (cfgV (stV s' f) [.case "FRAME_%{%}%" (.tuple [n, fr', .list is'])]) := by
  let ρ := VarEnv.empty.bindVals [("s", s), ("f", f), ("n", n), ("f'", fr), ("instr*", .list is),
    ("s'", s'), ("f''", fr'), ("instr'*", .list is')]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fs : ρ.findVal? "s" = some s := rfl
  have ff : ρ.findVal? "f" = some f := rfl
  have fn : ρ.findVal? "n" = some n := rfl
  have ffr : ρ.findVal? "f'" = some fr := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have fs' : ρ.findVal? "s'" = some s' := rfl
  have ffr' : ρ.findVal? "f''" = some fr' := rfl
  have fi' : ρ.findVal? "instr'*" = some (.list is') := rfl
  have hq : QuantsOk (simEnv20V B) ρ [.expP "s" storeT, .expP "f" frameT, .expP "n" nT,
      .expP "f'" frameT, .expP "instr*" adminsTy, .expP "s'" storeT, .expP "f''" frameT,
      .expP "instr'*" adminsTy] :=
    QuantsOk.cons fs (hs₁ ρ hρ) (QuantsOk.cons ff (hf ρ hρ) (QuantsOk.cons fn (hn ρ hρ)
      (QuantsOk.cons ffr (hfr ρ hρ) (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons fs' (hs₂ ρ hρ)
      (QuantsOk.cons ffr' (hfr' ρ hρ) (QuantsOk.cons fi' (his' ρ hρ) QuantsOk.nil)))))))
  have ei : EvalExp (simEnv20V B) ρ (iterV "instr" "instr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ei' : EvalExp (simEnv20V B) ρ (iterV "instr'" "instr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have est : EvalExp (simEnv20V B) ρ (stE (.varE "s") (.varE "f")) (stV s f) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ff))
  have est' : EvalExp (simEnv20V B) ρ (stE (.varE "s'") (.varE "f")) (stV s' f) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ff))
  have ein : EvalExp (simEnv20V B) ρ (stE (.varE "s") (.varE "f'")) (stV s fr) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ffr))
  have ein' : EvalExp (simEnv20V B) ρ (stE (.varE "s'") (.varE "f''")) (stV s' fr') :=
    evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ffr'))
  exact dderives_of_ruleAt (hasRuleAt_ctxtFrameFixV B) _ hq
    (evalExp_tup2
      (evalExp_case (op := "%;%") (evalExp_tup2 est (evalExp_list1
        (evalExp_case (op := "FRAME_%{%}%") (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr) ei)))))
      (evalExp_case (op := "%;%") (evalExp_tup2 est' (evalExp_list1
        (evalExp_case (op := "FRAME_%{%}%")
          (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr') ei'))))))
    (prems_one (.rulePr Equiv.evalArgs_nil
      (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 ein ei))
        (evalExp_case (op := "%;%") (evalExp_tup2 ein' ei'))) hst))

/-! ## Typing inversions at `simEnv20V` -/

theorem findCase_labelV : findCase (variantCases adminFixV20) "LABEL_%{%}%" =
    some (.tupT [.mk "n" nT, .mk "instr*" instrsT, .mk "admininstr*" adminsTy], []) := by
  with_unfolding_all rfl

theorem findCase_frameV : findCase (variantCases adminFixV20) "FRAME_%{%}%" =
    some (.tupT [.mk "n" nT, .mk "frame" frameT, .mk "admininstr*" adminsTy], []) := by
  with_unfolding_all rfl

/-- The payload of a typed `admininstr` case of `simEnv20V`, at the case's declared type. -/
theorem hasTyp_adminCaseV {op : MixopS} {t : Typ} {prems : List Prem} {w : Value}
    (hf : findCase (variantCases adminFixV20) op = some (t, prems))
    (h : TypedV (simEnv20V B) (.varT "admininstr" []) (.case op w)) :
    HasTyp (simEnv20V B) VarEnv.empty t w := by
  obtain ⟨op', w', he, hc⟩ :=
    hasTypDef_variantT_iff.1 (Whole.hasTypDef_of_closed findTyp_admin20V (h _ Whole.valsOnly_empty))
  obtain ⟨rfl, rfl⟩ : op = op' ∧ w = w' := by simpa using he
  exact Sim.IntNumeric.hasTyp_of_hasTypCase hc hf

/-- **A label is a typed `admininstr` of `simEnv20V` exactly when its parts are typed.** -/
theorem typedV_adminLabelV_iff {n : Nat} {cont : List V2.Instr} {body : List Admin} :
    TypedV (simEnv20V B) (.varT "admininstr" []) (adminToV (.label n cont body)) ↔
      TypedV (simEnv20V B) nT (.num (.natN n)) ∧
        TypedV (simEnv20V B) instrsT (.list (instrsToV cont)) ∧
        TypedV (simEnv20V B) adminsTy (.list (adminsToV body)) := by
  constructor
  · intro h
    obtain ⟨h₁, h₂, h₃⟩ := Whole.hasTyp_tup3_inv20 (hasTyp_adminCaseV findCase_labelV h)
    exact ⟨h₁, Whole.typedV_list_of_valsOnly20 ⟨rfl, rfl, rfl⟩ h₂, h₃⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact Pure.typedV_closedCase20 findTyp_admin20V findCase_labelV
      (Whole.hasTyp_tup3_mk20 h₁ h₂ h₃)

/-- **A frame is a typed `admininstr` of `simEnv20V` exactly when its parts are typed.** -/
theorem typedV_adminFrameV_iff {n : Nat} {fr : Frame} {body : List Admin} :
    TypedV (simEnv20V B) (.varT "admininstr" []) (adminToV (.frame n fr body)) ↔
      TypedV (simEnv20V B) nT (.num (.natN n)) ∧ TypedV (simEnv20V B) frameT (frameV fr) ∧
        TypedV (simEnv20V B) adminsTy (.list (adminsToV body)) := by
  constructor
  · intro h
    obtain ⟨h₁, h₂, h₃⟩ := Whole.hasTyp_tup3_inv20 (hasTyp_adminCaseV findCase_frameV h)
    exact ⟨h₁, Whole.typedV_of_valsOnly20 ⟨rfl, rfl, rfl⟩ h₂, h₃⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact Pure.typedV_closedCase20 findTyp_admin20V findCase_frameV
      (Whole.hasTyp_tup3_mk20 h₁ h₂ h₃)

theorem typedV_adminsV_single_iff {a : Admin} :
    TypedV (simEnv20V B) adminsTy (.list (adminsToV [a])) ↔
      TypedV (simEnv20V B) (.varT "admininstr" []) (adminToV a) := by
  simp [Sim.typedV_list_iff, adminsToV]

theorem typedV_adminsV_append_iff {l₁ l₂ : List Admin} :
    TypedV (simEnv20V B) adminsTy (.list (adminsToV (l₁ ++ l₂))) ↔
      TypedV (simEnv20V B) adminsTy (.list (adminsToV l₁)) ∧
        TypedV (simEnv20V B) adminsTy (.list (adminsToV l₂)) := by
  simp only [Pure.adminsToV_append, Sim.typedV_list_iff, List.mem_append]
  exact ⟨fun h => ⟨fun u hu => h u (.inl hu), fun u hu => h u (.inr hu)⟩,
    fun ⟨h₁, h₂⟩ u hu => hu.elim (h₁ u) (h₂ u)⟩

set_option maxRecDepth 100000 in
theorem findTyp_stateV : (simEnv20V B).findTyp? "state" =
    some ([], [.instD [] [] (.variantT [.mk "%;%" (.tupT [.mk "store" (.varT "store" []),
      .mk "frame" (.varT "frame" [])]) [] []])]) := rfl

/-- **A state image of `simEnv20V` is typed exactly when its store and frame are.** -/
theorem typedV_stateVV_iff {H : Type} {hn : H → String} {s : Store H} {f : Frame} :
    TypedV (simEnv20V B) stateT (stateV hn s f) ↔
      TypedV (simEnv20V B) storeT (storeV hn s) ∧ TypedV (simEnv20V B) frameT (frameV f) :=
  ⟨Whole.typedV_pair_inv findTyp_stateV,
    fun ⟨hs, hf⟩ => Pure.typedV_closedCase20 findTyp_stateV rfl (Whole.hasTyp_tup2G hs hf)⟩

end Silmaril.Wasm.SpecTec.Sim20.VecWhole
