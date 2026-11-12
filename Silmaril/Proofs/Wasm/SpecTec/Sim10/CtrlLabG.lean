module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.CtrlStuckG

/-!
# Stuck labels and frames in every environment like `simEnv10` (track v10)

`LABEL_ 0 {ε} (x TRAP)` and `FRAME_ 0 {f} (x TRAP)`, for an administrative instruction `x` that is
not a value and with `z; x TRAP` stuck (`CtrlStuckG`), are stuck in every environment `E` with
`Like10 B E`, at every builtins:

* at the label (`not_sstepG_labX`): `label-vals` needs a body of values; `br-zero`, `br-succ` and
  `return-label` would type the code after their redex, here `TRAP`, as `instr*`; `trap-label`
  needs the body `TRAP`; `Step/ctxt-label` needs the body to step;
* at the frame (`not_sstepG_frmX`): `frame-vals` needs a body of values; `return-frame` would type
  `TRAP` as `instr*`; `trap-frame` needs the body `TRAP`; `Step/ctxt-frame` needs the body to step.

The other rules' tags do not fit.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.Wasm.SpecTec.Sim (SStep SPure Fires cfgV stV ValsOnly)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (TagsIn)
open Silmaril.Wasm.SpecTec.Sim20.Pure (quant_val quant_listT evalExp_valsN_inv eval_labelVals
  eval_returnLabel eval_brZero eval_brSucc eval_returnFrame eval_frameVals evalExp_caseNil
  labelidxT)

set_option maxRecDepth 100000

variable {B : Builtins} {E : Env}

/-! ## The values -/

/-- The image of `LABEL_ 0 {ε} (a TRAP)`. -/
abbrev labX (a : Admin) : Value := adminToV (.label 0 [] [a, .trap])

/-- The image of `FRAME_ 0 {fr} (a TRAP)`. -/
abbrev frmX (fr : Frame) (a : Admin) : Value := adminToV (.frame 0 fr [a, .trap])

/-- A body `ws ++ [m] ++ rs` that is `x t`, with `ws` values and `x` not a value, has `rs = [t]`. -/
theorem tail_of_body {ws rs : List Value} {x m t : Value}
    (hc : ∀ u ∈ ws, ∃ w, u = .case "CONST" w) (hx : ∀ w, x ≠ .case "CONST" w)
    (hb : ws ++ [m] ++ rs = [x, t]) : rs = [t] := by
  have hn : ws = [] := nil_of_consts10 (l := [t]) (l' := m :: rs) hc hx (by rw [← hb]; simp)
  subst hn
  simp only [List.nil_append, List.singleton_append, List.cons.injEq] at hb
  exact hb.2

/-- The body of the label, read off a rule's left-hand side. -/
theorem body_of_labX {a : Admin} {nv : Value} {cs b : List Value}
    (h : Value.list [labX a] = .list [.case "LABEL_%{%}%" (.tuple [nv, .list cs, .list b])]) :
    b = [adminToV a, trapV10] := by
  simp only [labX, adminToV, adminsToV, Value.list.injEq, List.cons.injEq, Value.case.injEq,
    Value.tuple.injEq, and_true, true_and] at h
  exact h.2.2.symm

/-- The body of the frame, read off a rule's left-hand side. -/
theorem body_of_frmX {fr : Frame} {a : Admin} {nv fv : Value} {b : List Value}
    (h : Value.list [frmX fr a] = .list [.case "FRAME_%{%}%" (.tuple [nv, fv, .list b])]) :
    b = [adminToV a, trapV10] := by
  simp only [frmX, adminToV, adminsToV, Value.list.injEq, List.cons.injEq, Value.case.injEq,
    Value.tuple.injEq, and_true, true_and] at h
  exact h.2.2.symm

/-! ## The `Step_pure` rules at the label -/

section Label

variable {a : Admin} (hL : Like10 B E) (hx : ∀ w, adminToV a ≠ .case "CONST" w)
include hL hx

/-- `label-vals` does not fire: the body is not a run of values. -/
theorem not_firesG_labelVals_labX (w : Value) :
    ¬ Fires E "Step_pure" 7 (.tuple [.list [labX a], w]) := by
  intro hf
  obtain ⟨σ, hq, he, -⟩ := Sim20.Pure.fires_inv (hL.ruleAt (hasRuleAt10_labelVals B)) hf
  obtain ⟨vn, fn⟩ := quant_val (x := "n") (t := .varT "n" []) hq (by simp)
  obtain ⟨cs, fc, -⟩ := quant_listT (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws, fv, ht⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  have hb := body_of_labX (tuple_split (EvalExp.unique he (eval_labelVals fn fc fv))).1
  have hn := nil_of_consts10 (l' := []) (hL.consts (Sim.valsOnly_bindVals σ) ht) hx
    (by rw [List.append_nil, hb])
  rw [hn] at hb
  exact List.cons_ne_nil _ _ hb.symm

/-- `br-zero` does not fire: its tail `TRAP` would be an `instr`. -/
theorem not_firesG_brZero_labX (w : Value) :
    ¬ Fires E "Step_pure" 8 (.tuple [.list [labX a], w]) := by
  intro hf
  obtain ⟨σ, hq, he, -⟩ := Sim20.Pure.fires_inv (hL.ruleAt (hasRuleAt10_brZero B)) hf
  have hρ := Sim.valsOnly_bindVals σ
  obtain ⟨cs, fc, -⟩ := quant_listT (x := "instr'*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws₁, fv₁, ht₁⟩ := quant_listT (x := "val'*") (t := .varT "val" []) hq (by simp)
  obtain ⟨ws', fv', ht'⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨rs, fi, hti⟩ := quant_listT (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨v₁, v₂, h₁, -, -⟩ := evalExp_catE_iff.1 (Sim.RefsGC.rhs_of_concl he)
  obtain ⟨ws, fv, fn, -⟩ := evalExp_valsN_inv (by decide) h₁
  obtain rfl : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  have hb := body_of_labX (tuple_split (EvalExp.unique he (eval_brZero fn fc fv₁ fv fi))).1
  have hc : ∀ u ∈ ws₁ ++ ws', ∃ w, u = .case "CONST" w := fun u hu =>
    (List.mem_append.1 hu).elim (hL.consts hρ ht₁ u) (hL.consts hρ ht' u)
  rw [tail_of_body hc hx hb] at hti
  exact hL.trap hρ (instr_of_listG hti (List.mem_singleton_self _))

/-- `br-succ` does not fire: its tail `TRAP` would be an `instr`. -/
theorem not_firesG_brSucc_labX (w : Value) :
    ¬ Fires E "Step_pure" 9 (.tuple [.list [labX a], w]) := by
  intro hf
  obtain ⟨σ, hq, he, -⟩ := Sim20.Pure.fires_inv (hL.ruleAt (hasRuleAt10_brSucc B)) hf
  have hρ := Sim.valsOnly_bindVals σ
  obtain ⟨vn, fn⟩ := quant_val (x := "n") (t := .varT "n" []) hq (by simp)
  obtain ⟨cs, fc, -⟩ := quant_listT (x := "instr'*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws, fv, ht⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨lv, fl, hlt⟩ := hq "l" labelidxT (by simp)
  obtain ⟨k, rfl⟩ := hL.labelidx hρ hlt
  obtain ⟨rs, fi, hti⟩ := quant_listT (x := "instr*") (t := .varT "instr" []) hq (by simp)
  have hb := body_of_labX (tuple_split (EvalExp.unique he (eval_brSucc fn fc fv fl fi))).1
  rw [tail_of_body (hL.consts hρ ht) hx hb] at hti
  exact hL.trap hρ (instr_of_listG hti (List.mem_singleton_self _))

/-- `return-label` does not fire: its tail `TRAP` would be an `instr`. -/
theorem not_firesG_returnLabel_labX (w : Value) :
    ¬ Fires E "Step_pure" 16 (.tuple [.list [labX a], w]) := by
  intro hf
  obtain ⟨σ, hq, he, -⟩ := Sim20.Pure.fires_inv (hL.ruleAt (hasRuleAt10_returnLabel B)) hf
  have hρ := Sim.valsOnly_bindVals σ
  obtain ⟨vn, fn⟩ := quant_val (x := "n") (t := .varT "n" []) hq (by simp)
  obtain ⟨cs, fc, -⟩ := quant_listT (x := "instr'*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws, fv, ht⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨rs, fi, hti⟩ := quant_listT (x := "instr*") (t := .varT "instr" []) hq (by simp)
  have hb := body_of_labX (tuple_split (EvalExp.unique he (eval_returnLabel fn fc fv fi))).1
  rw [tail_of_body (hL.consts hρ ht) hx hb] at hti
  exact hL.trap hρ (instr_of_listG hti (List.mem_singleton_self _))

omit hx in
/-- `trap-label` does not fire: the body is not `TRAP` alone. -/
theorem not_firesG_trapLabel_labX (w : Value) :
    ¬ Fires E "Step_pure" 18 (.tuple [.list [labX a], w]) := by
  intro hf
  have hf' : Fires E "Step_pure" 18 (.tuple [.list (adminsToV [.label 0 [] [a, .trap]]), w]) := hf
  obtain ⟨σ, -, hes, -, -⟩ := firesPure10_inv (hL.ruleAt (hasRuleAt10_trapLabel B)) hf'
  obtain ⟨a', ha, he⟩ := codes10_one hes
  obtain rfl : a' = .label 0 [] [a, .trap] := by simpa using ha.symm
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 he
  obtain ⟨us, hus, rfl⟩ := evalExp_tupE_iff.1 hu
  obtain ⟨u₁, us₁, -, hus₁, rfl⟩ := evalExps_cons_iff.1 hus
  obtain ⟨u₂, us₂, -, hus₂, rfl⟩ := evalExps_cons_iff.1 hus₁
  obtain ⟨u₃, us₃, h₃, hus₃, rfl⟩ := evalExps_cons_iff.1 hus₂
  obtain rfl := evalExps_nil_iff.1 hus₃
  have hb : Value.list (adminsToV [a, .trap]) = u₃ := by
    simp only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and] at hcu
    exact hcu.2.2.1
  have hb' := hb.trans (EvalExp.unique h₃ (Sim.evalExp_list1 evalExp_caseNil))
  simp [adminsToV] at hb'

/-- **No `Step_pure` step at the label.** -/
theorem not_spureG_labX (js : List Value) : ¬ SPure E [labX a] js := by
  refine not_spureG hL (S := ["LABEL_%{%}%"]) (exc := [7, 8, 9, 16, 18]) tagsIn_one (by decide) ?_
  intro i hi hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact not_firesG_labelVals_labX hL hx _ hf
  · exact not_firesG_brZero_labX hL hx _ hf
  · exact not_firesG_brSucc_labX hL hx _ hf
  · exact not_firesG_returnLabel_labX hL hx _ hf
  · exact not_firesG_trapLabel_labX hL _ hf

omit hx in
/-- `Step/ctxt-label` does not fire when the body is stuck. -/
theorem not_firesG_ctxtLabel_labX (hst : ∀ z w, ¬ SStep E (cfgV z [adminToV a, trapV10]) w)
    (z w : Value) : ¬ Fires E "Step" 2 (.tuple [cfgV z [labX a], w]) := by
  intro hf
  obtain ⟨z₁, z', n, cont, is, is', h₁, -, hs⟩ :=
    inv_ctxtLabel10 (hL.ruleAt (hasRuleAt_ctxtLabel10 B)) hf
  have he := (Sim.Bwd.cfgV_inj h₁).2
  simp only [labX, adminToV, adminsToV, List.cons.injEq, Value.case.injEq, Value.tuple.injEq,
    Value.list.injEq, and_true, true_and] at he
  rw [← he.2.2] at hs
  exact hst z₁ _ hs

/-- **`z; LABEL_ 0 {ε} (a TRAP)` is stuck** when `a` is not a value and `z; a TRAP` is stuck. -/
theorem not_sstepG_labX (hst : ∀ z w, ¬ SStep E (cfgV z [adminToV a, trapV10]) w)
    (z w : Value) : ¬ SStep E (cfgV z [labX a]) w := by
  refine not_sstepG_of hL (S := ["LABEL_%{%}%"]) (exc := [0, 1, 2, 4]) tagsIn_one (by decide) ?_
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact not_firesG_pure hL (not_spureG_labX hL hx)
  · exact not_firesG_read hL fun js => not_sreadG hL tagsIn_one (by decide)
  · exact not_firesG_ctxtLabel_labX hL hst z w
  · exact not_firesG_ctxtInstrs_short hL (by simp)

end Label

/-! ## The `Step_pure` rules at the frame -/

section Frame

variable {fr : Frame} {a : Admin} (hL : Like10 B E) (hx : ∀ w, adminToV a ≠ .case "CONST" w)
include hL hx

/-- `frame-vals` does not fire: the body is not a run of values. -/
theorem not_firesG_frameVals_frmX (w : Value) :
    ¬ Fires E "Step_pure" 14 (.tuple [.list [frmX fr a], w]) := by
  intro hf
  obtain ⟨σ, hq, he, -⟩ := Sim20.Pure.fires_inv (hL.ruleAt (hasRuleAt10_frameVals B)) hf
  obtain ⟨vf, ff⟩ := quant_val (x := "f") (t := .varT "frame" []) hq (by simp)
  obtain ⟨ws', fv', ht⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨ws, fv, fn, -⟩ := evalExp_valsN_inv (by decide) (Sim.RefsGC.rhs_of_concl he)
  obtain rfl : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  have hb := body_of_frmX (tuple_split (EvalExp.unique he (eval_frameVals fn ff fv))).1
  have hn := nil_of_consts10 (l' := []) (hL.consts (Sim.valsOnly_bindVals σ) ht) hx
    (by rw [List.append_nil, hb])
  rw [hn] at hb
  exact List.cons_ne_nil _ _ hb.symm

/-- `return-frame` does not fire: its tail `TRAP` would be an `instr`. -/
theorem not_firesG_returnFrame_frmX (w : Value) :
    ¬ Fires E "Step_pure" 15 (.tuple [.list [frmX fr a], w]) := by
  intro hf
  obtain ⟨σ, hq, he, -⟩ := Sim20.Pure.fires_inv (hL.ruleAt (hasRuleAt10_returnFrame B)) hf
  have hρ := Sim.valsOnly_bindVals σ
  obtain ⟨vf, ff⟩ := quant_val (x := "f") (t := .varT "frame" []) hq (by simp)
  obtain ⟨ws₁, fv₁, ht₁⟩ := quant_listT (x := "val'*") (t := .varT "val" []) hq (by simp)
  obtain ⟨ws', fv', ht'⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨rs, fi, hti⟩ := quant_listT (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws, fv, fn, -⟩ := evalExp_valsN_inv (by decide) (Sim.RefsGC.rhs_of_concl he)
  obtain rfl : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  have hb := body_of_frmX (tuple_split (EvalExp.unique he (eval_returnFrame fn ff fv₁ fv fi))).1
  have hc : ∀ u ∈ ws₁ ++ ws', ∃ w, u = .case "CONST" w := fun u hu =>
    (List.mem_append.1 hu).elim (hL.consts hρ ht₁ u) (hL.consts hρ ht' u)
  rw [tail_of_body hc hx hb] at hti
  exact hL.trap hρ (instr_of_listG hti (List.mem_singleton_self _))

omit hx in
/-- `trap-frame` does not fire: the body is not `TRAP` alone. -/
theorem not_firesG_trapFrame_frmX (w : Value) :
    ¬ Fires E "Step_pure" 19 (.tuple [.list [frmX fr a], w]) := by
  intro hf
  have hf' : Fires E "Step_pure" 19 (.tuple [.list (adminsToV [.frame 0 fr [a, .trap]]), w]) := hf
  obtain ⟨σ, -, hes, -, -⟩ := firesPure10_inv (hL.ruleAt (hasRuleAt10_trapFrame B)) hf'
  obtain ⟨a', ha, he⟩ := codes10_one hes
  obtain rfl : a' = .frame 0 fr [a, .trap] := by simpa using ha.symm
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 he
  obtain ⟨us, hus, rfl⟩ := evalExp_tupE_iff.1 hu
  obtain ⟨u₁, us₁, -, hus₁, rfl⟩ := evalExps_cons_iff.1 hus
  obtain ⟨u₂, us₂, -, hus₂, rfl⟩ := evalExps_cons_iff.1 hus₁
  obtain ⟨u₃, us₃, h₃, hus₃, rfl⟩ := evalExps_cons_iff.1 hus₂
  obtain rfl := evalExps_nil_iff.1 hus₃
  have hb : Value.list (adminsToV [a, .trap]) = u₃ := by
    simp only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and] at hcu
    exact hcu.2.2.1
  have hb' := hb.trans (EvalExp.unique h₃ (Sim.evalExp_list1 evalExp_caseNil))
  simp [adminsToV] at hb'

/-- **No `Step_pure` step at the frame.** -/
theorem not_spureG_frmX (js : List Value) : ¬ SPure E [frmX fr a] js := by
  refine not_spureG hL (S := ["FRAME_%{%}%"]) (exc := [14, 15, 19]) tagsIn_one (by decide) ?_
  intro i hi hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact not_firesG_frameVals_frmX hL hx _ hf
  · exact not_firesG_returnFrame_frmX hL hx _ hf
  · exact not_firesG_trapFrame_frmX hL _ hf

omit hx in
/-- `Step/ctxt-frame` does not fire when the body is stuck. -/
theorem not_firesG_ctxtFrame_frmX (hst : ∀ z w, ¬ SStep E (cfgV z [adminToV a, trapV10]) w)
    (z w : Value) : ¬ Fires E "Step" 3 (.tuple [cfgV z [frmX fr a], w]) := by
  intro hf
  obtain ⟨s, s', f, fr₁, fr', n, is, is', h₁, -, hs⟩ :=
    inv_ctxtFrame10 (hL.ruleAt (hasRuleAt_ctxtFrame10 B)) hf
  have he := (Sim.Bwd.cfgV_inj h₁).2
  simp only [frmX, adminToV, adminsToV, List.cons.injEq, Value.case.injEq, Value.tuple.injEq,
    Value.list.injEq, and_true, true_and] at he
  rw [← he.2.2] at hs
  exact hst _ _ hs

/-- **`z; FRAME_ 0 {fr} (a TRAP)` is stuck** when `a` is not a value and `z; a TRAP` is stuck. -/
theorem not_sstepG_frmX (hst : ∀ z w, ¬ SStep E (cfgV z [adminToV a, trapV10]) w)
    (z w : Value) : ¬ SStep E (cfgV z [frmX fr a]) w := by
  refine not_sstepG_of hL (S := ["FRAME_%{%}%"]) (exc := [0, 1, 3, 4]) tagsIn_one (by decide) ?_
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact not_firesG_pure hL (not_spureG_frmX hL hx)
  · exact not_firesG_read hL fun js => not_sreadG hL tagsIn_one (by decide)
  · exact not_firesG_ctxtFrame_frmX hL hst z w
  · exact not_firesG_ctxtInstrs_short hL (by simp)

end Frame

end Silmaril.Wasm.SpecTec.Sim10.Whole
