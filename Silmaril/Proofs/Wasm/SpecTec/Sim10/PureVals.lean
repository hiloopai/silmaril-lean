module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Assemble2
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureConcat

/-!
# The value-sequence rules of 1.0 `Step_pure`, backwards, with 2.0's evaluation lemmas

`label-vals` (7), `br-zero` (8), `frame-vals` (14), `return-frame` (15), `return-label` (16) and
`trap-vals` (17) are byte-identical in 1.0 and 2.0 (census `same`). The 2.0 lemmas that evaluate
their conclusions (`Sim20.Pure.eval_labelVals`, `eval_brZero`, `eval_frameVals`,
`eval_returnFrame`, `eval_returnLabel`, `eval_trapVals`, and `evalExp_valsN_inv`, `or_of_eval`) are
stated for any environment, so **they apply verbatim to `simEnv10 B`**: this is the per-rule
transfer from 2.0 to 1.0. What is 1.0's is the decoding: the conclusion is compared with the 1.0
image of V1 code, and a typed `val*` is read back as V1 values (`const_of_typed10`).

Backwards, each is the V1 `PureStep` of the same name: `labelDone`, `labelBranch`, `frameDone`,
`frameReturn`, `labelReturn`, and `trapValues`/`trapTail` (V1 splits `trap-vals` by whether the
value prefix is empty).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  expression)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk quant_list)
open Silmaril.Wasm.SpecTec.Sim20.Pure (quant_val quant_listT evalExp_valsN_inv eval_labelVals
  eval_frameVals eval_trapVals eval_returnLabel eval_brZero eval_returnFrame or_of_eval ifPrem
  fires_inv)

set_option maxRecDepth 100000

variable {B : Builtins}

/-! ## Decoding value sequences -/

/-- Every element of a typed 1.0 `val*` is headed `CONST`. -/
theorem consts_of_typed10 {ρ : VarEnv} (hρ : Sim.ValsOnly ρ) {ws : List Value}
    (h : HasTyp (simEnv10 B) ρ (.iterT (.varT "val" []) .list) (.list ws)) :
    ∀ u ∈ ws, ∃ w, u = .case "CONST" w := by
  obtain ⟨vs, hvs, hl⟩ := hasTyp_iterT_list_iff.1 h
  obtain rfl := (Value.list.inj hvs).symm
  exact fun u hu => const_of_typed10 hρ (hasTypList_iff.1 hl u hu)

/-- Code whose image is headed `CONST` throughout is a sequence of V1 values. -/
theorem values_of_image {l : List Admin} {ws : List Value} (hl : adminsToV l = ws)
    (hc : ∀ u ∈ ws, ∃ w, u = .case "CONST" w) : ∃ us, l = values us := by
  refine values_of_all fun a ha => ?_
  have hm : adminToV a ∈ ws := by rw [← hl, adminsToV_map10]; exact List.mem_map_of_mem ha
  obtain ⟨w, hw⟩ := hc _ hm
  exact admin_of_const10 hw

/-- An image split at one marked element comes from code split there. -/
theorem split_marked10 {l : List Admin} {ws rs : List Value} {x : Value}
    (h : adminsToV l = ws ++ x :: rs) :
    ∃ l₁ m l₃, l = l₁ ++ [m] ++ l₃ ∧ adminsToV l₁ = ws ∧ adminToV m = x ∧ adminsToV l₃ = rs := by
  rw [adminsToV_map10] at h
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.1 h
  obtain ⟨m, l₃, rfl, hm, h₃⟩ := List.map_eq_cons_iff.1 h₂
  exact ⟨l₁, m, l₃, by simp, by rw [adminsToV_map10, h₁], hm, by rw [adminsToV_map10, h₃]⟩

/-- An image split in two comes from code split in two. -/
theorem split2_10 {l : List Admin} {xs ys : List Value} (h : adminsToV l = xs ++ ys) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ adminsToV l₁ = xs ∧ adminsToV l₂ = ys := by
  rw [adminsToV_map10] at h
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.1 h
  exact ⟨l₁, l₂, rfl, by rw [adminsToV_map10, h₁], by rw [adminsToV_map10, h₂]⟩

theorem head10_return {a : Admin} (h : adminHead10 a = "RETURN") : a = .source .return_ := by
  revert h; admin_head_inv10

theorem head10_br {a : Admin} (h : adminHead10 a = "BR") : ∃ l, a = .source (.br l) := by
  revert h; admin_head_inv10

/-- The images of a label and a frame. -/
theorem adminsToV_label10 (n : Nat) (cont : V1.Expr) (body : List Admin) :
    adminsToV [.label n cont body] = [.case "LABEL_%{%}%" (.tuple [.num (.natN n),
      .list (instrsToV cont), .list (adminsToV body)])] := rfl

theorem adminsToV_frame10 (n : Nat) (fr : Frame) (body : List Admin) :
    adminsToV [.frame n fr body] =
      [.case "FRAME_%{%}%" (.tuple [.num (.natN n), frameV fr, .list (adminsToV body)])] := rfl

/-- The one element of a single-element image, as a label. -/
theorem label_of_image {l : List Admin} {nv : Value} {cs b : List Value}
    (h : adminsToV l = [.case "LABEL_%{%}%" (.tuple [nv, .list cs, .list b])]) :
    ∃ n cont body, l = [.label n cont body] ∧ Value.num (.natN n) = nv ∧ instrsToV cont = cs ∧
      adminsToV body = b := by
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single10 h
  obtain ⟨n, cont, body, rfl⟩ := adminToV_label_inv10 ha
  simp only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.list.injEq,
    and_true, true_and] at ha
  exact ⟨n, cont, body, rfl, ha.1, ha.2.1, ha.2.2⟩

/-- The one element of a single-element image, as a frame. -/
theorem frame_of_image {l : List Admin} {nv fv : Value} {b : List Value}
    (h : adminsToV l = [.case "FRAME_%{%}%" (.tuple [nv, fv, .list b])]) :
    ∃ n fr body, l = [.frame n fr body] ∧ Value.num (.natN n) = nv ∧ adminsToV body = b := by
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single10 h
  obtain ⟨n, fr, body, rfl⟩ := adminToV_frame_inv10 ha
  simp only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.list.injEq,
    and_true, true_and] at ha
  exact ⟨n, fr, body, rfl, ha.1, ha.2.2⟩

/-- The tuple of a `Step_pure` firing, split. -/
theorem tuple_split {a b c d : Value} (h : Value.tuple [a, b] = .tuple [c, d]) : a = c ∧ b = d := by
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at h
  exact h

/-- A body `val'* val* M rest` with both value runs typed, read back as V1 code. -/
theorem split_vals_marked10 {σ : List (IL.Id × Value)} {body : List Admin}
    {ws₁ ws rs : List Value} {x : Value} (hb : adminsToV body = (ws₁ ++ ws) ++ x :: rs)
    (ht₁ : HasTyp (simEnv10 B) (VarEnv.empty.bindVals σ) (.iterT (.varT "val" []) .list) (.list ws₁))
    (ht : HasTyp (simEnv10 B) (VarEnv.empty.bindVals σ) (.iterT (.varT "val" []) .list) (.list ws)) :
    ∃ extra us m l₃, body = values extra ++ values us ++ [m] ++ l₃ ∧ adminsToV (values us) = ws ∧
      adminToV m = x := by
  obtain ⟨l₁, m, l₃, rfl, h₁₂, hm, -⟩ := split_marked10 hb
  obtain ⟨l₁', l₂, rfl, ha, hb'⟩ := split2_10 h₁₂
  obtain ⟨extra, rfl⟩ := values_of_image ha (consts_of_typed10 (Sim.valsOnly_bindVals σ) ht₁)
  obtain ⟨us, rfl⟩ := values_of_image hb' (consts_of_typed10 (Sim.valsOnly_bindVals σ) ht)
  exact ⟨extra, us, m, l₃, rfl, hb', hm⟩

/-! ## The rules -/

/-- **`Step_pure/label-vals` backwards**: V1's `labelDone`. -/
theorem bwd10_labelVals {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 7 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, hq, he, -⟩ := fires_inv (hasRuleAt10_labelVals B) hf
  obtain ⟨vn, fn⟩ := quant_val (x := "n") (t := .varT "n" []) hq (by simp)
  obtain ⟨cs, fc, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws, fv, ht⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨hl, hw⟩ := tuple_split (EvalExp.unique he (eval_labelVals fn fc fv))
  obtain ⟨n, cont, body, rfl, -, -, hb⟩ := label_of_image (Value.list.inj hl)
  obtain ⟨us, rfl⟩ := values_of_image hb (consts_of_typed10 (Sim.valsOnly_bindVals σ) ht)
  exact pureBwd10_of (hw.trans (congrArg Value.list hb.symm)) (.labelDone n cont us)

/-- **`Step_pure/frame-vals` backwards**: V1's `frameDone`. -/
theorem bwd10_frameVals {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 14 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, hq, he, -⟩ := fires_inv (hasRuleAt10_frameVals B) hf
  obtain ⟨vf, ff⟩ := quant_val (x := "f") (t := .varT "frame" []) hq (by simp)
  obtain ⟨ws', fv', ht⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨ws, fv, fn, -⟩ := evalExp_valsN_inv (by decide) (Sim.RefsGC.rhs_of_concl he)
  have ew : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  obtain ⟨hl, hw⟩ := tuple_split (EvalExp.unique he (eval_frameVals fn ff fv))
  obtain ⟨n, fr, body, rfl, hn, hb⟩ := frame_of_image (Value.list.inj hl)
  obtain ⟨us, rfl⟩ := values_of_image hb (consts_of_typed10 (Sim.valsOnly_bindVals σ) (ew ▸ ht))
  have hlen : us.length = n := by
    have := Sim.Bwd.natN_inj hn
    rw [this, ← hb, adminsToV_values, List.length_map]
  exact pureBwd10_of (hw.trans (congrArg Value.list hb.symm)) (.frameDone n fr us hlen)

/-- **`Step_pure/trap-vals` backwards**: V1's `trapValues` or `trapTail`. -/
theorem bwd10_trapVals {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 17 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, hq, he, hp⟩ := fires_inv (hasRuleAt10_trapVals B) hf
  obtain ⟨ws, fv, ht⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨rs, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨hl, hw⟩ := tuple_split (EvalExp.unique he (eval_trapVals fv fi))
  have hor : ws ≠ [] ∨ rs ≠ [] := or_of_eval fv fi (ifPrem (hp _ (List.mem_singleton_self _)))
  obtain ⟨l₁, m, l₃, rfl, h₁, hm, h₃⟩ := split_marked10 (Value.list.inj hl)
  obtain rfl := head10_trap (adminToV_case10 hm)
  obtain ⟨us, rfl⟩ := values_of_image h₁ (consts_of_typed10 (Sim.valsOnly_bindVals σ) ht)
  have hw' : Value.list w = .list (adminsToV [.trap]) := hw
  rcases us with _ | ⟨v, us⟩
  · cases l₃ with
    | nil =>
      exfalso
      rcases hor with h | h
      · exact h (h₁.symm.trans rfl)
      · exact h h₃.symm
    | cons i tail => exact pureBwd10_of hw' (.trapTail i tail)
  · exact pureBwd10_of hw' (.trapValues v us l₃)

/-- **`Step_pure/return-label` backwards**: V1's `labelReturn`. -/
theorem bwd10_returnLabel {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 16 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, hq, he, -⟩ := fires_inv (hasRuleAt10_returnLabel B) hf
  obtain ⟨vn, fn⟩ := quant_val (x := "n") (t := .varT "n" []) hq (by simp)
  obtain ⟨cs, fc, -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws, fv, ht⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨rs, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨hl, hw⟩ := tuple_split (EvalExp.unique he (eval_returnLabel fn fc fv fi))
  obtain ⟨n, cont, body, rfl, -, -, hb⟩ := label_of_image (Value.list.inj hl)
  obtain ⟨l₁, m, l₃, rfl, h₁, hm, -⟩ := split_marked10 (by simpa using hb)
  obtain rfl := head10_return (adminToV_case10 hm)
  obtain ⟨us, rfl⟩ := values_of_image h₁ (consts_of_typed10 (Sim.valsOnly_bindVals σ) ht)
  have hw' : Value.list w = .list (adminsToV (values us ++ [.source .return_])) := by
    rw [hw, adminsToV_map10, List.map_append, ← adminsToV_map10, h₁]
    rfl
  exact pureBwd10_of hw' (.labelReturn n cont us l₃)

/-- **`Step_pure/br-zero` backwards**: V1's `labelBranch`. -/
theorem bwd10_brZero {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 8 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, hq, he, -⟩ := fires_inv (hasRuleAt10_brZero B) hf
  obtain ⟨cs, fc, -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws₁, fv₁, ht₁⟩ := quant_listT (x := "val'*") (t := .varT "val" []) hq (by simp)
  obtain ⟨ws', fv', ht⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨rs, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨v₁, v₂, h₁, -, -⟩ := evalExp_catE_iff.1 (Sim.RefsGC.rhs_of_concl he)
  obtain ⟨ws, fv, fn, -⟩ := evalExp_valsN_inv (by decide) h₁
  have ew : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  obtain ⟨hl, hw⟩ := tuple_split (EvalExp.unique he (eval_brZero fn fc fv₁ fv fi))
  obtain ⟨n, cont, body, rfl, hn, hc, hb⟩ := label_of_image (Value.list.inj hl)
  have hb₂ : adminsToV body = (ws₁ ++ ws) ++ .case "BR" (pctV 0) :: rs := by
    rw [hb]
    simp only [List.append_assoc, List.singleton_append]
  obtain ⟨extra, us, m, l₃, rfl, hb', hm⟩ := split_vals_marked10 hb₂ ht₁ (ew ▸ ht)
  obtain ⟨l, rfl⟩ := head10_br (adminToV_case10 hm)
  have hl0 : l = ⟨0⟩ := Idx.toNat_injective (Sim20.Pure.pctV_inj (Value.case.inj hm).2)
  have hlen : us.length = n := by
    rw [Sim.Bwd.natN_inj hn, ← hb', adminsToV_values, List.length_map]
  have hw' : Value.list w = .list (adminsToV (values us ++ expression cont)) := by
    rw [hw, adminsToV_map10, List.map_append, ← adminsToV_map10, ← adminsToV_map10, hb',
      adminsToV_expression, hc]
  exact hl0 ▸ pureBwd10_of hw' (.labelBranch n cont extra us l₃ hlen)

/-- **`Step_pure/return-frame` backwards**: V1's `frameReturn`. -/
theorem bwd10_returnFrame {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 15 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨σ, hq, he, -⟩ := fires_inv (hasRuleAt10_returnFrame B) hf
  obtain ⟨vf, ff⟩ := quant_val (x := "f") (t := .varT "frame" []) hq (by simp)
  obtain ⟨ws₁, fv₁, ht₁⟩ := quant_listT (x := "val'*") (t := .varT "val" []) hq (by simp)
  obtain ⟨ws', fv', ht⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (by simp)
  obtain ⟨rs, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (by simp)
  obtain ⟨ws, fv, fn, -⟩ := evalExp_valsN_inv (by decide) (Sim.RefsGC.rhs_of_concl he)
  have ew : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  obtain ⟨hl, hw⟩ := tuple_split (EvalExp.unique he (eval_returnFrame fn ff fv₁ fv fi))
  obtain ⟨n, fr, body, rfl, hn, hb⟩ := frame_of_image (Value.list.inj hl)
  have hb₂ : adminsToV body = (ws₁ ++ ws) ++ caseNilV "RETURN" :: rs := by
    rw [hb]
    simp only [List.append_assoc, List.singleton_append]
  obtain ⟨extra, us, m, l₃, rfl, hb', hm⟩ := split_vals_marked10 hb₂ ht₁ (ew ▸ ht)
  obtain rfl := head10_return (adminToV_case10 hm)
  have hlen : us.length = n := by
    rw [Sim.Bwd.natN_inj hn, ← hb', adminsToV_values, List.length_map]
  exact pureBwd10_of (hw.trans (congrArg Value.list hb'.symm)) (.frameReturn n fr extra us l₃ hlen)

end Silmaril.Wasm.SpecTec.Sim10.Whole
