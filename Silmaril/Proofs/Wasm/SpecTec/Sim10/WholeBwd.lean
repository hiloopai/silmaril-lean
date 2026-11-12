module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Rules
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Invert

/-!
# The backward half of the 1.0 whole step, assembled from per-rule obligations

`backward10_of_parts`: given the per-rule obligations `BwdParts10 G` (`Step_pure`, `Step_read` and
the `Step` rules from `local.set` on, asked at configurations satisfying an invariant `G`), every
step of the wasm-1.0 script under the backend reading from the image of a V1 configuration
satisfying `G` is the image of a V1 step. The five structural rules of 1.0's `Step` are handled
here, for every configuration:

* `inv_pure10`, `inv_read10`, `inv_ctxtLabel10`, `inv_ctxtFrame10`, `inv_ctxtInstrs10`: rules 0–4
  read backwards, for any environment with their provenance;
* `Step/pure` is V1's `Step.pure` and `Step/read` is any V1 step that keeps the state (V1 reduces
  `block` and `loop` purely, the script by `Step_read`);
* `Step/ctxt-label` and `Step/ctxt-frame` are V1's `label` and `frame` (1.0's `ctxt-frame` lets the
  inner frame change, as V1's does);
* `Step/ctxt-instrs` is V1's `context`: the `val*` prefix is typed `val`, and a typed `val` image
  is a V1 value (`admin_of_val10`).

The recursion is on `codeSize10`, the number of administrative instructions at any depth. The
invariant must pass to label and frame bodies and to infixes (`CfgInv10`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (iterPat evalExp_iterPat)
open Silmaril.Wasm.SpecTec.Sim (RuleBody DDerives otherwise SStep SPure SRead Fires PremW QuantsOk
  ValsOnly cfgV stV evalExp_tup2 evalExp_tup3 evalExp_list1 evalExp_case dderives_iff_fires
  ruleBody_scope quant_of quant_list fires_body evalExp_cat evalExp_or evalExp_ne_nil
  valsOnly_bindVals valsT)
open Silmaril.Wasm.SpecTec.Sim.Bwd (rulePrem_nil ifPrem_true cfgV_inj stV_inj tuple2_inj)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20 (TypedSome)
open Silmaril.Wasm.SpecTec.Sim20.Whole (evalExp_subIterPat)

set_option maxRecDepth 100000

/-! ## The five structural rules, read back -/

section Invert

variable {env : Env}

/-- `Step/pure`, read back. -/
theorem inv_pure10 (h₀ : HasRuleAt env "Step" "%~>%" 0 pureRule10) {v₁ v₂ : Value}
    (hf : Fires env "Step" 0 (.tuple [v₁, v₂])) :
    ∃ z is js, v₁ = cfgV z is ∧ v₂ = cfgV z js ∧ TypedSome env adminsT (.list is) ∧
      TypedSome env adminsT (.list js) ∧ SPure env is js := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body h₀ hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := .varT "state" []) hq (.head _)
  obtain ⟨is, fi, ti⟩ :=
    quant_list (x := "admininstr*") (t := .varT "admininstr" []) hq (.tail _ (.head _))
  obtain ⟨js, fj, tj⟩ :=
    quant_list (x := "admininstr'*") (t := .varT "admininstr" []) hq (.tail _ (.tail _ (.head _)))
  have ei : EvalExp env _ (iterPat "admininstr" "admininstr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ej : EvalExp env _ (iterPat "admininstr'" "admininstr'*") (.list js) :=
    evalExp_iterPat (by decide) fj
  have hc : Value.tuple [v₁, v₂] = .tuple [cfgV z is, cfgV z js] :=
    EvalExp.unique he (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (evalExp_tup2 (evalExp_var fz) ej)))
  have hd : SPure env is js := rulePrem_nil (hp _ (.head _)) (evalExp_tup2 ei ej)
  exact ⟨z, is, js, (tuple2_inj hc).1, (tuple2_inj hc).2, ⟨_, valsOnly_bindVals σ, ti⟩,
    ⟨_, valsOnly_bindVals σ, tj⟩, hd⟩

/-- `Step/read`, read back. -/
theorem inv_read10 (h₀ : HasRuleAt env "Step" "%~>%" 1 readRule10) {v₁ v₂ : Value}
    (hf : Fires env "Step" 1 (.tuple [v₁, v₂])) :
    ∃ z is js, v₁ = cfgV z is ∧ v₂ = cfgV z js ∧ TypedSome env adminsT (.list is) ∧
      TypedSome env adminsT (.list js) ∧ SRead env (cfgV z is) js := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body h₀ hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := .varT "state" []) hq (.head _)
  obtain ⟨is, fi, ti⟩ :=
    quant_list (x := "admininstr*") (t := .varT "admininstr" []) hq (.tail _ (.head _))
  obtain ⟨js, fj, tj⟩ :=
    quant_list (x := "admininstr'*") (t := .varT "admininstr" []) hq (.tail _ (.tail _ (.head _)))
  have ei : EvalExp env _ (iterPat "admininstr" "admininstr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ej : EvalExp env _ (iterPat "admininstr'" "admininstr'*") (.list js) :=
    evalExp_iterPat (by decide) fj
  have ez := evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei)
  have hc : Value.tuple [v₁, v₂] = .tuple [cfgV z is, cfgV z js] :=
    EvalExp.unique he (evalExp_tup2 ez (evalExp_case (evalExp_tup2 (evalExp_var fz) ej)))
  have hd : SRead env (cfgV z is) js := rulePrem_nil (hp _ (.head _)) (evalExp_tup2 ez ej)
  exact ⟨z, is, js, (tuple2_inj hc).1, (tuple2_inj hc).2, ⟨_, valsOnly_bindVals σ, ti⟩,
    ⟨_, valsOnly_bindVals σ, tj⟩, hd⟩

/-- `Step/ctxt-label`, read back. -/
theorem inv_ctxtLabel10 (h₀ : HasRuleAt env "Step" "%~>%" 2 ctxtLabelRule10) {v₁ v₂ : Value}
    (hf : Fires env "Step" 2 (.tuple [v₁, v₂])) :
    ∃ z z' n cont is is',
      v₁ = cfgV z [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is])] ∧
      v₂ = cfgV z' [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is'])] ∧
      SStep env (cfgV z is) (cfgV z' is') := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body h₀ hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := .varT "state" []) hq (.head _)
  obtain ⟨n, fn, -⟩ := quant_of (x := "n") (t := .varT "n" []) hq (.tail _ (.head _))
  obtain ⟨cont, fc, -⟩ :=
    quant_list (x := "instr_0*") (t := .varT "instr" []) hq (.tail _ (.tail _ (.head _)))
  obtain ⟨is, fi, -⟩ := quant_list (x := "admininstr*") (t := .varT "admininstr" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨z', fz', -⟩ :=
    quant_of (x := "z'") (t := .varT "state" []) hq (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨is', fi', -⟩ := quant_list (x := "admininstr'*") (t := .varT "admininstr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have ec : EvalExp env _ (iterPat "instr_0" "instr_0*") (.list cont) :=
    evalExp_iterPat (by decide) fc
  have ei : EvalExp env _ (iterPat "admininstr" "admininstr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ei' : EvalExp env _ (iterPat "admininstr'" "admininstr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have hc : Value.tuple [v₁, v₂] =
      .tuple [cfgV z [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is])],
        cfgV z' [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is'])]] :=
    EvalExp.unique he (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) ec ei)))))
      (evalExp_case (evalExp_tup2 (evalExp_var fz')
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) ec ei'))))))
  have hs : SStep env (cfgV z is) (cfgV z' is') := rulePrem_nil (hp _ (.head _))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (evalExp_tup2 (evalExp_var fz') ei')))
  exact ⟨z, z', n, cont, is, is', (tuple2_inj hc).1, (tuple2_inj hc).2, hs⟩

/-- `Step/ctxt-frame`, read back: the inner frame goes from `fr` to `fr'`. -/
theorem inv_ctxtFrame10 (h₀ : HasRuleAt env "Step" "%~>%" 3 ctxtFrameRule10) {v₁ v₂ : Value}
    (hf : Fires env "Step" 3 (.tuple [v₁, v₂])) :
    ∃ s s' f fr fr' n is is',
      v₁ = cfgV (stV s f) [.case "FRAME_%{%}%" (.tuple [n, fr, .list is])] ∧
      v₂ = cfgV (stV s' f) [.case "FRAME_%{%}%" (.tuple [n, fr', .list is'])] ∧
      SStep env (cfgV (stV s fr) is) (cfgV (stV s' fr') is') := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body h₀ hf)
  obtain ⟨s, fs, -⟩ := quant_of (x := "s") (t := .varT "store" []) hq (.head _)
  obtain ⟨f, ff, -⟩ := quant_of (x := "f") (t := .varT "frame" []) hq (.tail _ (.head _))
  obtain ⟨n, fn, -⟩ := quant_of (x := "n") (t := .varT "n" []) hq (.tail _ (.tail _ (.head _)))
  have qfr : ∃ v, (VarEnv.empty.bindVals σ).findVal? "f'" = some v ∧
      HasTyp env (VarEnv.empty.bindVals σ) (.varT "frame" []) v :=
    quant_of hq (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨fr, ffr, -⟩ := qfr
  obtain ⟨is, fi, -⟩ := quant_list (x := "admininstr*") (t := .varT "admininstr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨s', fs', -⟩ := quant_of (x := "s'") (t := .varT "store" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  obtain ⟨fr', ffr', -⟩ := quant_of (x := "f''") (t := .varT "frame" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  obtain ⟨is', fi', -⟩ := quant_list (x := "admininstr'*") (t := .varT "admininstr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
  have ei : EvalExp env _ (iterPat "admininstr" "admininstr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ei' : EvalExp env _ (iterPat "admininstr'" "admininstr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have hc : Value.tuple [v₁, v₂] =
      .tuple [cfgV (stV s f) [.case "FRAME_%{%}%" (.tuple [n, fr, .list is])],
        cfgV (stV s' f) [.case "FRAME_%{%}%" (.tuple [n, fr', .list is'])]] :=
    EvalExp.unique he (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ff)))
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr) ei)))))
      (evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ff)))
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr') ei'))))))
  have hs : SStep env (cfgV (stV s fr) is) (cfgV (stV s' fr') is') := rulePrem_nil (hp _ (.head _))
    (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ffr)))
        ei))
      (evalExp_case (evalExp_tup2
        (evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ffr'))) ei')))
  exact ⟨s, s', f, fr, fr', n, is, is', (tuple2_inj hc).1, (tuple2_inj hc).2, hs⟩

/-- What `Step/ctxt-instrs` says, read back. -/
def CtxtInstrsInv10 (env : Env) (v₁ v₂ : Value) : Prop :=
  ∃ z z' vs is is' rest, (∃ ρ, ValsOnly ρ ∧ HasTyp env ρ valsT (.list vs)) ∧
    (vs ≠ [] ∨ rest ≠ []) ∧ v₁ = cfgV z (vs ++ is ++ rest) ∧ v₂ = cfgV z' (vs ++ is' ++ rest) ∧
    SStep env (cfgV z is) (cfgV z' is')

/-- `Step/ctxt-instrs`, read back, for every split. -/
theorem inv_ctxtInstrs10 (h₀ : HasRuleAt env "Step" "%~>%" 4 ctxtInstrsRule10) {v₁ v₂ : Value}
    (hf : Fires env "Step" 4 (.tuple [v₁, v₂])) : CtxtInstrsInv10 env v₁ v₂ := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body h₀ hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := .varT "state" []) hq (.head _)
  obtain ⟨vs, fv, tv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq (.tail _ (.head _))
  obtain ⟨is, fi, -⟩ :=
    quant_list (x := "admininstr*") (t := .varT "admininstr" []) hq (.tail _ (.tail _ (.head _)))
  obtain ⟨rest, fr, -⟩ := quant_list (x := "admininstr_1*") (t := .varT "admininstr" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨z', fz', -⟩ :=
    quant_of (x := "z'") (t := .varT "state" []) hq (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨is', fi', -⟩ := quant_list (x := "admininstr'*") (t := .varT "admininstr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have ev : EvalExp env _ valsE10 (.list vs) := evalExp_subIterPat (by decide) fv
  have ev' : EvalExp env _ (iterPat "val" "val*") (.list vs) := evalExp_iterPat (by decide) fv
  have ei : EvalExp env _ (iterPat "admininstr" "admininstr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ei' : EvalExp env _ (iterPat "admininstr'" "admininstr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have er : EvalExp env _ (iterPat "admininstr_1" "admininstr_1*") (.list rest) :=
    evalExp_iterPat (by decide) fr
  have hc : Value.tuple [v₁, v₂] =
      .tuple [cfgV z (vs ++ (is ++ rest)), cfgV z' (vs ++ (is' ++ rest))] :=
    EvalExp.unique he (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_cat ev (evalExp_cat ei er))))
      (evalExp_case (evalExp_tup2 (evalExp_var fz') (evalExp_cat ev (evalExp_cat ei' er)))))
  have hs : SStep env (cfgV z is) (cfgV z' is') := rulePrem_nil (hp _ (.head _))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (evalExp_tup2 (evalExp_var fz') ei')))
  have hb : Value.bool (decide (vs ≠ [] ∨ rest ≠ [])) = .bool true :=
    ifPrem_true (hp _ (.tail _ (.head _))) (evalExp_or (evalExp_ne_nil ev') (evalExp_ne_nil er))
  have hne : vs ≠ [] ∨ rest ≠ [] := of_decide_eq_true (Value.bool.inj hb)
  have h₁ : v₁ = cfgV z (vs ++ is ++ rest) := by rw [List.append_assoc]; exact (tuple2_inj hc).1
  have h₂ : v₂ = cfgV z' (vs ++ is' ++ rest) := by rw [List.append_assoc]; exact (tuple2_inj hc).2
  exact ⟨z, z', vs, is, is', rest, ⟨_, valsOnly_bindVals σ, tv⟩, hne, h₁, h₂, hs⟩

end Invert

/-! ## Decoding images -/

/-- No V1 instruction is encoded with `LABEL_` or `FRAME_`. -/
theorem instrToV_head10 (i : V1.Instr) : ∃ op x, instrToV i = .case op x ∧
    op ≠ "LABEL_%{%}%" ∧ op ≠ "FRAME_%{%}%" := by
  cases i <;> exact ⟨_, _, rfl, by decide, by decide⟩

/-- An image headed `LABEL_` is a label. -/
theorem adminToV_label_inv10 {a : Admin} {x : Value} (h : adminToV a = .case "LABEL_%{%}%" x) :
    ∃ n cont body, a = .label n cont body := by
  cases a with
  | source i =>
    obtain ⟨op, y, hy, hne, -⟩ := instrToV_head10 i
    have h' : instrToV i = .case "LABEL_%{%}%" x := h
    rw [hy] at h'
    exact absurd (Value.case.inj h').1 hne
  | label n cont body => exact ⟨n, cont, body, rfl⟩
  | _ => simp [adminToV, Silmaril.SpecTec.Equiv.Execution.caseNilV] at h

/-- An image headed `FRAME_` is a frame. -/
theorem adminToV_frame_inv10 {a : Admin} {x : Value} (h : adminToV a = .case "FRAME_%{%}%" x) :
    ∃ n fi body, a = .frame n fi body := by
  cases a with
  | source i =>
    obtain ⟨op, y, hy, -, hne⟩ := instrToV_head10 i
    have h' : instrToV i = .case "FRAME_%{%}%" x := h
    rw [hy] at h'
    exact absurd (Value.case.inj h').1 hne
  | frame n fi body => exact ⟨n, fi, body, rfl⟩
  | _ => simp [adminToV, Silmaril.SpecTec.Equiv.Execution.caseNilV] at h

/-- `adminsToV` is a `map`. -/
theorem adminsToV_map10 : ∀ l : List Admin, adminsToV l = l.map adminToV
  | [] => rfl
  | a :: l => by
    show adminToV a :: adminsToV l = _
    rw [adminsToV_map10 l]
    rfl

/-- An image that is a one-element list comes from a one-element list. -/
theorem adminsToV_eq_single10 {l : List Admin} {v : Value} (h : adminsToV l = [v]) :
    ∃ a, l = [a] ∧ adminToV a = v := by
  rw [adminsToV_map10] at h
  match l, h with
  | [a], h => exact ⟨a, rfl, by simpa using h⟩

/-- An image split in three comes from code split in three. -/
theorem adminsToV_eq_append3 {l : List Admin} {xs ys zs : List Value}
    (h : adminsToV l = xs ++ ys ++ zs) :
    ∃ l₁ l₂ l₃, l = l₁ ++ l₂ ++ l₃ ∧ adminsToV l₁ = xs ∧ adminsToV l₂ = ys ∧ adminsToV l₃ = zs := by
  rw [adminsToV_map10] at h
  obtain ⟨m, l₃, rfl, hm, h₃⟩ := List.map_eq_append_iff.1 h
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.1 hm
  exact ⟨l₁, l₂, l₃, rfl, by rw [adminsToV_map10, h₁], by rw [adminsToV_map10, h₂],
    by rw [adminsToV_map10, h₃]⟩

variable {H : Type}

/-- The image of a configuration, as `cfgV`. -/
theorem configV_eq10 (hn : H → String) (c : Config H) :
    configV hn c = cfgV (stV (storeV hn c.store) (frameV c.frame)) (adminsToV c.code) := rfl

/-- Reading `configV` against a `cfgV`. -/
theorem configV_cfgV10 {hn : H → String} {c : Config H} {z : Value} {is : List Value}
    (h : configV hn c = cfgV z is) :
    z = stV (storeV hn c.store) (frameV c.frame) ∧ is = adminsToV c.code := by
  have h' := cfgV_inj h
  exact ⟨h'.1.symm, h'.2.symm⟩

/-! ## Typed values are V1 values -/

/-- The constructors of 1.0's `val`: `CONST` only. -/
theorem findTyp_val10 (B : Builtins) : ∃ cs, (simEnv10 B).findTyp? "val" =
    some ([], [.instD [] [] (.variantT cs)]) ∧
    cs.map (fun c : TypCase => match c with | .mk o _ _ _ => o) = ["CONST"] :=
  ⟨_, rfl, rfl⟩

/-- **A typed 1.0 `val` is headed `CONST`.** -/
theorem const_of_typed10 {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {v : Value}
    (h : HasTyp (simEnv10 B) ρ (.varT "val" []) v) : ∃ w, v = .case "CONST" w := by
  have hl : localTyp? ρ "val" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  obtain ⟨cs, hcs, hheads⟩ := findTyp_val10 B
  rw [hcs] at htd
  obtain rfl := (Option.some.inj htd).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, -, hd⟩ | hrest
  · obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
    obtain ⟨t, qs, prems, hm, -⟩ := hasTypCase_mem hc
    have hmem := List.mem_map_of_mem (f := fun c : TypCase => match c with | .mk o _ _ _ => o) hm
    rw [hheads] at hmem
    obtain rfl := List.mem_singleton.1 hmem
    exact ⟨w, rfl⟩
  · exact absurd hrest not_hasTypInsts_nil

/-- An image headed `CONST` is a V1 value. -/
theorem admin_of_const10 {a : Admin} {w : Value} (h : adminToV a = .case "CONST" w) :
    ∃ v, a = value v := by
  cases a with
  | source i =>
    cases i
    case intConst t b => exact ⟨⟨.int t, b⟩, rfl⟩
    case floatConst t b => exact ⟨⟨.float t, b⟩, rfl⟩
    all_goals simp [adminToV, instrToV, Silmaril.SpecTec.Equiv.Execution.caseNilV] at h
  | _ => simp [adminToV, Silmaril.SpecTec.Equiv.Execution.caseNilV] at h

/-- Code whose elements are values is a sequence of values. -/
theorem values_of_all : ∀ {l : List Admin}, (∀ a ∈ l, ∃ v, a = value v) → ∃ us, l = values us
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨v, rfl⟩ := h a (.head _)
    obtain ⟨us, rfl⟩ := values_of_all (fun b hb => h b (.tail _ hb))
    exact ⟨v :: us, rfl⟩

/-- **Code whose image is a typed `val*` is a sequence of V1 values.** -/
theorem values_of_typed10 {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) :
    ∀ {l : List Admin}, HasTyp (simEnv10 B) ρ valsT (.list (adminsToV l)) →
      ∃ us, l = values us := by
  intro l h
  obtain ⟨vs, hvs, hl⟩ := hasTyp_iterT_list_iff.1 h
  obtain rfl := (Value.list.inj hvs).symm
  have hall : ∀ a ∈ l, ∃ v, a = value v := by
    intro a ha
    have hm : adminToV a ∈ adminsToV l := by rw [adminsToV_map10]; exact List.mem_map_of_mem ha
    obtain ⟨w, hw⟩ := const_of_typed10 hρ (hasTypList_iff.1 hl _ hm)
    exact admin_of_const10 hw
  exact values_of_all hall

/-- The image of V1 values. -/
theorem adminsToV_values (us : List Execution.Runtime.Value) :
    adminsToV (values us) = us.map valV := by
  rw [adminsToV_map10, V1.Execution.values, List.map_map]
  congr 1
  funext v
  rcases v with ⟨⟨_⟩ | ⟨_⟩, _⟩ <;> rfl

/-! ## The size of active code -/

mutual
/-- The number of administrative instructions in `a`, at any depth of labels and frames. -/
def adminSize10 : Admin → Nat
  | .label _ _ b => codeSize10 b + 1
  | .frame _ _ b => codeSize10 b + 1
  | _ => 1

/-- `adminSize10`, summed over a sequence. -/
def codeSize10 : List Admin → Nat
  | [] => 0
  | a :: l => adminSize10 a + codeSize10 l
end

theorem adminSize10_pos (a : Admin) : 0 < adminSize10 a := by
  cases a <;> simp [adminSize10]

theorem codeSize10_append : ∀ (l₁ l₂ : List Admin),
    codeSize10 (l₁ ++ l₂) = codeSize10 l₁ + codeSize10 l₂
  | [], l₂ => by simp [codeSize10]
  | a :: l₁, l₂ => by
    simp only [List.cons_append, codeSize10, codeSize10_append l₁ l₂]
    omega

theorem codeSize10_pos {l : List Admin} (h : l ≠ []) : 0 < codeSize10 l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => have := adminSize10_pos a; simp only [codeSize10]; omega

/-- The middle of a split with a non-empty side is smaller. -/
theorem codeSize10_infix {l₁ l l₂ : List Admin} (h : l₁ ≠ [] ∨ l₂ ≠ []) :
    codeSize10 l < codeSize10 (l₁ ++ l ++ l₂) := by
  rw [codeSize10_append, codeSize10_append]
  rcases h with h | h
  · have := codeSize10_pos h; omega
  · have := codeSize10_pos h; omega

theorem codeSize10_label (n : Nat) (cont : V1.Expr) (b : List Admin) :
    codeSize10 b < codeSize10 [.label n cont b] := by
  simp [codeSize10, adminSize10]

theorem codeSize10_frame (n : Nat) (f : Frame) (b : List Admin) :
    codeSize10 b < codeSize10 [.frame n f b] := by
  simp [codeSize10, adminSize10]

/-! ## The per-rule obligations, and the recursion -/

/-- A predicate on configurations that passes to the body of a label (in the same state), the body
of a frame (in that frame), and any infix of the code. -/
structure CfgInv10 (G : Config H → Prop) : Prop where
  label : ∀ s f n cont body, G ⟨s, f, [.label n cont body]⟩ → G ⟨s, f, body⟩
  frame : ∀ s f n fi body, G ⟨s, f, [.frame n fi body]⟩ → G ⟨s, fi, body⟩
  mid : ∀ s f l₁ l l₂, G ⟨s, f, l₁ ++ l ++ l₂⟩ → G ⟨s, f, l⟩

/-- **The per-rule obligations of the 1.0 backward half**, at configurations satisfying `G`: every
firing of a `Step_pure` rule, of a `Step_read` rule, and of a `Step` rule other than the five
structural ones, at the image of V1 code or a V1 configuration, is the image of a V1 step. -/
structure BwdParts10 (G : Config H → Prop) (B : Builtins) (hn : H → String)
    (host : HostSemantics H) : Prop where
  /-- `Step_pure`. -/
  pure : ∀ (i : Nat) (c : Config H) (w : List Value), G c →
    TypedSome (simEnv10 B) adminsT (.list (adminsToV c.code)) →
    TypedSome (simEnv10 B) adminsT (.list w) →
    Fires (simEnv10 B) "Step_pure" i (.tuple [.list (adminsToV c.code), .list w]) →
    ∃ code', w = adminsToV code' ∧ PureStep c.code code'
  /-- `Step_read`: a V1 step that keeps the state. -/
  read : ∀ (i : Nat) (c : Config H) (w : List Value), G c →
    TypedSome (simEnv10 B) adminsT (.list (adminsToV c.code)) →
    TypedSome (simEnv10 B) adminsT (.list w) →
    Fires (simEnv10 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩
  /-- The `Step` rules from `local.set` on. -/
  step : ∀ (i : Nat), 5 ≤ i → ∀ (c : Config H) (w : Value), G c →
    Fires (simEnv10 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step host c c'

section Rec

variable {G : Config H → Prop} {B : Builtins} {hn : H → String} {host : HostSemantics H}

/-- The backward conclusion at `c`. -/
def BwdAt10 (hn : H → String) (host : HostSemantics H) (c : Config H) (w : Value) : Prop :=
  ∃ c', w = configV hn c' ∧ Step host c c'

/-- The induction hypothesis: the backward conclusion for code smaller than `n`. -/
def IH10 (G : Config H → Prop) (B : Builtins) (hn : H → String) (host : HostSemantics H)
    (n : Nat) : Prop :=
  ∀ (c : Config H) (w : Value), G c → codeSize10 c.code < n →
    SStep (simEnv10 B) (configV hn c) w → BwdAt10 hn host c w

/-- `Step/pure` backwards. -/
theorem bwd_pure10 (Bk : BwdParts10 G B hn host) {c : Config H} {w : Value} (hg : G c)
    (hf : Fires (simEnv10 B) "Step" 0 (.tuple [configV hn c, w])) : BwdAt10 hn host c w := by
  obtain ⟨z, is, js, h₁, h₂, ti, tj, hp⟩ := inv_pure10 (hasRuleAt_pure10 B) hf
  obtain ⟨t, rules, hrel⟩ := findRel_pure10 B
  have e₁ := configV_cfgV10 h₁
  obtain ⟨i, hi⟩ := (dderives_iff_fires hrel).1 hp
  rw [e₁.2] at ti hi
  obtain ⟨code', rfl, hst⟩ := Bk.pure i c js hg ti tj hi
  exact ⟨⟨c.store, c.frame, code'⟩, by rw [h₂, e₁.1]; rfl, .pure _ _ hst⟩

/-- `Step/read` backwards. -/
theorem bwd_read10 (Bk : BwdParts10 G B hn host) {c : Config H} {w : Value} (hg : G c)
    (hf : Fires (simEnv10 B) "Step" 1 (.tuple [configV hn c, w])) : BwdAt10 hn host c w := by
  obtain ⟨z, is, js, h₁, h₂, ti, tj, hp⟩ := inv_read10 (hasRuleAt_read10 B) hf
  obtain ⟨t, rules, hrel⟩ := findRel_read10 B
  have e₁ := configV_cfgV10 h₁
  obtain ⟨i, hi⟩ := (dderives_iff_fires hrel).1 hp
  rw [← h₁] at hi
  rw [e₁.2] at ti
  obtain ⟨code', rfl, hst⟩ := Bk.read i c js hg ti tj hi
  exact ⟨⟨c.store, c.frame, code'⟩, by rw [h₂, e₁.1]; rfl, hst⟩

/-- `Step/ctxt-label` backwards. -/
theorem bwd_ctxtLabel10 (I : CfgInv10 G) {n : Nat} (ih : IH10 G B hn host n) {s : Store H}
    {f : Frame} {code : List Admin} {w : Value} (hg : G ⟨s, f, code⟩)
    (hlt : codeSize10 code < n + 1)
    (hf : Fires (simEnv10 B) "Step" 2 (.tuple [configV hn ⟨s, f, code⟩, w])) :
    BwdAt10 hn host ⟨s, f, code⟩ w := by
  obtain ⟨z, z', m, cont, is, is', h₁, h₂, hs⟩ := inv_ctxtLabel10 (hasRuleAt_ctxtLabel10 B) hf
  have e₁ := configV_cfgV10 h₁
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single10 e₁.2.symm
  obtain ⟨k, cont₀, body, rfl⟩ := adminToV_label_inv10 ha
  have hp : Value.num (.natN k) = m ∧ instrsToV cont₀ = cont ∧ adminsToV body = is := by
    simpa only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have e₂ : cfgV z is = configV hn ⟨s, f, body⟩ := by rw [configV_eq10, e₁.1, hp.2.2]
  obtain ⟨⟨s₂, f₂, K⟩, hw, hst⟩ :=
    ih _ _ (I.label _ _ _ _ _ hg)
      (Nat.lt_of_lt_of_le (codeSize10_label k cont₀ body) (Nat.le_of_lt_succ hlt)) (e₂ ▸ hs)
  have e₃ := cfgV_inj (hw.trans (configV_eq10 hn _))
  refine ⟨⟨s₂, f₂, [.label k cont₀ K]⟩, ?_, .label hst k cont₀⟩
  rw [h₂, e₃.1, e₃.2, ← hp.1, ← hp.2.1]
  rfl

/-- `Step/ctxt-frame` backwards. -/
theorem bwd_ctxtFrame10 (I : CfgInv10 G) {n : Nat} (ih : IH10 G B hn host n) {s : Store H}
    {f : Frame} {code : List Admin} {w : Value} (hg : G ⟨s, f, code⟩)
    (hlt : codeSize10 code < n + 1)
    (hf : Fires (simEnv10 B) "Step" 3 (.tuple [configV hn ⟨s, f, code⟩, w])) :
    BwdAt10 hn host ⟨s, f, code⟩ w := by
  obtain ⟨sv, sv', fv, fr, fr', m, is, is', h₁, h₂, hs⟩ :=
    inv_ctxtFrame10 (hasRuleAt_ctxtFrame10 B) hf
  have e₁ := configV_cfgV10 h₁
  have e₀ : sv = storeV hn s ∧ fv = frameV f := stV_inj e₁.1
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single10 e₁.2.symm
  obtain ⟨k, fi, body, rfl⟩ := adminToV_frame_inv10 ha
  have hp : Value.num (.natN k) = m ∧ frameV fi = fr ∧ adminsToV body = is := by
    simpa only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have e₂ : cfgV (stV sv fr) is = configV hn ⟨s, fi, body⟩ := by
    rw [configV_eq10, e₀.1, ← hp.2.1, hp.2.2]
  obtain ⟨⟨s₂, f₂, K⟩, hw, hst⟩ :=
    ih _ _ (I.frame _ _ _ _ _ hg)
      (Nat.lt_of_lt_of_le (codeSize10_frame k fi body) (Nat.le_of_lt_succ hlt)) (e₂ ▸ hs)
  have e₃ := cfgV_inj (hw.trans (configV_eq10 hn _))
  have e₄ : sv' = storeV hn s₂ ∧ fr' = frameV f₂ := stV_inj e₃.1
  refine ⟨⟨s₂, f, [.frame k f₂ K]⟩, ?_, .frame hst k f⟩
  rw [h₂, e₄.1, e₃.2, e₀.2, ← hp.1, e₄.2]
  rfl

/-- `Step/ctxt-instrs` backwards: V1's `context`. -/
theorem bwd_ctxtInstrs10 (I : CfgInv10 G) {n : Nat} (ih : IH10 G B hn host n) {s : Store H}
    {f : Frame} {code : List Admin} {w : Value} (hg : G ⟨s, f, code⟩)
    (hlt : codeSize10 code < n + 1)
    (hf : Fires (simEnv10 B) "Step" 4 (.tuple [configV hn ⟨s, f, code⟩, w])) :
    BwdAt10 hn host ⟨s, f, code⟩ w := by
  obtain ⟨z, z', vs, is, is', rest, ⟨ρ, hρ, tv⟩, hne, h₁, h₂, hs⟩ :=
    inv_ctxtInstrs10 (hasRuleAt_ctxtInstrs10 B) hf
  have e₁ := configV_cfgV10 h₁
  obtain ⟨l₁, l₂, l₃, rfl, hl₁, hl₂, hl₃⟩ := adminsToV_eq_append3 e₁.2.symm
  rw [← hl₁] at tv
  obtain ⟨us, rfl⟩ := values_of_typed10 hρ tv
  have hne' : values us ≠ [] ∨ l₃ ≠ [] := by
    rcases hne with h | h
    · left; rintro he; rw [he] at hl₁; exact h hl₁.symm
    · right; rintro he; rw [he] at hl₃; exact h hl₃.symm
  have e₂ : cfgV z is = configV hn ⟨s, f, l₂⟩ := by rw [configV_eq10, e₁.1, hl₂]
  obtain ⟨⟨s₂, f₂, K⟩, hw, hst⟩ :=
    ih _ _ (I.mid _ _ _ _ _ hg)
      (Nat.lt_of_lt_of_le (codeSize10_infix hne') (Nat.le_of_lt_succ hlt)) (e₂ ▸ hs)
  have e₃ := cfgV_inj (hw.trans (configV_eq10 hn _))
  refine ⟨⟨s₂, f₂, values us ++ K ++ l₃⟩, ?_, .context hst us l₃⟩
  rw [h₂, e₃.1, e₃.2, ← hl₁, ← hl₃, configV_eq10]
  simp only [adminsToV_map10, List.map_append]

/-- No `Step` rule fires beyond the 13 of 1.0, so the dispatch below is total. -/
theorem bwd_all10 (Bk : BwdParts10 G B hn host) (I : CfgInv10 G) : ∀ n, IH10 G B hn host n
  | 0 => fun _ _ _ h => absurd h (Nat.not_lt_zero _)
  | n + 1 => fun ⟨s, f, code⟩ w hg hlt hs => by
    obtain ⟨t, rules, hrel⟩ := findRel_step10 B
    obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
    match i, hf with
    | 0, hf => exact bwd_pure10 Bk hg hf
    | 1, hf => exact bwd_read10 Bk hg hf
    | 2, hf => exact bwd_ctxtLabel10 I (bwd_all10 Bk I n) hg hlt hf
    | 3, hf => exact bwd_ctxtFrame10 I (bwd_all10 Bk I n) hg hlt hf
    | 4, hf => exact bwd_ctxtInstrs10 I (bwd_all10 Bk I n) hg hlt hf
    | k + 5, hf => exact Bk.step (k + 5) (by omega) _ w hg hf

end Rec

/-- **The 1.0 backward half under `G`, from the per-rule obligations under `G`.** -/
theorem backward10_of_parts {G : Config H → Prop} {B : Builtins} {hn : H → String}
    {host : HostSemantics H} (Bk : BwdParts10 G B hn host) (I : CfgInv10 G)
    (c : Config H) (w : Value) (hg : G c) (hs : SStepB (simEnv10 B) (configV hn c) w) :
    ∃ c', w = configV hn c' ∧ Step host c c' :=
  bwd_all10 Bk I (codeSize10 c.code + 1) c w hg (Nat.lt_succ_self _) ((sstepB10_iff B).1 hs)

end Silmaril.Wasm.SpecTec.Sim10.Whole
