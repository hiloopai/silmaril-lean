module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.TyElim.Rules
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.TyElim.Img
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.TyElim.Calls
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.RefOkV.Assemble

/-!
# Round 6: inverting the validation rules down to `Rectype_ok2`

* `reftypeOk_heap`: `Reftype_ok` at `REF null? ht` holds only from `Heaptype_ok` at `ht`;
* `heaptypeOk_def`: `Heaptype_ok` at a defined type holds only from `Typeuse_ok`, which holds
  only from `Deftype_ok` (`typeuseOk_def`);
* `deftypeOk_inv`: `Deftype_ok` at `_DEF (REC subtype*) i` in `ctxR L` holds only from
  `Rectype_ok2` at the group, in `ctxR (subtype* ++ L)` (SpecTec's `{RECS subtype*} ⊕ C`);
* `rectypeOk2_get`: `Rectype_ok2` gives `Subtype_ok2` at every member, at its position.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.TyElim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_inj natV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Round6.Reading
open Round6.RefOkB (ctxR)

variable {B : Builtins}

/-! ## Evaluation, inverted -/

theorem ev2 {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {a b : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂]) (.tuple [a, b])) :
    EvalExp env ρ e₁ a ∧ EvalExp env ρ e₂ b := by
  obtain ⟨a', b', he, h₁, h₂⟩ := RefOkV.evalExp_tup2_inv h
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨h₁, h₂⟩

theorem ev3 {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {a b c : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂, e₃]) (.tuple [a, b, c])) :
    EvalExp env ρ e₁ a ∧ EvalExp env ρ e₂ b ∧ EvalExp env ρ e₃ c := by
  obtain ⟨a', b', c', he, h₁, h₂, h₃⟩ := RefOkV.evalExp_tup3_ex h
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  exact ⟨h₁, h₂, h₃⟩

theorem evCase {env : Env} {ρ : VarEnv} {op op' : MixopS} {e : Exp} {w : Value}
    (h : EvalExp env ρ (.caseE op e) (.case op' w)) : op = op' ∧ EvalExp env ρ e w := by
  obtain ⟨w', hw, he⟩ := evalExp_caseE_iff.1 h
  simp only [Value.case.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨rfl, hw⟩

/-- A relational premise, inverted. -/
theorem prem_rule {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {x : IL.Id} {op : MixopS}
    {e : Exp} (h : DPremB env O els ρ (.rulePr x [] op e)) :
    ∃ v, EvalExp env ρ e v ∧ DDerivesB env O x op [] v := by
  cases h with
  | rulePr ha he hd =>
    obtain rfl := Equiv.Validation.evalArgs_nil_iff.1 ha
    exact ⟨_, he, hd⟩

/-- A relational premise on `(C, x)`, at known values. -/
theorem prem_rule2 {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {r : IL.Id} {op : MixopS}
    {x y : IL.Id} {a b : Value} (hx : ρ.findVal? x = some a) (hy : ρ.findVal? y = some b)
    (h : DPremB env O els ρ (.rulePr r [] op (.tupE [.varE x, .varE y]))) :
    DDerivesB env O r op [] (.tuple [a, b]) := by
  obtain ⟨v, hv, hd⟩ := prem_rule h
  rwa [hv.unique (evalExp_tup2 (evalExp_var hx) (evalExp_var hy))] at hd

/-- A relational premise on `(C, x, y)`, at known values. -/
theorem prem_rule3 {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {r : IL.Id} {op : MixopS}
    {x y z : IL.Id} {a b c : Value} (hx : ρ.findVal? x = some a) (hy : ρ.findVal? y = some b)
    (hz : ρ.findVal? z = some c)
    (h : DPremB env O els ρ (.rulePr r [] op (.tupE [.varE x, .varE y, .varE z]))) :
    DDerivesB env O r op [] (.tuple [a, b, c]) := by
  obtain ⟨v, hv, hd⟩ := prem_rule h
  rwa [hv.unique (evalExp_tup3 (evalExp_var hx) (evalExp_var hy) (evalExp_var hz))] at hd

/-- A conclusion without an empty-domain option iteration is its only alternative. -/
theorem concl_eq {e e' : Exp} (halt : e' ∈ conclAlts e) (h : hasOptNil e = false) : e' = e :=
  List.mem_singleton.1 (conclAlts_of_not h ▸ halt)

/-- A two-component conclusion `(C, x)` with `x` read through `subE`, inverted. -/
theorem concl_C2sub {env : Env} {ρ : VarEnv} {x : IL.Id} {t₁ t₂ : Typ} {c a : Value}
    (he : EvalExp env ρ (.tupE [.varE "C", .subE (.varE x) t₁ t₂]) (.tuple [c, a])) :
    ρ.findVal? "C" = some c ∧ ρ.findVal? x = some a :=
  have h := ev2 he
  ⟨evalExp_varE_iff.1 h.1, evalExp_varE_iff.1 (evalExp_subE_iff.1 h.2)⟩

/-! ## `Reftype_ok` -/

theorem ev_refConcl {env : Env} {ρ : VarEnv} {X : Exp} {c a hv : Value}
    (h : EvalExp env ρ (.tupE [.varE "C", .caseE "REF" (.tupE [X, .varE "heaptype"])])
      (.tuple [c, .case "REF" (.tuple [a, hv])])) :
    ρ.findVal? "C" = some c ∧ ρ.findVal? "heaptype" = some hv := by
  obtain ⟨h₁, h₂⟩ := ev2 h
  obtain ⟨-, h₂⟩ := evCase h₂
  obtain ⟨-, h₃⟩ := ev2 h₂
  exact ⟨evalExp_varE_iff.1 h₁, evalExp_varE_iff.1 h₃⟩

/-- **`Reftype_ok` at `REF null? ht` holds only from `Heaptype_ok` at `ht`.** -/
theorem reftypeOk_heap {O : ElseI} {c a hv : Value}
    (hd : DDerivesB (simEnv B) O "Reftype_ok" "%|-%:OK" [] (.tuple [c, .case "REF" (.tuple [a, hv])])) :
    DDerivesB (simEnv B) O "Heaptype_ok" "%|-%:OK" [] (.tuple [c, hv]) := by
  obtain ⟨i, nm, qs, e, e', prems, σ, hr, halt, -, he, hp⟩ := dderivesB_inv findRel_reftypeOk hd
  rcases i with _ | i
  · simp only [reftypeOkRules, List.getElem?_cons_zero, Option.some.injEq, Rule.ruleD.injEq] at hr
    obtain ⟨rfl, rfl, -, rfl, rfl⟩ := hr
    simp [conclAlts, hasOptNil, hasOptNilL, optAlts, optAltsL, prod2] at halt
    obtain ⟨X, rfl⟩ : ∃ X, e' = .tupE [.varE "C", .caseE "REF" (.tupE [X, .varE "heaptype"])] := by
      rcases halt with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    obtain ⟨hC, hH⟩ := ev_refConcl he
    exact prem_rule2 hC hH (hp _ (List.mem_singleton_self _))
  · simp [reftypeOkRules] at hr

/-! ## `Heaptype_ok` and `Typeuse_ok` at a defined type -/

/-- A typed quantifier, read off `QuantsOk`. -/
theorem quant {env : Env} {σ : List (IL.Id × Value)} {qs : List Param} {x : IL.Id} {t : Typ}
    (hq : QuantsOk env (VarEnv.empty.bindVals σ) qs) (hm : Param.expP x t ∈ qs) :
    ∃ w, (VarEnv.empty.bindVals σ).findVal? x = some w ∧
      HasTyp env (VarEnv.empty.bindVals σ) t w := hq x t hm

/-- `Heaptype_ok/abs` does not hold at a defined type. -/
theorem heaptypeOk_abs {σ : List (IL.Id × Value)} {c : Value} {d : DefType}
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ)
      [.expP "C" (.varT "context" []), .expP "absheaptype" (.varT "absheaptype" [])])
    (he : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.tupE [.varE "C", .subE
      (.varE "absheaptype") (.varT "absheaptype" []) (.varT "heaptype" [])]) (.tuple [c, tyV d])) :
    False := by
  obtain ⟨g, k, rfl⟩ : ∃ g k, d = Ty.defn g k := by cases d; exact ⟨_, _, rfl⟩
  obtain ⟨w, hw, ht⟩ := quant hq (x := "absheaptype") (t := .varT "absheaptype" []) (by simp)
  have e : w = tyV (Ty.defn g k) := Option.some.inj (hw.symm.trans (concl_C2sub he).2)
  rcases abs_inv (Round5.Multi.hasE_of_valsOnly (valsOnly_bind σ) ht) with ⟨a, ha⟩ | ha
  · cases a <;> simp [e, tyV, Silmaril.SpecTec.Equiv.Validation.absV] at ha
  · simp [e, tyV] at ha

/-- `C ⊢ BOT : OK` is not at a defined type. -/
theorem not_evalExp_bot_def {env : Env} {ρ : VarEnv} {c : Value} {d : DefType}
    (he : EvalExp env ρ (.tupE [.varE "C", .caseE "BOT" (.tupE [])]) (.tuple [c, tyV d])) : False := by
  obtain ⟨g, k, rfl⟩ : ∃ g k, d = Ty.defn g k := by cases d; exact ⟨_, _, rfl⟩
  exact absurd (evCase (ev2 he).2).1 (by decide)

/-- **`Heaptype_ok` at a defined type holds only from `Typeuse_ok`.** -/
theorem heaptypeOk_def {O : ElseI} {c : Value} {d : DefType}
    (hd : DDerivesB (simEnv B) O "Heaptype_ok" "%|-%:OK" [] (.tuple [c, tyV d])) :
    DDerivesB (simEnv B) O "Typeuse_ok" "%|-%:OK" [] (.tuple [c, tyV d]) := by
  obtain ⟨i, nm, qs, e, e', prems, σ, hr, halt, hq, he, hp⟩ := dderivesB_inv findRel_heaptypeOk hd
  rcases i with _ | _ | _ | i
  all_goals simp only [heaptypeOkRules, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq, Rule.ruleD.injEq, List.getElem?_nil, reduceCtorEq] at hr
  all_goals obtain ⟨rfl, rfl, -, rfl, rfl⟩ := hr
  · exact (heaptypeOk_abs hq ((concl_eq halt rfl) ▸ he)).elim
  · have h := concl_C2sub ((concl_eq halt rfl) ▸ he)
    exact prem_rule2 h.1 h.2 (hp _ (List.mem_singleton_self _))
  · exact (not_evalExp_bot_def ((concl_eq halt rfl) ▸ he)).elim

/-- A conclusion `(C, op x)` is not at a defined type, for `op ≠ _DEF`. -/
theorem not_evalExp_case_def {env : Env} {ρ : VarEnv} {op : MixopS} {x : Exp} {c : Value}
    {d : DefType} (hop : op ≠ "_DEF")
    (he : EvalExp env ρ (.tupE [.varE "C", .caseE op x]) (.tuple [c, tyV d])) : False := by
  obtain ⟨g, k, rfl⟩ : ∃ g k, d = Ty.defn g k := by cases d; exact ⟨_, _, rfl⟩
  exact hop (evCase (ev2 he).2).1

/-- **`Typeuse_ok` at a defined type holds only from `Deftype_ok`.** -/
theorem typeuseOk_def {O : ElseI} {c : Value} {d : DefType}
    (hd : DDerivesB (simEnv B) O "Typeuse_ok" "%|-%:OK" [] (.tuple [c, tyV d])) :
    DDerivesB (simEnv B) O "Deftype_ok" "%|-%:OK" [] (.tuple [c, tyV d]) := by
  obtain ⟨i, nm, qs, e, e', prems, σ, hr, halt, -, he, hp⟩ := dderivesB_inv findRel_typeuseOk hd
  rcases i with _ | _ | _ | i
  all_goals simp only [typeuseOkRules, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq, Rule.ruleD.injEq, List.getElem?_nil, reduceCtorEq] at hr
  all_goals obtain ⟨rfl, rfl, -, rfl, rfl⟩ := hr
  · exact (not_evalExp_case_def (by decide) ((concl_eq halt rfl) ▸ he)).elim
  · exact (not_evalExp_case_def (by decide) ((concl_eq halt rfl) ▸ he)).elim
  · have h := concl_C2sub ((concl_eq halt rfl) ▸ he)
    exact prem_rule2 h.1 h.2 (hp _ (List.mem_singleton_self _))

/-! ## `Deftype_ok` -/

/-- One more field, evaluated. -/
theorem evalExpFields_cons' {env : Env} {ρ : VarEnv} {a : AtomS} {e : Exp} {v : Value}
    {fs : List ExpField} {gs : List (AtomS × Value)} (h : EvalExp env ρ e v)
    (hs : EvalExpFields env ρ fs gs) : EvalExpFields env ρ (.mk a e :: fs) ((a, v) :: gs) := by
  obtain ⟨n₁, h₁⟩ := h
  obtain ⟨n₂, h₂⟩ := hs
  obtain ⟨m, hm⟩ : ∃ m, n₂ = m + 1 := by
    cases n₂ with
    | zero => simp [evalExpFields] at h₂
    | succ m => exact ⟨m, rfl⟩
  subst hm
  refine ⟨max n₁ m + 1, ?_⟩
  have e₁ := evalExp_ok_of_le (Nat.le_max_left n₁ m) h₁
  have e₂ := evalExpFields_ok_of_le (m := m + 1) (n := max n₁ m + 1) (by omega) h₂
  simp only [evalExpFields, List.mapM_cons] at e₂ ⊢
  simp [e₁, e₂]

/-- No fields. -/
theorem evalExpFields_nil' {env : Env} {ρ : VarEnv} : EvalExpFields env ρ [] [] :=
  ⟨1, by simp [evalExpFields]; rfl⟩

theorem evListNil {env : Env} {ρ : VarEnv} : EvalExp env ρ (.listE []) (.list []) :=
  evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩

/-- **`{RECS subtype*} ⊕ C` is `ctxR (subtype* ++ L)`** in `C = ctxR L`. -/
theorem evalExp_recsCtx_of {ρ : VarEnv} {L vs : List Value}
    (hC : ρ.findVal? "C" = some (ctxR L))
    (hit : EvalExp (simEnv B) ρ (.iterE (.varE "subtype") RefOkB.subsNIt) (.list vs)) :
    EvalExp (simEnv B) ρ RefOkB.recsCtxE (ctxR (vs ++ L)) := by
  have hf := evalExpFields_cons' (a := "TYPES") evListNil <|
    evalExpFields_cons' (a := "TAGS") evListNil <| evalExpFields_cons' (a := "GLOBALS") evListNil <|
    evalExpFields_cons' (a := "MEMS") evListNil <| evalExpFields_cons' (a := "TABLES") evListNil <|
    evalExpFields_cons' (a := "FUNCS") evListNil <| evalExpFields_cons' (a := "DATAS") evListNil <|
    evalExpFields_cons' (a := "ELEMS") evListNil <| evalExpFields_cons' (a := "LOCALS") evListNil <|
    evalExpFields_cons' (a := "LABELS") evListNil <|
    evalExpFields_cons' (a := "RETURN") (evalExp_optE_none_iff.2 rfl) <|
    evalExpFields_cons' (a := "REFS") evListNil <|
    evalExpFields_cons' (a := "RECS") hit evalExpFields_nil'
  exact evalExp_compE_iff.2 ⟨_, _, evalExp_strE_iff.2 ⟨_, hf, rfl⟩, evalExp_var hC,
    by simp [Value.comp?, Value.compFields?, ctxR]⟩

/-- The image of a group. -/
theorem tyV_group (subs : Ty (.list .sub)) :
    tyV (Ty.group subs) = .case "REC" (.case "%" (.tuple [.list (subs.toList.map tyV)])) := by
  rw [← Equiv.Validation.tyV_list]; rfl

/-- `REC (% e)`, evaluated at `REC (% x)`. -/
theorem pct1_inv {env : Env} {ρ : VarEnv} {e : Exp} {x : Value}
    (h : EvalExp env ρ (.caseE "REC" (.caseE "%" (.tupE [e]))) (.case "REC" (.case "%" (.tuple [x])))) :
    EvalExp env ρ e x := by
  obtain ⟨-, h₁⟩ := evCase h
  obtain ⟨-, h₂⟩ := evCase h₁
  obtain ⟨vs, hvs, he⟩ := evalExp_tupE_iff.1 h₂
  obtain ⟨y, rest, rfl, hy, hrest⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  have hnil : rest = [] := Equiv.Validation.evalExps_nil_iff.1 hrest
  have ey : x = y := by simpa [hnil] using he
  exact ey ▸ hy

/-- `rectype = REC subtype^n`, at a group's image: `subtype^n` is its members. -/
theorem rectypeEq_inv {env : Env} {ρ : VarEnv} {subs : Ty (.list .sub)}
    (hR : ρ.findVal? "rectype" = some (tyV (Ty.group subs)))
    (hc : EvalExp env ρ (.cmpE .eqOp .boolT (.varE "rectype") (.caseE "REC" (.caseE "%"
      (.tupE [.iterE (.varE "subtype") RefOkB.subsNIt])))) (.bool true)) :
    EvalExp env ρ (.iterE (.varE "subtype") RefOkB.subsNIt) (.list (subs.toList.map tyV)) := by
  obtain ⟨v₁, v₂, hv₁, hv₂, hcv⟩ := evalExp_cmpE_iff.1 hc
  have e₁₂ : v₁ = v₂ := Silmaril.SpecTec.Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hcv
  have e₁ : v₁ = tyV (Ty.group subs) := Option.some.inj ((evalExp_varE_iff.1 hv₁).symm.trans hR)
  have hv₂' : EvalExp env ρ (.caseE "REC" (.caseE "%" (.tupE [.iterE (.varE "subtype")
      RefOkB.subsNIt]))) (.case "REC" (.case "%" (.tuple [.list (subs.toList.map tyV)]))) := by
    rw [← tyV_group, ← e₁, e₁₂]; exact hv₂
  exact pct1_inv hv₂'

/-- **`Deftype_ok` at `_DEF (REC subtype*) i` in `ctxR L`** holds only from `Rectype_ok2` at the
group, in `ctxR (subtype* ++ L)`. -/
theorem deftypeOk_inv {O : ElseI} {L : List Value} {subs : Ty (.list .sub)} {k : Nat}
    (hd : DDerivesB (simEnv B) O "Deftype_ok" "%|-%:OK" []
      (.tuple [ctxR L, tyV (Ty.defn (.group subs) k)])) :
    DDerivesB (simEnv B) O "Rectype_ok2" "%|-%:%" []
      (.tuple [ctxR (subs.toList.map tyV ++ L), tyV (Ty.group subs), .case "OK" (natV 0)]) := by
  obtain ⟨i, nm, qs, e, e', prems, σ, hr, halt, -, he, hp⟩ := dderivesB_inv findRel_deftypeOk hd
  rcases i with _ | i
  all_goals simp only [deftypeOkRules, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq, Rule.ruleD.injEq, List.getElem?_nil, reduceCtorEq] at hr
  obtain ⟨rfl, rfl, -, rfl, rfl⟩ := hr
  have h := ev2 ((concl_eq halt rfl) ▸ he)
  have hC := evalExp_varE_iff.1 h.1
  have hR : (VarEnv.empty.bindVals σ).findVal? "rectype" = some (tyV (Ty.group subs)) :=
    evalExp_varE_iff.1 (ev2 (evCase h.2).2).1
  have hit : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.iterE (.varE "subtype") RefOkB.subsNIt)
      (.list (subs.toList.map tyV)) := by
    cases hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) with
    | ifPr hc => exact rectypeEq_inv hR hc
  obtain ⟨v, hv, hdv⟩ := prem_rule (hp _ (List.mem_cons_self ..))
  rwa [hv.unique (evalExp_tup3 (evalExp_recsCtx_of hC hit) (evalExp_var hR)
    (evalExp_case (evalExp_numE_iff.2 rfl)))] at hdv

/-! ## `Rectype_ok2` -/

/-- `Rectype_ok2/empty`: the group is empty. -/
theorem rect_empty {env : Env} {ρ : VarEnv} {c : Value} {vs : List Value} {m : Nat}
    (he : EvalExp env ρ (.tupE [.varE "C", .caseE "REC" (.caseE "%" (.tupE [.listE []])),
      .caseE "OK" (.varE "i")]) (.tuple [c, .case "REC" (.case "%" (.tuple [.list vs])),
        .case "OK" (natV m)])) : vs = [] := by
  have h := pct1_inv (ev3 he).2.1
  have e := h.unique evListNil
  exact Value.list.inj e

/-- `[x] ++ e`, evaluated at a list. -/
theorem cat_inv {env : Env} {ρ : VarEnv} {x : IL.Id} {e : Exp} {vs : List Value}
    (h : EvalExp env ρ (.catE (.listE [.varE x]) e) (.list vs)) :
    ∃ s₁ rest, vs = s₁ :: rest ∧ ρ.findVal? x = some s₁ ∧ EvalExp env ρ e (.list rest) := by
  obtain ⟨y₁, y₂, hy₁, hy₂, hcat⟩ := evalExp_catE_iff.1 h
  obtain ⟨ys, hys, rfl⟩ := evalExp_listE_iff.1 hy₁
  obtain ⟨s₁, ys', rfl, hs₁, hys'⟩ := Equiv.Validation.evalExps_cons_iff.1 hys
  have hnil : ys' = [] := Equiv.Validation.evalExps_nil_iff.1 hys'
  obtain ⟨rest, rfl⟩ : ∃ rest, y₂ = .list rest := by
    cases y₂ <;> simp_all [Value.cat?]
  have e : vs = s₁ :: rest := by simpa [Value.cat?, hnil] using hcat.symm
  exact ⟨s₁, rest, e, evalExp_varE_iff.1 hs₁, hy₂⟩

/-- `Rectype_ok2/cons`: the head is `Subtype_ok2` at position `m` and the tail `Rectype_ok2` from
`m + 1`. -/
theorem rect_cons {O : ElseI} {els : Prop} {σ : List (IL.Id × Value)} {c : Value}
    {vs : List Value} {m : Nat}
    (he : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.tupE [.varE "C", .caseE "REC" (.caseE "%"
      (.tupE [.catE (.listE [.varE "subtype_1"]) (.iterE (.varE "subtype") RefOkB.subsIt)])),
      .caseE "OK" (.varE "i")]) (.tuple [c, .case "REC" (.case "%" (.tuple [.list vs])),
        .case "OK" (natV m)]))
    (hp : ∀ pr ∈ [Prem.rulePr "Subtype_ok2" [] "%|-%:%" (.tupE [.varE "C", .varE "subtype_1",
        .caseE "OK" (.varE "i")]), .rulePr "Rectype_ok2" [] "%|-%:%" (.tupE [.varE "C",
        .caseE "REC" (.caseE "%" (.tupE [.iterE (.varE "subtype") RefOkB.subsIt])),
        .caseE "OK" (.binE .addOp (.numT .natT) (.varE "i") (.numE (.natN 1)))])],
      DPremB (simEnv B) O els (VarEnv.empty.bindVals σ) pr) :
    ∃ s₁ rest, vs = s₁ :: rest ∧
      DDerivesB (simEnv B) O "Subtype_ok2" "%|-%:%" [] (.tuple [c, s₁, .case "OK" (natV m)]) ∧
      DDerivesB (simEnv B) O "Rectype_ok2" "%|-%:%" []
        (.tuple [c, .case "REC" (.case "%" (.tuple [.list rest])), .case "OK" (natV (m + 1))]) := by
  obtain ⟨h₁, h₂, h₃⟩ := ev3 he
  have hC := evalExp_varE_iff.1 h₁
  have hI := evalExp_varE_iff.1 (evCase h₃).2
  obtain ⟨s₁, rest, hvs, hS, hit⟩ := cat_inv (pct1_inv h₂)
  have hadd : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.binE .addOp (.numT .natT) (.varE "i") (.numE (.natN 1))) (natV (m + 1)) :=
    ⟨3, by simp [evalExp, hI, natV, binValues, boolShort, Num.bin]⟩
  obtain ⟨v₁, hv₁, hd₁⟩ := prem_rule (hp _ (List.mem_cons_self ..))
  obtain ⟨v₂, hv₂, hd₂⟩ := prem_rule (hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  refine ⟨s₁, rest, hvs, ?_, ?_⟩
  · rwa [hv₁.unique (evalExp_tup3 (evalExp_var hC) (evalExp_var hS)
      (evalExp_case (evalExp_var hI)))] at hd₁
  · rwa [hv₂.unique (evalExp_tup3 (evalExp_var hC) (evalExp_case (evalExp_case
      (evalExp_tupE_iff.2 ⟨_, evalExps_cons hit evalExps_nil, rfl⟩))) (evalExp_case hadd))] at hd₂

/-- **`Rectype_ok2`, inverted**: the group is empty, or its head is `Subtype_ok2` at position
`m` and its tail `Rectype_ok2` from `m + 1`. -/
theorem rectypeOk2_inv {O : ElseI} {c : Value} {vs : List Value} {m : Nat}
    (hd : DDerivesB (simEnv B) O "Rectype_ok2" "%|-%:%" []
      (.tuple [c, .case "REC" (.case "%" (.tuple [.list vs])), .case "OK" (natV m)])) :
    vs = [] ∨ ∃ s₁ rest, vs = s₁ :: rest ∧
      DDerivesB (simEnv B) O "Subtype_ok2" "%|-%:%" [] (.tuple [c, s₁, .case "OK" (natV m)]) ∧
      DDerivesB (simEnv B) O "Rectype_ok2" "%|-%:%" []
        (.tuple [c, .case "REC" (.case "%" (.tuple [.list rest])), .case "OK" (natV (m + 1))]) := by
  obtain ⟨i, nm, qs, e, e', prems, σ, hr, halt, -, he, hp⟩ := dderivesB_inv findRel_rectypeOk2 hd
  rcases i with _ | _ | i
  all_goals simp only [rectypeOk2Rules, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq, Rule.ruleD.injEq, List.getElem?_nil, reduceCtorEq] at hr
  all_goals obtain ⟨rfl, rfl, -, rfl, rfl⟩ := hr
  · exact .inl (rect_empty ((concl_eq halt rfl) ▸ he))
  · exact .inr (rect_cons ((concl_eq halt rfl) ▸ he) hp)

/-- **`Rectype_ok2` at `REC subtype*` from position `m`** gives `Subtype_ok2` at every member, at
its position. -/
theorem rectypeOk2_get {O : ElseI} {c : Value} :
    ∀ (vs : List Value) (m : Nat), DDerivesB (simEnv B) O "Rectype_ok2" "%|-%:%" []
      (.tuple [c, .case "REC" (.case "%" (.tuple [.list vs])), .case "OK" (natV m)]) →
      ∀ k st, vs[k]? = some st →
        DDerivesB (simEnv B) O "Subtype_ok2" "%|-%:%" [] (.tuple [c, st, .case "OK" (natV (m + k))])
  | [], _, _, _, _, hk => by simp at hk
  | _ :: rest, m, hd, k, st, hk => by
    rcases rectypeOk2_inv hd with h | ⟨s₁, rest', he, h₁, h₂⟩
    · cases h
    · simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rcases k with _ | k
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        exact h₁
      · simp only [List.getElem?_cons_succ] at hk
        have := rectypeOk2_get rest (m + 1) h₂ k st hk
        rwa [show m + 1 + k = m + (k + 1) by omega] at this

end Silmaril.Wasm.SpecTec.Sim.Round6.TyElim
