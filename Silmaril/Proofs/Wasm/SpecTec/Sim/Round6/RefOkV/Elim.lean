module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.RefOkV.IntroMain

/-!
# Round 6: inverting the rules of `Ref_ok` under `DDerivesB`

One lemma per rule of `Ref_ok`: from the evaluated conclusion at `(storeV hn s, refToValue r, w)`
and the rule's premises, `w` is the image of a type `rt` with `RefOkE s r rt`. The premises that
consult `Ref_ok` itself come with the claim for their value (`PremM`, the induction hypothesis
of the recursion in `ElimMain.lean`); `Reftype_ok {}` and `Reftype_sub {}` are read through
`AgreeTy`'s elimination fields.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_inj)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue refToValue_inj)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round6.Reading

variable {H : Type} {B : Builtins}

/-- The claim, at the value of a `Ref_ok` instance. -/
def RefM (hn : H → String) (s : Store H) (v : Value) : Prop :=
  ∀ r w, v = .tuple [storeV hn s, refToValue r, w] → ∃ rt, w = tyV rt ∧ RefOkE s r rt

/-- The claim, at a premise: a `Ref_ok` premise satisfies it at its value. -/
def PremM (B : Builtins) (hn : H → String) (s : Store H) (ρ : VarEnv) : Prem → Prop
  | .rulePr x _ _ e => x = "Ref_ok" → ∀ v, EvalExp (simEnv B) ρ e v → RefM hn s v
  | _ => True

/-! ## Evaluation inversions -/

theorem evalExp_tup2_inv {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂]) v) :
    ∃ a b, v = .tuple [a, b] ∧ EvalExp env ρ e₁ a ∧ EvalExp env ρ e₂ b := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 h
  obtain ⟨a, ws, rfl, ha, hws⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  obtain ⟨b, us, rfl, hb, hus⟩ := Equiv.Validation.evalExps_cons_iff.1 hws
  obtain rfl := Equiv.Validation.evalExps_nil_iff.1 hus
  exact ⟨a, b, rfl, ha, hb⟩

/-- The conclusion of a base rule: the store, the reference's case, the type. -/
theorem baseConcl_inv {ρ : VarEnv} {op : MixopS} {x : IL.Id} {eh : Exp} {sv rv w : Value}
    (he : EvalExp (simEnv B) ρ (baseConcl op x eh) (.tuple [sv, rv, w])) :
    ρ.findVal? "s" = some sv ∧ (∃ xv, ρ.findVal? x = some xv ∧ rv = .case op xv) ∧
      EvalExp (simEnv B) ρ (refNonNullE eh) w := by
  obtain ⟨h₁, h₂, h₃⟩ := Round5.RefOk.evalExp_tup3_inv he
  obtain ⟨xv, hx, rfl⟩ := evalExp_caseE_iff.1 h₂
  exact ⟨evalExp_varE_iff.1 h₁, ⟨xv, evalExp_varE_iff.1 hx, rfl⟩, h₃⟩

/-- A non-null reference type at an abstract heap type. -/
theorem refNonNullAbs_inv {ρ : VarEnv} {w : Value} {a : AbsHeapType} {op' : MixopS}
    (hop : Silmaril.SpecTec.Equiv.Validation.absV a = .case op' (.tuple []))
    (h : EvalExp (simEnv B) ρ (refNonNullE (absE op')) w) : w = tyV (Ty.ref false (Ty.abs a)) :=
  have hc : EvalExp (simEnv B) ρ (refNonNullE (absE op')) (tyV (Ty.ref false (Ty.abs a))) := by
    have e : tyV (Ty.ref false (Ty.abs a)) =
        .case "REF" (.tuple [.opt none, .case op' (.tuple [])]) := by simp only [tyV, hop]; rfl
    rw [e]
    exact evalExp_case (evalExp_tup2 (evalExp_optE_none_iff.2 rfl)
      (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)))
  h.unique hc

/-- A non-null reference type at the defined type `dt`. -/
theorem refNonNullDt_inv {ρ : VarEnv} {w : Value}
    (h : EvalExp (simEnv B) ρ (refNonNullE dtHeapE) w) :
    ∃ dv, ρ.findVal? "dt" = some dv ∧ w = .case "REF" (.tuple [.opt none, dv]) := by
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨a, b, rfl, ha, hb⟩ := evalExp_tup2_inv hu
  have ha' : a = .opt none := evalExp_optE_none_iff.1 ha
  exact ⟨b, evalExp_varE_iff.1 (evalExp_subE_iff.1 hb), by rw [ha']⟩

/-- `s.F[a].TYPE = dt`, inverted. -/
theorem typePrem_inv {O : ElseI} {els : Prop} {ρ : VarEnv} {F : AtomS}
    (h : DPremB (simEnv B) O els ρ (typePrem F)) :
    ∃ sv lv i iv dv, ρ.findVal? "s" = some sv ∧ sv.field? F = some lv ∧
      ρ.findVal? "a" = some (.num (.natN i)) ∧ lv.idx? i = some iv ∧
      ρ.findVal? "dt" = some dv ∧ iv.field? "TYPE" = some dv := by
  cases h with
  | ifPr he =>
    obtain ⟨v₁, v₂, h₁, h₂, h₃⟩ := evalExp_cmpE_iff.1 he
    have e : v₁ = v₂ := by simpa [cmpValues] using h₃
    obtain ⟨iv, hi, hT⟩ := evalExp_dotE_iff.1 h₁
    obtain ⟨lv, i, hl, ha, hidx⟩ := evalExp_idxE_iff.1 hi
    obtain ⟨sv, hs, hF⟩ := evalExp_dotE_iff.1 hl
    exact ⟨sv, lv, i, iv, v₂, evalExp_varE_iff.1 hs, hF, evalExp_varE_iff.1 ha, hidx,
      evalExp_varE_iff.1 h₂, e ▸ hT⟩

/-- An instance of a mapped list, by index. -/
theorem idx_map_inv {α : Type} {f : α → Value} {l : List α} {i : Nat} {iv : Value}
    (h : (Value.list (l.map f)).idx? i = some iv) : ∃ x, l[i]? = some x ∧ iv = f x := by
  simp only [Value.idx?, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x, hx, rfl⟩

/-! ## The base rules -/

/-- `Ref_ok/null`, inverted. -/
theorem elim_null {ρ : VarEnv} {hn : H → String} {s : Store H} {r : Ref} {w : Value}
    (he : EvalExp (simEnv B) ρ (.tupE [.varE "s", .caseE "REF.NULL_ADDR" (.tupE []),
      .caseE "REF" (.tupE [.optE (some (.caseE "NULL" (.tupE []))), .caseE "BOT" (.tupE [])])])
      (.tuple [storeV hn s, refToValue r, w])) :
    ∃ rt, w = tyV rt ∧ RefOkE s r rt := by
  obtain ⟨-, h₂, h₃⟩ := Round5.RefOk.evalExp_tup3_inv he
  obtain ⟨u, hu, hr⟩ := evalExp_caseE_iff.1 h₂
  have hr' : r = .null := by cases r <;> simp_all [refToValue]
  subst hr'
  exact ⟨_, h₃.unique Round5.RefOk.evalExp_refNullBot, .null⟩

/-- `Ref_ok/i31`, inverted. -/
theorem elim_i31 {ρ : VarEnv} {hn : H → String} {s : Store H} {r : Ref} {w : Value}
    (he : EvalExp (simEnv B) ρ (baseConcl "REF.I31_NUM" "i" (absE "I31"))
      (.tuple [storeV hn s, refToValue r, w])) :
    ∃ rt, w = tyV rt ∧ RefOkE s r rt := by
  obtain ⟨-, ⟨xv, -, hr⟩, h₃⟩ := baseConcl_inv he
  have hw := refNonNullAbs_inv (a := .i31) rfl h₃
  cases r <;> simp [refToValue] at hr
  exact ⟨_, hw, .i31 _⟩

/-- `Ref_ok/host`, inverted. -/
theorem elim_host {ρ : VarEnv} {hn : H → String} {s : Store H} {r : Ref} {w : Value}
    (he : EvalExp (simEnv B) ρ (baseConcl "REF.HOST_ADDR" "a" (absE "ANY"))
      (.tuple [storeV hn s, refToValue r, w])) :
    ∃ rt, w = tyV rt ∧ RefOkE s r rt := by
  obtain ⟨-, ⟨xv, -, hr⟩, h₃⟩ := baseConcl_inv he
  have hw := refNonNullAbs_inv (a := .any) rfl h₃
  cases r <;> simp [refToValue] at hr
  exact ⟨_, hw, .host _⟩

theorem struct_of_case {r : Ref} {i : Nat}
    (hr : refToValue r = .case "REF.STRUCT_ADDR" (.num (.natN i))) : r = .struct i := by
  cases r <;> simp_all [refToValue]

theorem array_of_case {r : Ref} {i : Nat}
    (hr : refToValue r = .case "REF.ARRAY_ADDR" (.num (.natN i))) : r = .array i := by
  cases r <;> simp_all [refToValue]

theorem func_of_case {r : Ref} {i : Nat}
    (hr : refToValue r = .case "REF.FUNC_ADDR" (.num (.natN i))) : r = .func i := by
  cases r <;> simp_all [refToValue]

theorem exn_of_case {r : Ref} {i : Nat}
    (hr : refToValue r = .case "REF.EXN_ADDR" (.num (.natN i))) : r = .exn i := by
  cases r <;> simp_all [refToValue]

/-- `Ref_ok/struct`, inverted. -/
theorem elim_struct {O : ElseI} {els : Prop} {ρ : VarEnv} {hn : H → String} {s : Store H}
    {r : Ref} {w : Value}
    (he : EvalExp (simEnv B) ρ (baseConcl "REF.STRUCT_ADDR" "a" dtHeapE)
      (.tuple [storeV hn s, refToValue r, w]))
    (hp : DPremB (simEnv B) O els ρ (typePrem "STRUCTS")) :
    ∃ rt, w = tyV rt ∧ RefOkE s r rt := by
  obtain ⟨hS, ⟨xv, hX, hr⟩, h₃⟩ := baseConcl_inv he
  obtain ⟨dv, hD, rfl⟩ := refNonNullDt_inv h₃
  obtain ⟨sv, lv, i, iv, dv', hS', hF, hA, hidx, hD', hT⟩ := typePrem_inv hp
  have esv : sv = storeV hn s := Option.some.inj (hS'.symm.trans hS)
  have exv : xv = .num (.natN i) := Option.some.inj (hX.symm.trans hA)
  have edv : dv' = dv := Option.some.inj (hD'.symm.trans hD)
  have hl : lv = .list (s.structs.map structInstV) := by
    rw [esv] at hF
    exact (Option.some.inj hF).symm
  obtain ⟨si, hsi, rfl⟩ := idx_map_inv (hl ▸ hidx)
  have hty : dv = tyV si.type := (Option.some.inj (edv ▸ hT)).symm
  have hr' : r = .struct i := struct_of_case (exv ▸ hr)
  subst hr' hty
  exact ⟨_, rfl, .struct hsi⟩

/-- `Ref_ok/array`, inverted. -/
theorem elim_array {O : ElseI} {els : Prop} {ρ : VarEnv} {hn : H → String} {s : Store H}
    {r : Ref} {w : Value}
    (he : EvalExp (simEnv B) ρ (baseConcl "REF.ARRAY_ADDR" "a" dtHeapE)
      (.tuple [storeV hn s, refToValue r, w]))
    (hp : DPremB (simEnv B) O els ρ (typePrem "ARRAYS")) :
    ∃ rt, w = tyV rt ∧ RefOkE s r rt := by
  obtain ⟨hS, ⟨xv, hX, hr⟩, h₃⟩ := baseConcl_inv he
  obtain ⟨dv, hD, rfl⟩ := refNonNullDt_inv h₃
  obtain ⟨sv, lv, i, iv, dv', hS', hF, hA, hidx, hD', hT⟩ := typePrem_inv hp
  have esv : sv = storeV hn s := Option.some.inj (hS'.symm.trans hS)
  have exv : xv = .num (.natN i) := Option.some.inj (hX.symm.trans hA)
  have edv : dv' = dv := Option.some.inj (hD'.symm.trans hD)
  have hl : lv = .list (s.arrays.map arrayInstV) := by
    rw [esv] at hF
    exact (Option.some.inj hF).symm
  obtain ⟨ai, hai, rfl⟩ := idx_map_inv (hl ▸ hidx)
  have hty : dv = tyV ai.type := (Option.some.inj (edv ▸ hT)).symm
  have hr' : r = .array i := array_of_case (exv ▸ hr)
  subst hr' hty
  exact ⟨_, rfl, .array hai⟩

/-- `Ref_ok/func`, inverted. -/
theorem elim_func {O : ElseI} {els : Prop} {ρ : VarEnv} {hn : H → String} {s : Store H}
    {r : Ref} {w : Value}
    (he : EvalExp (simEnv B) ρ (baseConcl "REF.FUNC_ADDR" "a" dtHeapE)
      (.tuple [storeV hn s, refToValue r, w]))
    (hp : DPremB (simEnv B) O els ρ (typePrem "FUNCS")) :
    ∃ rt, w = tyV rt ∧ RefOkE s r rt := by
  obtain ⟨hS, ⟨xv, hX, hr⟩, h₃⟩ := baseConcl_inv he
  obtain ⟨dv, hD, rfl⟩ := refNonNullDt_inv h₃
  obtain ⟨sv, lv, i, iv, dv', hS', hF, hA, hidx, hD', hT⟩ := typePrem_inv hp
  have esv : sv = storeV hn s := Option.some.inj (hS'.symm.trans hS)
  have exv : xv = .num (.natN i) := Option.some.inj (hX.symm.trans hA)
  have edv : dv' = dv := Option.some.inj (hD'.symm.trans hD)
  have hl : lv = .list (s.funcs.map (funcInstV hn)) := by
    rw [esv] at hF
    exact (Option.some.inj hF).symm
  obtain ⟨fi, hfi, rfl⟩ := idx_map_inv (hl ▸ hidx)
  have hty : dv = tyV fi.type := (Option.some.inj (edv ▸ hT)).symm
  have hr' : r = .func i := func_of_case (exv ▸ hr)
  subst hr' hty
  exact ⟨_, rfl, .func hfi⟩

/-- `Ref_ok/exn`, inverted. -/
theorem elim_exn {O : ElseI} {els : Prop} {ρ : VarEnv} {hn : H → String} {s : Store H}
    {r : Ref} {w : Value}
    (he : EvalExp (simEnv B) ρ (baseConcl "REF.EXN_ADDR" "a" (absE "EXN"))
      (.tuple [storeV hn s, refToValue r, w]))
    (hp : DPremB (simEnv B) O els ρ exnPrem) :
    ∃ rt, w = tyV rt ∧ RefOkE s r rt := by
  obtain ⟨hS, ⟨xv, hX, hr⟩, h₃⟩ := baseConcl_inv he
  have hw := refNonNullAbs_inv (a := .exn) rfl h₃
  cases hp with
  | ifPr hc =>
    obtain ⟨v₁, -, h₁, -, -⟩ := evalExp_cmpE_iff.1 hc
    obtain ⟨lv, i, hl, ha, hidx⟩ := evalExp_idxE_iff.1 h₁
    obtain ⟨sv, hs, hF⟩ := evalExp_dotE_iff.1 hl
    have esv : sv = storeV hn s := Option.some.inj ((evalExp_varE_iff.1 hs).symm.trans hS)
    have exv : xv = .num (.natN i) := Option.some.inj (hX.symm.trans (evalExp_varE_iff.1 ha))
    have hl' : lv = .list (s.exns.map exnInstV) := by
      rw [esv] at hF
      exact (Option.some.inj hF).symm
    obtain ⟨e, he', -⟩ := idx_map_inv (hl' ▸ hidx)
    have hr' : r = .exn i := exn_of_case (exv ▸ hr)
    subst hr'
    exact ⟨_, hw, .exn he'⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV
