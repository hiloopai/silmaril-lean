module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.AgreeSub.Abs
public import Silmaril.Wasm.SpecTec.Sim.Round5Fwd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Thms

/-!
# Round 6: defined heap types, under `DDerivesB`

In `simEnv (BI P hn host)`, in any typed context `c`, at bounded (`Round4.tyBnd`) types:

* `dderivesB_expandB`: **SpecTec's `Expand` under `DDerivesB`** (round 5's
  `Fwd.dderives_expandB`, lifted along `dderivesB_of_dderives'`);
* `dderivesB_defStruct`, `dderivesB_defArray`, `dderivesB_defFunc`: `Heaptype_sub/struct`,
  `array`, `func`, from Core's `Expand`;
* `dderivesB_def`: `Heaptype_sub/def`; `dderivesB_super`: `Deftype_sub/super`;
* `tyBnd_super`: **the declared supertypes of a bounded defined type are bounded**;
* `dderivesB_reach`: **reachability along declared supertypes in `{}` (`TypeCtx.Reach {}`) is
  derivable**, as a chain of `def`/`super` steps closed by `refl`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV absV tyV_list finalV natV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core (HostSemantics)
open Silmaril.Wasm.Numerics (Profile)
open Round6.Reading
open Round4Int (BI)
open Round4 (tyBnd)

variable {B : Builtins} {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **SpecTec's `Expand` under `DDerivesB`**, on the images of Core's `Expand d ct`, for bounded
`d`. -/
theorem dderivesB_expandB (O : ElseI) {d : DefType} {ct : CCompType} (hd : tyBnd d = true)
    (h : Expand d ct) :
    DDerivesB (simEnv (BI P hn host)) O "Expand" "%~~%" [] (.tuple [tyV d, tyV ct]) :=
  dderivesB_of_dderives' (Round5.Fwd.dderives_expandB (Round5.Int.typesB _) O hd h)

/-- A list variable iterated pointwise evaluates to the image of the sequence it is bound to. -/
theorem evalExp_listIter {env : Env} {ρ : VarEnv} {x : IL.Id} {k : TKind} {t : Ty (.list k)}
    (hy : ρ.findVal? (x ++ "*") = some (tyV t))
    (hx : ∀ w, (ρ.bindVals [(x, w)]).findVal? x = some w) :
    EvalExp env ρ (listIterE x) (tyV t) := by
  have h := evalExp_iterMap (env := env) (b := .varE x) (x := x) (y := x ++ "*")
    (ws := t.toList.map tyV) (g := fun w => w) (by rw [← tyV_list]; exact hy)
    (fun w _ => evalExp_var (hx w))
  rw [List.map_id', ← tyV_list] at h
  exact h

/-- A bounded defined type is a typed heap type. -/
theorem heapT_def {d : DefType} (hd : tyBnd d = true) : HeapT B (tyV d) :=
  typedV_heaptype (h := .use (.dt d)) hd

/-- A bounded defined type is a typed `deftype`. -/
theorem defT {d : DefType} (hd : tyBnd d = true) :
    TypedV (simEnv B) (.varT "deftype" []) (tyV d) := (Round5.Int.typesB B).deftype d hd

/-- **`Heaptype_sub/struct`.** -/
theorem dderivesB_defStruct (O : ElseI) {c : Value} (hc : CtxT (BI P hn host) c) {d : DefType}
    {fs : Ty (.list .field)} (hd : tyBnd d = true) (h : Expand d (.struct fs)) :
    HSub (BI P hn host) O c (tyV d) (absV .struct) := by
  have hfs : tyBnd fs = true := by
    have := Round5.Fwd.tyBnd_of_expand hd h
    simp only [tyBnd, Bool.and_eq_true] at this
    exact this.2
  obtain ⟨l, hl, hall⟩ := Round5.Pos.tyT_tyV (B := BI P hn host) fs hfs
  have hT : TypedV (simEnv (BI P hn host)) (.iterT (.varT "fieldtype" []) .list) (tyV fs) := by
    rw [hl]
    exact typedV_list_iff.2 hall
  exact dderivesB_of_ruleAt ruleAt_struct (self_mem_conclAlts _)
    [("C", c), ("deftype", tyV d), ("fieldtype*", tyV fs)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (defT hd _ (valsOnly_bind _))
      (QuantsOk.cons rfl (hT _ (valsOnly_bind _)) QuantsOk.nil)))
    (evalExp_tup3 (evalExp_var rfl) (RefsGC.evalExp_sub_of (evalExp_var rfl))
      (evalExp_atomE "STRUCT"))
    (premsB_one (.rulePr (evalArgs_nil _ _) (evalExp_tup2 (evalExp_var rfl)
      (evalExp_case (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons
        (evalExp_listIter rfl fun _ => rfl) evalExps_nil, rfl⟩))))
      (dderivesB_expandB O hd h)))

/-- **`Heaptype_sub/array`.** -/
theorem dderivesB_defArray (O : ElseI) {c : Value} (hc : CtxT (BI P hn host) c) {d : DefType}
    {f : CFieldType} (hd : tyBnd d = true) (h : Expand d (.array f)) :
    HSub (BI P hn host) O c (tyV d) (absV .array) := by
  have hf : tyBnd f = true := Round5.Fwd.tyBnd_of_expand hd h
  have hT : TypedV (simEnv (BI P hn host)) (.varT "fieldtype" []) (tyV f) :=
    Round5.Pos.tyT_tyV (B := BI P hn host) f hf
  exact dderivesB_of_ruleAt ruleAt_array (self_mem_conclAlts _)
    [("C", c), ("deftype", tyV d), ("fieldtype", tyV f)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (defT hd _ (valsOnly_bind _))
      (QuantsOk.cons rfl (hT _ (valsOnly_bind _)) QuantsOk.nil)))
    (evalExp_tup3 (evalExp_var rfl) (RefsGC.evalExp_sub_of (evalExp_var rfl))
      (evalExp_atomE "ARRAY"))
    (premsB_one (.rulePr (evalArgs_nil _ _) (evalExp_tup2 (evalExp_var rfl)
      (evalExp_case (evalExp_var rfl))) (dderivesB_expandB O hd h)))

/-- **`Heaptype_sub/func`.** -/
theorem dderivesB_defFunc (O : ElseI) {c : Value} (hc : CtxT (BI P hn host) c) {d : DefType}
    {ps rs : Ty (.list .val)} (hd : tyBnd d = true) (h : Expand d (.func ps rs)) :
    HSub (BI P hn host) O c (tyV d) (absV .func) := by
  have hb := Round5.Fwd.tyBnd_func (Round5.Fwd.tyBnd_of_expand hd h)
  have hT : ∀ ts : Ty (.list .val), tyBnd ts = true →
      TypedV (simEnv (BI P hn host)) (.iterT (.varT "valtype" []) .list) (tyV ts) := fun ts h => by
    rw [tyV_list]
    exact (Round5.Int.typesB _).valtypes ts h
  exact dderivesB_of_ruleAt ruleAt_func (self_mem_conclAlts _)
    [("C", c), ("deftype", tyV d), ("t_1*", tyV ps), ("t_2*", tyV rs)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (defT hd _ (valsOnly_bind _))
      (QuantsOk.cons rfl (hT ps hb.1 _ (valsOnly_bind _))
        (QuantsOk.cons rfl (hT rs hb.2 _ (valsOnly_bind _)) QuantsOk.nil))))
    (evalExp_tup3 (evalExp_var rfl) (RefsGC.evalExp_sub_of (evalExp_var rfl))
      (evalExp_atomE "FUNC"))
    (premsB_one (.rulePr (evalArgs_nil _ _) (evalExp_tup2 (evalExp_var rfl)
      (evalExp_case (evalExp_tup2
        (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons
          (evalExp_listIter rfl fun _ => rfl) evalExps_nil, rfl⟩))
        (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons
          (evalExp_listIter rfl fun _ => rfl) evalExps_nil, rfl⟩)))))
      (dderivesB_expandB O hd h)))

/-- **`Heaptype_sub/def`**, from `Deftype_sub`. -/
theorem dderivesB_def (O : ElseI) {c : Value} (hc : CtxT B c) {d₁ d₂ : DefType}
    (hb₁ : tyBnd d₁ = true) (hb₂ : tyBnd d₂ = true)
    (hs : DDerivesB (simEnv B) O "Deftype_sub" "%|-%<:%" [] (.tuple [c, tyV d₁, tyV d₂])) :
    HSub B O c (tyV d₁) (tyV d₂) :=
  dderivesB_of_ruleAt ruleAt_def (self_mem_conclAlts _)
    [("C", c), ("deftype_1", tyV d₁), ("deftype_2", tyV d₂)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (defT hb₁ _ (valsOnly_bind _))
      (QuantsOk.cons rfl (defT hb₂ _ (valsOnly_bind _)) QuantsOk.nil)))
    (evalExp_tup3 (evalExp_var rfl) (RefsGC.evalExp_sub_of (evalExp_var rfl))
      (RefsGC.evalExp_sub_of (evalExp_var rfl)))
    (premsB_one (.rulePr (evalArgs_nil _ _)
      (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl)) hs))

/-- The assignment of `Deftype_sub/super`'s variables. -/
def superσ (c : Value) (d₁ d₂ : DefType) (fin : Bool) (sups : Ty (.list .use)) (ct : CCompType)
    (j : Nat) : List (IL.Id × Value) :=
  [("C", c), ("deftype_1", tyV d₁), ("deftype_2", tyV d₂), ("final?", finalV fin),
    ("typeuse*", tyV sups), ("ct", tyV ct), ("i", natV j)]

/-- `typeuse*`, evaluated under `superσ`. -/
theorem evalExp_typeuses {env : Env} {c : Value} {d₁ d₂ : DefType} {fin : Bool}
    {sups : Ty (.list .use)} {ct : CCompType} {j : Nat} :
    EvalExp env (VarEnv.empty.bindVals (superσ c d₁ d₂ fin sups ct j)) typeusesE (tyV sups) := by
  have hu := evalExp_iterMap (env := env) (ρ := VarEnv.empty.bindVals (superσ c d₁ d₂ fin sups ct j))
    (b := .varE "typeuse") (x := "typeuse") (y := "typeuse*") (ws := sups.toList.map tyV)
    (g := fun w => w) (by rw [← tyV_list]; rfl) (fun w _ => evalExp_var rfl)
  rw [List.map_id', ← tyV_list] at hu
  exact hu

/-- `SUB final? typeuse* ct`, evaluated under `superσ`. -/
theorem evalExp_superSub {env : Env} {c : Value} {d₁ d₂ : DefType} {fin : Bool}
    {sups : Ty (.list .use)} {ct : CCompType} {j : Nat} :
    EvalExp env (VarEnv.empty.bindVals (superσ c d₁ d₂ fin sups ct j)) superSubE
      (tyV (Ty.sub fin sups ct)) := by
  have hf := IntNumeric.evalExp_iterOpt (env := env)
    (ρ := VarEnv.empty.bindVals (superσ c d₁ d₂ fin sups ct j)) (b := .varE "final")
    (x := "final") (y := "final?") (o := if fin then some (.case "FINAL" (.tuple [])) else none)
    (v := if fin then some (.case "FINAL" (.tuple [])) else none) rfl
    (fun w hw => ⟨w, hw, evalExp_var rfl⟩) id
  exact evalExp_case (evalExp_tup3 hf evalExp_typeuses (evalExp_var rfl))

/-- `$unrolldt(deftype_1) = SUB final? typeuse* ct`, the first premise of `Deftype_sub/super`,
holds under `superσ` when Core's `unrolldt` agrees. -/
theorem dpremB_superIf {O : ElseI} {els : Prop} {c : Value} {d₁ d₂ : DefType} {fin : Bool}
    {sups : Ty (.list .use)} {ct : CCompType} {j : Nat}
    (hun : unrolldt d₁ = some (.sub fin sups ct)) :
    DPremB (simEnv (BI P hn host)) O els (VarEnv.empty.bindVals (superσ c d₁ d₂ fin sups ct j))
      (.ifPr (.cmpE .eqOp .boolT (.callE "unrolldt" [.expA (.varE "deftype_1")]) superSubE)) :=
  .ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_callArgs rfl
    (Equiv.evalArgs_cons (evalExp_var rfl) (evalArgs_nil _ _))
    ((Prims.applies_unrolldt (prof := P) hn host d₁ _).2 (by rw [hun]; rfl)),
    evalExp_superSub, by simp [cmpValues]⟩)

/-- `typeuse*[i]`, evaluated under `superσ`. -/
theorem evalExp_superIdx {env : Env} {c : Value} {d₁ d₂ : DefType} {fin : Bool}
    {sups : Ty (.list .use)} {ct : CCompType} {j : Nat} {u : CTypeUse}
    (hj : sups.toList[j]? = some u) :
    EvalExp env (VarEnv.empty.bindVals (superσ c d₁ d₂ fin sups ct j))
      (.idxE typeusesE (.varE "i")) (tyV u) :=
  RefsGC.evalExp_idx (l := sups.toList.map tyV) (tyV_list sups ▸ evalExp_typeuses)
    (evalExp_var rfl) (by simp [hj])

/-- **`Deftype_sub/super`**: `d₁ <: d₂` when the `j`-th declared supertype of `d₁` is below
`d₂`. -/
theorem dderivesB_super (O : ElseI) {c : Value} (hc : CtxT (BI P hn host) c) {d₁ d₂ : DefType}
    {fin : Bool} {sups : Ty (.list .use)} {ct : CCompType} {j : Nat} {u : CTypeUse}
    (hb₁ : tyBnd d₁ = true) (hb₂ : tyBnd d₂ = true)
    (hun : unrolldt d₁ = some (.sub fin sups ct)) (hj : sups.toList[j]? = some u)
    (hs : HSub (BI P hn host) O c (tyV u) (tyV d₂)) :
    DDerivesB (simEnv (BI P hn host)) O "Deftype_sub" "%|-%<:%" [] (.tuple [c, tyV d₁, tyV d₂]) :=
  have hb := Round5.Fwd.tyBnd_of_unrolldt hb₁ hun
  have T := Round5.Int.typesB (BI P hn host)
  dderivesB_of_ruleAt ruleAt_super (self_mem_conclAlts _) (superσ c d₁ d₂ fin sups ct j)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (defT hb₁ _ (valsOnly_bind _))
      (QuantsOk.cons rfl (defT hb₂ _ (valsOnly_bind _)) (QuantsOk.cons rfl
        (T.final fin _ (valsOnly_bind _)) (QuantsOk.cons rfl (T.typeuses sups hb.1 _
          (valsOnly_bind _)) (QuantsOk.cons rfl (T.comptype ct hb.2 _ (valsOnly_bind _))
            (QuantsOk.cons rfl (RefOkB.typedV_natT j _ (valsOnly_bind _)) QuantsOk.nil)))))))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl))
    (premsB_two (dpremB_superIf hun) (.rulePr (evalArgs_nil _ _) (evalExp_tup3 (evalExp_var rfl)
      (RefsGC.evalExp_sub_of (evalExp_superIdx hj)) (RefsGC.evalExp_sub_of (evalExp_var rfl))) hs))

/-- **The declared supertypes of a bounded defined type are bounded.** -/
theorem tyBnd_super {d : DefType} {u : CTypeUse} (hd : tyBnd d = true) (hu : u ∈ supersOf d) :
    tyBnd u = true := by
  unfold supersOf at hu
  split at hu
  · rename_i st hun
    cases st with
    | sub fin sups ct =>
      exact Round5.Fwd.tyBnd_of_mem (Round5.Fwd.tyBnd_of_unrolldt hd hun).1 hu
  · simp at hu

/-- **Reachability in `{}` is derivable**: a chain of `Deftype_sub/super` steps (each wrapped by
`Heaptype_sub/def`), closed by `Heaptype_sub/refl`. -/
theorem dderivesB_reach (O : ElseI) {c : Value} (hc : CtxT (BI P hn host) c) {d₁ d₂ : DefType}
    (h : ({} : TypeCtx).Reach d₁ d₂) (hb₂ : tyBnd d₂ = true) :
    tyBnd d₁ = true → HSub (BI P hn host) O c (tyV d₁) (tyV d₂) := by
  induction h with
  | refl d => exact fun hb => dderivesB_refl O hc (heapT_def hb)
  | @step d d' e u hu hr _ ih =>
    intro hb
    cases u with
    | idx x => simp [TypeCtx.resolve] at hr
    | recv i => simp [TypeCtx.resolve] at hr
    | dt e' =>
      simp only [TypeCtx.resolve, Option.some.injEq] at hr
      subst hr
      have hbu : tyBnd e' = true := tyBnd_super hb hu
      unfold supersOf at hu
      split at hu
      · rename_i st hun
        cases st with
        | sub fin sups ct =>
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hu
          exact dderivesB_def O hc hb hb₂ (dderivesB_super O hc hb hb₂ hun hj (ih hb₂ hbu))
      · simp at hu

end Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub
