module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.AgreeOk.DOk
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.AgreeOk.Canon

/-!
# Round 6: the subtyping rules under `DDerivesB`, in any typed context

One lemma per rule of the subtyping group not covered by tracks reading and agreety-subintro:

* under `RECS` (in `RefOkB.ctxR l`): `Heaptype_sub/rec-struct`, `rec-array`, `rec-func`
  (`dd_recKind`) and `rec-sub` (`dd_recSub`);
* at the other sorts, in any typed context: `Valtype_sub/num`, `vec`, `ref`, `bot`,
  `Storagetype_sub/val`, `pack`, `Fieldtype_sub/const`, `var`, `Resulttype_sub`,
  `Comptype_sub/struct`, `array`, `func`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV tyV_list absV natV finalV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Round6.Reading
open Round6.AgreeSub (CtxT HeapT HSub listIterE evalExp_atomE typeusesE)
open Round4 (tyBnd)

variable {B : Builtins}

/-! ## Evaluation helpers -/

/-- `final?` iterated, under a scope binding `final?`. -/
theorem evalExp_finalIter {env : Env} {ρ : VarEnv} {fin : Bool}
    (h : ρ.findVal? "final?" = some (finalV fin))
    (hx : ∀ w, (ρ.bindVals [("final", w)]).findVal? "final" = some w) :
    EvalExp env ρ (.iterE (.varE "final") (.mk .opt [.mk "final" (.varE "final?")]))
      (finalV fin) :=
  IntNumeric.evalExp_iterOpt (o := if fin then some (.case "FINAL" (.tuple [])) else none)
    (v := if fin then some (.case "FINAL" (.tuple [])) else none) h
    (fun w hw => ⟨w, hw, evalExp_var (hx w)⟩) id

/-- `C.RECS[i] = st` evaluates to `true` in `RefOkB.ctxR l` when `l[i] = st`. -/
theorem evalExp_recsEq {env : Env} {ρ : VarEnv} {l : List Value} {i : Nat} {st : Value} {e : Exp}
    (hC : ρ.findVal? "C" = some (RefOkB.ctxR l)) (hI : ρ.findVal? "i" = some (natV i))
    (he : EvalExp env ρ e st) (hi : l[i]? = some st) :
    EvalExp env ρ (.cmpE .eqOp .boolT (.idxE (.dotE (.varE "C") "RECS") (.varE "i")) e)
      (.bool true) :=
  evalExp_cmpE_iff.2 ⟨st, st, evalExp_idxE_iff.2 ⟨.list l, i,
    evalExp_dotE_iff.2 ⟨RefOkB.ctxR l, evalExp_var hC, rfl⟩, evalExp_var hI, hi⟩,
    he, by simp [cmpValues]⟩

/-- A bounded sequence's image is a typed list at its elements' sort. -/
theorem typedV_tyList {k : TKind} {s : IL.Id} {t : Ty (.list k)} (hb : tyBnd t = true)
    (hs : ∀ u, Round5.Pos.TyT B k u → TypedV (simEnv B) (.varT s []) u) :
    TypedV (simEnv B) (.iterT (.varT s []) .list) (tyV t) := by
  obtain ⟨l, hl, hall⟩ := Round5.Pos.tyT_tyV (B := B) t hb
  rw [hl]
  exact typedV_list_iff.2 fun u hu => hs u (hall u hu)

/-! ## `REC` rules -/

/-- The scope of `rec-struct`/`rec-array`/`rec-func`. -/
def recσ (l : List Value) (i : Nat) (fin : Bool) (rest : List (IL.Id × Value)) :
    List (IL.Id × Value) :=
  [("C", RefOkB.ctxR l), ("i", natV i), ("final?", finalV fin)] ++ rest

/-- The value of `SUB final? eps STRUCT %(fieldtype*)` under `recσ`. -/
theorem evalExp_recStructSub {l : List Value} {i : Nat} {fin : Bool} {fs : Ty (.list .field)} :
    EvalExp (simEnv B) (VarEnv.empty.bindVals (recσ l i fin [("fieldtype*", tyV fs)]))
      (.caseE "SUB" (.tupE [.iterE (.varE "final") (.mk .opt [.mk "final" (.varE "final?")]),
        .listE [], .caseE "STRUCT" (resE "fieldtype")]))
      (tyV (Ty.sub fin .nil (.struct fs) : CSubType)) := by
  have hs : EvalExp (simEnv B) (VarEnv.empty.bindVals (recσ l i fin [("fieldtype*", tyV fs)]))
      (.caseE "STRUCT" (resE "fieldtype")) (tyV (Ty.struct fs)) := by
    rw [tyV, tyV_list]
    exact evalExp_case (evalExp_resE rfl fun _ => rfl)
  exact evalExp_case (evalExp_tup3 (evalExp_finalIter rfl fun _ => rfl)
    (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩) hs)

/-- **`Heaptype_sub/rec-struct`.** -/
theorem dd_recStruct (O : ElseI) {l : List Value} (hc : CtxT B (RefOkB.ctxR l)) {i : Nat}
    {fin : Bool} {fs : Ty (.list .field)} (hb : tyBnd (Ty.struct fs) = true)
    (hi : l[i]? = some (tyV (Ty.sub fin .nil (.struct fs) : CSubType))) :
    HSub B O (RefOkB.ctxR l) (tyV (Ty.recv i : CTypeUse)) (absV .struct) :=
  dderivesB_of_ruleAt ruleAt_recStruct (self_mem_conclAlts _)
    (recσ l i fin [("fieldtype*", tyV fs)])
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (RefOkB.typedV_n i _ (valsOnly_bind _)) (QuantsOk.cons rfl
        ((Round5.Int.typesB B).final fin _ (valsOnly_bind _)) (QuantsOk.cons rfl
          ((typedV_tyList (tyBnd_struct' hb) fun _ h => h) _ (valsOnly_bind _)) QuantsOk.nil))))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_case (evalExp_var rfl)) (evalExp_atomE "STRUCT"))
    (premsB_one (.ifPr (evalExp_recsEq rfl rfl evalExp_recStructSub hi)))

/-- **`Heaptype_sub/rec-array`.** -/
theorem dd_recArray (O : ElseI) {l : List Value} (hc : CtxT B (RefOkB.ctxR l)) {i : Nat}
    {fin : Bool} {f : CFieldType} (hb : tyBnd (Ty.array f) = true)
    (hi : l[i]? = some (tyV (Ty.sub fin .nil (.array f) : CSubType))) :
    HSub B O (RefOkB.ctxR l) (tyV (Ty.recv i : CTypeUse)) (absV .array) :=
  dderivesB_of_ruleAt ruleAt_recArray (self_mem_conclAlts _)
    (recσ l i fin [("fieldtype", tyV f)])
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (RefOkB.typedV_n i _ (valsOnly_bind _)) (QuantsOk.cons rfl
        ((Round5.Int.typesB B).final fin _ (valsOnly_bind _))
        (QuantsOk.cons rfl (Round5.Pos.tyT_tyV (B := B) f hb _ (valsOnly_bind _))
          QuantsOk.nil))))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_case (evalExp_var rfl)) (evalExp_atomE "ARRAY"))
    (premsB_one (.ifPr (evalExp_recsEq rfl rfl (evalExp_case (evalExp_tup3
      (evalExp_finalIter rfl fun _ => rfl) (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩)
      (evalExp_case (evalExp_var rfl)))) hi)))

/-- The value of `SUB final? eps FUNC %(t_1*) -> %(t_2*)` under `recσ`. -/
theorem evalExp_recFuncSub {l : List Value} {i : Nat} {fin : Bool} {ps rs : Ty (.list .val)} :
    EvalExp (simEnv B) (VarEnv.empty.bindVals (recσ l i fin [("t_1*", tyV ps), ("t_2*", tyV rs)]))
      (.caseE "SUB" (.tupE [.iterE (.varE "final") (.mk .opt [.mk "final" (.varE "final?")]),
        .listE [], .caseE "FUNC%->%" (.tupE [resE "t_1", resE "t_2"])]))
      (tyV (Ty.sub fin .nil (.func ps rs) : CSubType)) := by
  have hs : EvalExp (simEnv B)
      (VarEnv.empty.bindVals (recσ l i fin [("t_1*", tyV ps), ("t_2*", tyV rs)]))
      (.caseE "FUNC%->%" (.tupE [resE "t_1", resE "t_2"])) (tyV (Ty.func ps rs)) := by
    rw [tyV, tyV_list, tyV_list]
    exact evalExp_case (evalExp_tup2 (evalExp_resE rfl fun _ => rfl)
      (evalExp_resE rfl fun _ => rfl))
  exact evalExp_case (evalExp_tup3 (evalExp_finalIter rfl fun _ => rfl)
    (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩) hs)

/-- **`Heaptype_sub/rec-func`.** -/
theorem dd_recFunc (O : ElseI) {l : List Value} (hc : CtxT B (RefOkB.ctxR l)) {i : Nat}
    {fin : Bool} {ps rs : Ty (.list .val)} (hb : tyBnd (Ty.func ps rs) = true)
    (hi : l[i]? = some (tyV (Ty.sub fin .nil (.func ps rs) : CSubType))) :
    HSub B O (RefOkB.ctxR l) (tyV (Ty.recv i : CTypeUse)) (absV .func) :=
  have hpr := tyBnd_func' hb
  dderivesB_of_ruleAt ruleAt_recFunc (self_mem_conclAlts _)
    (recσ l i fin [("t_1*", tyV ps), ("t_2*", tyV rs)])
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (RefOkB.typedV_n i _ (valsOnly_bind _)) (QuantsOk.cons rfl
        ((Round5.Int.typesB B).final fin _ (valsOnly_bind _))
        (QuantsOk.cons rfl ((typedV_tyList hpr.1 fun _ h => h.1) _ (valsOnly_bind _))
          (QuantsOk.cons rfl ((typedV_tyList hpr.2 fun _ h => h.1) _ (valsOnly_bind _))
            QuantsOk.nil)))))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_case (evalExp_var rfl)) (evalExp_atomE "FUNC"))
    (premsB_one (.ifPr (evalExp_recsEq rfl rfl evalExp_recFuncSub hi)))

/-- **`Heaptype_sub/rec-struct`, `rec-array`, `rec-func`**: `REC i` is below the kind of a
parent-free `RECS[i]`. -/
theorem dd_recKind (O : ElseI) {l : List Value} (hc : CtxT B (RefOkB.ctxR l)) {i : Nat}
    {fin : Bool} {ct : CCompType} (hb : tyBnd ct = true)
    (hi : l[i]? = some (tyV (Ty.sub fin .nil ct : CSubType))) :
    HSub B O (RefOkB.ctxR l) (tyV (Ty.recv i : CTypeUse)) (absV (compAbs ct)) := by
  cases ct with
  | struct fs => exact dd_recStruct O hc hb hi
  | array f => exact dd_recArray O hc hb hi
  | func ps rs => exact dd_recFunc O hc hb hi

/-- The scope of `rec-sub`. -/
def recSubσ (l : List Value) (i : Nat) (sups : Ty (.list .use)) (j : Nat) (fin : Bool)
    (ct : CCompType) : List (IL.Id × Value) :=
  [("C", RefOkB.ctxR l), ("i", natV i), ("typeuse*", tyV sups), ("j", natV j),
    ("final?", finalV fin), ("ct", tyV ct)]

/-- `typeuse*` under `recSubσ`. -/
theorem evalExp_recSubUses {env : Env} {l : List Value} {i : Nat} {sups : Ty (.list .use)}
    {j : Nat} {fin : Bool} {ct : CCompType} :
    EvalExp env (VarEnv.empty.bindVals (recSubσ l i sups j fin ct)) typeusesE (tyV sups) := by
  have hu := evalExp_iterMap (env := env) (ρ := VarEnv.empty.bindVals (recSubσ l i sups j fin ct))
    (b := .varE "typeuse") (x := "typeuse") (y := "typeuse*") (ws := sups.toList.map tyV)
    (g := fun w => w) (by rw [← tyV_list]; rfl) (fun w _ => evalExp_var rfl)
  rw [List.map_id', ← tyV_list] at hu
  exact hu

/-- **`Heaptype_sub/rec-sub`**: `REC i` is below each declared supertype of `RECS[i]`. -/
theorem dd_recSub (O : ElseI) {l : List Value} (hc : CtxT B (RefOkB.ctxR l)) {i j : Nat}
    {fin : Bool} {sups : Ty (.list .use)} {ct : CCompType} {u : CTypeUse}
    (hb : tyBnd (Ty.sub fin sups ct : CSubType) = true)
    (hi : l[i]? = some (tyV (Ty.sub fin sups ct : CSubType))) (hj : sups.toList[j]? = some u) :
    HSub B O (RefOkB.ctxR l) (tyV (Ty.recv i : CTypeUse)) (tyV u) :=
  have T := Round5.Int.typesB B
  have hb' := tyBnd_sub' hb
  dderivesB_of_ruleAt ruleAt_recSub (self_mem_conclAlts _) (recSubσ l i sups j fin ct)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (RefOkB.typedV_n i _ (valsOnly_bind _)) (QuantsOk.cons rfl
        (T.typeuses sups hb'.1 _ (valsOnly_bind _)) (QuantsOk.cons rfl
          (RefOkB.typedV_natT j _ (valsOnly_bind _)) (QuantsOk.cons rfl
            (T.final fin _ (valsOnly_bind _)) (QuantsOk.cons rfl
              (T.comptype ct hb'.2 _ (valsOnly_bind _)) QuantsOk.nil))))))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_case (evalExp_var rfl))
      (RefsGC.evalExp_sub_of (RefsGC.evalExp_idx (l := sups.toList.map tyV)
        (tyV_list sups ▸ evalExp_recSubUses) (evalExp_var rfl) (by simp [hj]))))
    (premsB_one (.ifPr (evalExp_recsEq rfl rfl (evalExp_case (evalExp_tup3
      (evalExp_finalIter rfl fun _ => rfl) evalExp_recSubUses (evalExp_var rfl))) hi)))

/-! ## The other sorts -/

/-- **A subsumption rule `x_1 <: x_2`** (`Valtype_sub/num`, …) from the relation at `x`'s
sort. -/
theorem dd_subsumeSub (O : ElseI) {c v₁ v₂ : Value} (hc : CtxT B c) {r r' x s' nm : IL.Id}
    {k : Nat} (hr : HasRuleAt (simEnv B) r "%|-%<:%" k (subsumeRule nm x x s' r'))
    (hv₁ : TypedV (simEnv B) (.varT x []) v₁) (hv₂ : TypedV (simEnv B) (.varT x []) v₂)
    (hd : DDerivesB (simEnv B) O r' "%|-%<:%" [] (.tuple [c, v₁, v₂]))
    (hC : (VarEnv.empty.bindVals [("C", c), (x ++ "_1", v₁), (x ++ "_2", v₂)]).findVal? "C" =
      some c := by rfl)
    (h₁ : (VarEnv.empty.bindVals [("C", c), (x ++ "_1", v₁), (x ++ "_2", v₂)]).findVal?
      (x ++ "_1") = some v₁ := by rfl)
    (h₂ : (VarEnv.empty.bindVals [("C", c), (x ++ "_1", v₁), (x ++ "_2", v₂)]).findVal?
      (x ++ "_2") = some v₂ := by rfl) :
    DDerivesB (simEnv B) O r "%|-%<:%" [] (.tuple [c, v₁, v₂]) :=
  dderivesB_of_ruleAt hr (self_mem_conclAlts _) [("C", c), (x ++ "_1", v₁), (x ++ "_2", v₂)]
    (QuantsOk.cons hC (hc _ (valsOnly_bind _)) (QuantsOk.cons h₁ (hv₁ _ (valsOnly_bind _))
      (QuantsOk.cons h₂ (hv₂ _ (valsOnly_bind _)) QuantsOk.nil)))
    (evalExp_tup3 (evalExp_var hC) (RefsGC.evalExp_sub_of (evalExp_var h₁))
      (RefsGC.evalExp_sub_of (evalExp_var h₂)))
    (premsB_one (.rulePr (evalArgs_nil _ _)
      (evalExp_tup3 (evalExp_var hC) (evalExp_var h₁) (evalExp_var h₂)) hd))

/-- **A reflexive leaf rule** (`Numtype_sub`, `Vectype_sub`, `Packtype_sub`). -/
theorem dd_leafSub (O : ElseI) {c v : Value} (hc : CtxT B c) {r x : IL.Id}
    (hr : HasRuleAt (simEnv B) r "%|-%<:%" 0 (leafSubRule x))
    (hv : TypedV (simEnv B) (.varT x []) v)
    (hC : (VarEnv.empty.bindVals [("C", c), (x, v)]).findVal? "C" = some c := by rfl)
    (hx : (VarEnv.empty.bindVals [("C", c), (x, v)]).findVal? x = some v := by rfl) :
    DDerivesB (simEnv B) O r "%|-%<:%" [] (.tuple [c, v, v]) :=
  dderivesB_of_ruleAt hr (self_mem_conclAlts _) [("C", c), (x, v)]
    (QuantsOk.cons hC (hc _ (valsOnly_bind _)) (QuantsOk.cons hx (hv _ (valsOnly_bind _))
      QuantsOk.nil))
    (evalExp_tup3 (evalExp_var hC) (evalExp_var hx) (evalExp_var hx)) premsB_nil

/-- **`Valtype_sub/bot`.** -/
theorem dd_valtypeSubBot (O : ElseI) {c v : Value} (hc : CtxT B c)
    (hv : TypedV (simEnv B) (.varT "valtype" []) v) :
    DDerivesB (simEnv B) O "Valtype_sub" "%|-%<:%" [] (.tuple [c, .case "BOT" (.tuple []), v]) :=
  dderivesB_of_ruleAt ruleAt_valtypeSubBot (self_mem_conclAlts _) [("C", c), ("valtype", v)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (hv _ (valsOnly_bind _))
      QuantsOk.nil))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_atomE "BOT") (evalExp_var rfl)) premsB_nil

/-- The scope of `Fieldtype_sub`. -/
def fieldσ (c z₁ z₂ : Value) : List (IL.Id × Value) := [("C", c), ("zt_1", z₁), ("zt_2", z₂)]

/-- `MUT?`, evaluated. -/
theorem evalExp_mutOptE {env : Env} {ρ : VarEnv} (b : Bool) :
    EvalExp env ρ (mutOptE b) (.opt (if b then some (.case "MUT" (.tuple [])) else none)) := by
  cases b
  · exact evalExp_optE_none_iff.2 rfl
  · exact evalExp_optE_some_iff.2 ⟨_, evalExp_atomE "MUT", rfl⟩

/-- **`Fieldtype_sub/const`.** -/
theorem dd_fieldtypeSubConst (O : ElseI) {c z₁ z₂ : Value} (hc : CtxT B c)
    (h₁ : TypedV (simEnv B) (.varT "storagetype" []) z₁)
    (h₂ : TypedV (simEnv B) (.varT "storagetype" []) z₂)
    (hd : DDerivesB (simEnv B) O "Storagetype_sub" "%|-%<:%" [] (.tuple [c, z₁, z₂])) :
    DDerivesB (simEnv B) O "Fieldtype_sub" "%|-%<:%" []
      (.tuple [c, .case "%%" (.tuple [.opt none, z₁]), .case "%%" (.tuple [.opt none, z₂])]) :=
  dderivesB_of_ruleAt ruleAt_fieldtypeSubConst (self_mem_conclAlts _) (fieldσ c z₁ z₂)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (h₁ _ (valsOnly_bind _))
      (QuantsOk.cons rfl (h₂ _ (valsOnly_bind _)) QuantsOk.nil)))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_case (evalExp_tup2 (evalExp_mutOptE false)
      (evalExp_var rfl))) (evalExp_case (evalExp_tup2 (evalExp_mutOptE false) (evalExp_var rfl))))
    (premsB_one (.rulePr (evalArgs_nil _ _)
      (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl)) hd))

/-- **`Fieldtype_sub/var`.** -/
theorem dd_fieldtypeSubVar (O : ElseI) {c z₁ z₂ : Value} (hc : CtxT B c)
    (h₁ : TypedV (simEnv B) (.varT "storagetype" []) z₁)
    (h₂ : TypedV (simEnv B) (.varT "storagetype" []) z₂)
    (hd : DDerivesB (simEnv B) O "Storagetype_sub" "%|-%<:%" [] (.tuple [c, z₁, z₂]))
    (hd' : DDerivesB (simEnv B) O "Storagetype_sub" "%|-%<:%" [] (.tuple [c, z₂, z₁])) :
    DDerivesB (simEnv B) O "Fieldtype_sub" "%|-%<:%" []
      (.tuple [c, .case "%%" (.tuple [.opt (some (.case "MUT" (.tuple []))), z₁]),
        .case "%%" (.tuple [.opt (some (.case "MUT" (.tuple []))), z₂])]) :=
  dderivesB_of_ruleAt ruleAt_fieldtypeSubVar (self_mem_conclAlts _) (fieldσ c z₁ z₂)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (h₁ _ (valsOnly_bind _))
      (QuantsOk.cons rfl (h₂ _ (valsOnly_bind _)) QuantsOk.nil)))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_case (evalExp_tup2 (evalExp_mutOptE true)
      (evalExp_var rfl))) (evalExp_case (evalExp_tup2 (evalExp_mutOptE true) (evalExp_var rfl))))
    (premsB_two (.rulePr (evalArgs_nil _ _)
      (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl)) hd)
      (.rulePr (evalArgs_nil _ _)
      (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl)) hd'))

/-- The scope of `Resulttype_sub`. -/
def resSubσ (c : Value) (ps : List (Value × Value)) : List (IL.Id × Value) :=
  [("C", c), ("t_1*", .list (ps.map Prod.fst)), ("t_2*", .list (ps.map Prod.snd))]

/-- **`Resulttype_sub`**, from `Valtype_sub` pointwise. -/
theorem dd_resulttypeSub (O : ElseI) {c : Value} (hc : CtxT B c) {ps : List (Value × Value)}
    (hT : ∀ p ∈ ps, TypedV (simEnv B) (.varT "valtype" []) p.1 ∧
      TypedV (simEnv B) (.varT "valtype" []) p.2)
    (h : ∀ p ∈ ps, DDerivesB (simEnv B) O "Valtype_sub" "%|-%<:%" [] (.tuple [c, p.1, p.2])) :
    DDerivesB (simEnv B) O "Resulttype_sub" "%|-%<:%" []
      (.tuple [c, .case "%" (.tuple [.list (ps.map Prod.fst)]),
        .case "%" (.tuple [.list (ps.map Prod.snd)])]) :=
  dderivesB_of_ruleAt ruleAt_resulttypeSub (self_mem_conclAlts _) (resSubσ c ps)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_list_iff.2 (fun v hv => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hv
        exact (hT p hp).1) _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_list_iff.2 (fun v hv => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hv
        exact (hT p hp).2) _ (valsOnly_bind _)) QuantsOk.nil)))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_resE rfl fun _ => rfl)
      (evalExp_resE rfl fun _ => rfl))
    (premsB_one (dpremB_iter2 rfl rfl fun p hp => .rulePr (evalArgs_nil _ _)
      (evalExp_tup3 (evalExp_var (by simp [resSubσ, VarEnv.findVal?, VarEnv.bindVals, Map.binds,
        Map.bind])) (evalExp_var rfl) (evalExp_var rfl)) (h p hp)))

/-- The scope of `Comptype_sub/struct`. -/
def structSubσ (c : Value) (ps : List (Value × Value)) (extra : List Value) :
    List (IL.Id × Value) :=
  [("C", c), ("ft_1*", .list (ps.map Prod.fst)), ("ft'_1*", .list extra),
    ("ft_2*", .list (ps.map Prod.snd))]

/-- **`Comptype_sub/struct`**, from `Fieldtype_sub` on a prefix. -/
theorem dd_comptypeSubStruct (O : ElseI) {c : Value} (hc : CtxT B c) {ps : List (Value × Value)}
    {extra : List Value}
    (hT : ∀ p ∈ ps, TypedV (simEnv B) (.varT "fieldtype" []) p.1 ∧
      TypedV (simEnv B) (.varT "fieldtype" []) p.2)
    (hE : ∀ f ∈ extra, TypedV (simEnv B) (.varT "fieldtype" []) f)
    (h : ∀ p ∈ ps, DDerivesB (simEnv B) O "Fieldtype_sub" "%|-%<:%" [] (.tuple [c, p.1, p.2])) :
    DDerivesB (simEnv B) O "Comptype_sub" "%|-%<:%" []
      (.tuple [c, .case "STRUCT" (.case "%" (.tuple [.list (ps.map Prod.fst ++ extra)])),
        .case "STRUCT" (.case "%" (.tuple [.list (ps.map Prod.snd)]))]) :=
  have e₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals (structSubσ c ps extra)) (listIterE "ft_1")
      (.list (ps.map Prod.fst)) := evalExp_listIterV rfl fun _ => rfl
  have e₂ : EvalExp (simEnv B) (VarEnv.empty.bindVals (structSubσ c ps extra)) (listIterE "ft'_1")
      (.list extra) := evalExp_listIterV rfl fun _ => rfl
  dderivesB_of_ruleAt ruleAt_comptypeSubStruct (self_mem_conclAlts _) (structSubσ c ps extra)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_list_iff.2 (fun v hv => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hv
        exact (hT p hp).1) _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_list_iff.2 hE _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_list_iff.2 (fun v hv => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hv
        exact (hT p hp).2) _ (valsOnly_bind _)) QuantsOk.nil))))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_case (evalExp_case (evalExp_tupE_iff.2
      ⟨_, evalExps_cons (evalExp_catE_iff.2 ⟨_, _, e₁, e₂, rfl⟩) evalExps_nil, rfl⟩)))
      (evalExp_case (evalExp_resE rfl fun _ => rfl)))
    (premsB_one (dpremB_iter2 rfl rfl fun p hp => .rulePr (evalArgs_nil _ _)
      (evalExp_tup3 (evalExp_var (by simp [structSubσ, VarEnv.findVal?, VarEnv.bindVals,
        Map.binds, Map.bind])) (evalExp_var rfl) (evalExp_var rfl)) (h p hp)))

/-- **`Comptype_sub/array`.** -/
theorem dd_comptypeSubArray (O : ElseI) {c f₁ f₂ : Value} (hc : CtxT B c)
    (h₁ : TypedV (simEnv B) (.varT "fieldtype" []) f₁)
    (h₂ : TypedV (simEnv B) (.varT "fieldtype" []) f₂)
    (hd : DDerivesB (simEnv B) O "Fieldtype_sub" "%|-%<:%" [] (.tuple [c, f₁, f₂])) :
    DDerivesB (simEnv B) O "Comptype_sub" "%|-%<:%" []
      (.tuple [c, .case "ARRAY" f₁, .case "ARRAY" f₂]) :=
  dderivesB_of_ruleAt ruleAt_comptypeSubArray (self_mem_conclAlts _)
    [("C", c), ("ft_1", f₁), ("ft_2", f₂)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (h₁ _ (valsOnly_bind _))
      (QuantsOk.cons rfl (h₂ _ (valsOnly_bind _)) QuantsOk.nil)))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_case (evalExp_var rfl))
      (evalExp_case (evalExp_var rfl)))
    (premsB_one (.rulePr (evalArgs_nil _ _)
      (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl)) hd))

/-- The scope of `Comptype_sub/func`. -/
def funcSubσ (c : Value) (p₁ r₁ p₂ r₂ : List Value) : List (IL.Id × Value) :=
  [("C", c), ("t_11*", .list p₁), ("t_12*", .list r₁), ("t_21*", .list p₂), ("t_22*", .list r₂)]

/-- **`Comptype_sub/func`**, from two `Resulttype_sub`. -/
theorem dd_comptypeSubFunc (O : ElseI) {c : Value} (hc : CtxT B c) {p₁ r₁ p₂ r₂ : List Value}
    (hT : ∀ l ∈ [p₁, r₁, p₂, r₂], ∀ t ∈ l, TypedV (simEnv B) (.varT "valtype" []) t)
    (hp : DDerivesB (simEnv B) O "Resulttype_sub" "%|-%<:%" []
      (.tuple [c, .case "%" (.tuple [.list p₂]), .case "%" (.tuple [.list p₁])]))
    (hr : DDerivesB (simEnv B) O "Resulttype_sub" "%|-%<:%" []
      (.tuple [c, .case "%" (.tuple [.list r₁]), .case "%" (.tuple [.list r₂])])) :
    DDerivesB (simEnv B) O "Comptype_sub" "%|-%<:%" []
      (.tuple [c, .case "FUNC%->%" (.tuple [.case "%" (.tuple [.list p₁]),
          .case "%" (.tuple [.list r₁])]),
        .case "FUNC%->%" (.tuple [.case "%" (.tuple [.list p₂]),
          .case "%" (.tuple [.list r₂])])]) :=
  have hl : ∀ l ∈ [p₁, r₁, p₂, r₂], TypedV (simEnv B) (.iterT (.varT "valtype" []) .list)
      (.list l) := fun l hl => typedV_list_iff.2 (hT l hl)
  dderivesB_of_ruleAt ruleAt_comptypeSubFunc (self_mem_conclAlts _) (funcSubσ c p₁ r₁ p₂ r₂)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (hl p₁ (by simp) _ (valsOnly_bind _)) (QuantsOk.cons rfl
        (hl r₁ (by simp) _ (valsOnly_bind _)) (QuantsOk.cons rfl
          (hl p₂ (by simp) _ (valsOnly_bind _)) (QuantsOk.cons rfl
            (hl r₂ (by simp) _ (valsOnly_bind _)) QuantsOk.nil)))))
    (evalExp_tup3 (evalExp_var rfl)
      (evalExp_case (evalExp_tup2 (evalExp_resE rfl fun _ => rfl)
        (evalExp_resE rfl fun _ => rfl)))
      (evalExp_case (evalExp_tup2 (evalExp_resE rfl fun _ => rfl)
        (evalExp_resE rfl fun _ => rfl))))
    (premsB_two (.rulePr (evalArgs_nil _ _) (evalExp_tup3 (evalExp_var rfl)
        (evalExp_resE rfl fun _ => rfl) (evalExp_resE rfl fun _ => rfl)) hp)
      (.rulePr (evalArgs_nil _ _) (evalExp_tup3 (evalExp_var rfl)
        (evalExp_resE rfl fun _ => rfl) (evalExp_resE rfl fun _ => rfl)) hr))

end Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk
