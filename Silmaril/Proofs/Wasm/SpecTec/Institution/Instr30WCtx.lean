module

public import Silmaril.Wasm.SpecTec.Institution.Instr30Y.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk.Thms
public import Silmaril.Wasm.SpecTec.Institution.Instr30W.Defs

/-!
# Instruction typing of the wasm-3.0 script, round 6's `RECS` rules under locals and globals

Round 6's canonical derivations (`Round6.AgreeOk.okD_of`, `subD_of`) are read at the SpecTec
contexts `Round6.RefOkB.ctxR l`, which have nothing but `RECS l`. Most of their rule lemmas are generic in
the context; the ones that read `C.RECS`, unroll through `$unrollht_(C, …)` or build
`{RECS st*} ⊕ C` are stated at `ctxR l`. This file restates exactly those at
`ctxRX ls gs l`, the context with `LOCALS ls`, `GLOBALS gs` and `RECS l`. The proofs are copies of
round 6's (`AgreeOk.DSub`, `DGroup`, `Funcs`, `Round6.RefOkB.Derive`) with the context changed; the
locals and globals are only carried along.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30W

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_list natV absV finalV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core (HostSemantics)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (CtxT HSub typeusesE)
open Silmaril.Wasm.SpecTec.Sim.Round4Int (BI)
open Silmaril.Wasm.SpecTec.Sim.Round4 (tyBnd)

variable {B : Builtins} {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## The contexts -/

/-- **`{LOCALS ls, GLOBALS gs, RECS l}`**, every other field empty. -/
def ctxRX (ls gs l : List Value) : Value :=
  .struct [("TYPES", .list []), ("TAGS", .list []), ("GLOBALS", .list gs), ("MEMS", .list []),
    ("TABLES", .list []), ("FUNCS", .list []), ("DATAS", .list []), ("ELEMS", .list []),
    ("LOCALS", .list ls), ("LABELS", .list []), ("RETURN", .opt none), ("REFS", .list []),
    ("RECS", .list l)]

/-- Without `RECS`, it is an earlier `{LOCALS ls, GLOBALS gs}`. -/
theorem ctxRX_nil (ls gs : List Value) : ctxRX ls gs [] = Instr30Y.ctxLG ls gs := rfl

/-- **`ctxRX ls gs l` is a typed context** when its entries are typed. -/
theorem typedV_ctxRX {ls gs l : List Value}
    (hl : ∀ u ∈ ls, TypedV (simEnv B) (.varT "localtype" []) u)
    (hg : ∀ u ∈ gs, TypedV (simEnv B) (.varT "globaltype" []) u)
    (hr : ∀ u ∈ l, TypedV (simEnv B) (.varT "subtype" []) u) : CtxT B (ctxRX ls gs l) :=
  have hn : TypedV (simEnv B) (.iterT (.varT "resulttype" []) .opt) (.opt none) :=
    fun _ _ => hasTyp_iterT_opt_iff.2 (.inl rfl)
  have h0 {t : Typ} : TypedV (simEnv B) (.iterT t .list) (.list []) := Round5.RefOk.typedV_listNil
  Round5.Pos.typedV_struct Round6.Reading.findTyp_context <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_iff.2 hg) <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_iff.2 hl) <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of hn <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_one (typedV_list_iff.2 hr)

/-! ## `Typeuse_ok/rec` -/

/-- `C.RECS[i] = st` evaluates to `true` in `ctxRX ls gs l` when `l[i] = st`. -/
theorem evalExp_recsIdxX {ρ : VarEnv} {ls gs l : List Value} {i : Nat} {st : Value}
    (hC : ρ.findVal? "C" = some (ctxRX ls gs l)) (hI : ρ.findVal? "i" = some (natV i))
    (hS : ρ.findVal? "st" = some st) (hi : l[i]? = some st) :
    EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT (.idxE (.dotE (.varE "C") "RECS") (.varE "i"))
      (.varE "st")) (.bool true) :=
  evalExp_cmpE_iff.2 ⟨st, st, evalExp_idxE_iff.2 ⟨.list l, i,
    evalExp_dotE_iff.2 ⟨ctxRX ls gs l, Sim.evalExp_var hC, rfl⟩, Sim.evalExp_var hI, hi⟩,
    Sim.evalExp_var hS, by simp [cmpValues]⟩

/-- **`Typeuse_ok/rec`** in `ctxRX ls gs l`. -/
theorem dd_typeuseOkRecX (O : ElseI) {ls gs l : List Value} {i : Nat} {st : Value}
    (hc : CtxT B (ctxRX ls gs l))
    (hst : TypedV (simEnv B) (.varT "subtype" []) st) (hi : l[i]? = some st) :
    DDerivesB (simEnv B) O "Typeuse_ok" "%|-%:OK" [] (.tuple [ctxRX ls gs l, .case "REC" (natV i)]) :=
  dderivesB_of_ruleAt Round6.RefOkB.ruleAt_typeuseOkRec (self_mem_conclAlts _)
    [("C", ctxRX ls gs l), ("i", natV i), ("st", st)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Round6.RefOkB.typedV_n i _ (valsOnly_bind _)) (QuantsOk.cons rfl (hst _ (valsOnly_bind _))
        QuantsOk.nil)))
    (evalExp_tup2 (Sim.evalExp_var rfl) (evalExp_case (Sim.evalExp_var rfl)))
    (premsB_one (.ifPr (evalExp_recsIdxX rfl rfl rfl hi)))

/-! ## `REC` subtyping rules -/

/-- `C.RECS[i] = st` evaluates to `true` in `ctxRX ls gs l` when `l[i] = st`. -/
theorem evalExp_recsEqX {env : Env} {ρ : VarEnv} {ls gs l : List Value} {i : Nat} {st : Value}
    {e : Exp} (hC : ρ.findVal? "C" = some (ctxRX ls gs l)) (hI : ρ.findVal? "i" = some (natV i))
    (he : EvalExp env ρ e st) (hi : l[i]? = some st) :
    EvalExp env ρ (.cmpE .eqOp .boolT (.idxE (.dotE (.varE "C") "RECS") (.varE "i")) e)
      (.bool true) :=
  evalExp_cmpE_iff.2 ⟨st, st, evalExp_idxE_iff.2 ⟨.list l, i,
    evalExp_dotE_iff.2 ⟨ctxRX ls gs l, Sim.evalExp_var hC, rfl⟩, Sim.evalExp_var hI, hi⟩,
    he, by simp [cmpValues]⟩

/-- The scope of `rec-struct`/`rec-array`/`rec-func`. -/
def recσX (ls gs l : List Value) (i : Nat) (fin : Bool) (rest : List (IL.Id × Value)) :
    List (IL.Id × Value) :=
  [("C", ctxRX ls gs l), ("i", natV i), ("final?", finalV fin)] ++ rest

/-- The value of `SUB final? eps STRUCT %(fieldtype*)` under `recσX`. -/
theorem evalExp_recStructSubX {ls gs l : List Value} {i : Nat} {fin : Bool}
    {fs : Silmaril.Wasm.Validation.Ty (.list .field)} :
    EvalExp (simEnv B) (VarEnv.empty.bindVals (recσX ls gs l i fin [("fieldtype*", tyV fs)]))
      (.caseE "SUB" (.tupE [.iterE (.varE "final") (.mk .opt [.mk "final" (.varE "final?")]),
        .listE [], .caseE "STRUCT" (Round6.AgreeOk.resE "fieldtype")]))
      (tyV (Silmaril.Wasm.Validation.Ty.sub fin .nil (.struct fs) : CSubType)) := by
  have hs : EvalExp (simEnv B) (VarEnv.empty.bindVals (recσX ls gs l i fin [("fieldtype*", tyV fs)]))
      (.caseE "STRUCT" (Round6.AgreeOk.resE "fieldtype")) (tyV (Silmaril.Wasm.Validation.Ty.struct fs)) := by
    rw [tyV, tyV_list]
    exact evalExp_case (evalExp_resE rfl fun _ => rfl)
  exact evalExp_case (evalExp_tup3 (evalExp_finalIter rfl fun _ => rfl)
    (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩) hs)

/-- **`Heaptype_sub/rec-struct`** in `ctxRX ls gs l`. -/
theorem dd_recStructX (O : ElseI) {ls gs l : List Value} (hc : CtxT B (ctxRX ls gs l)) {i : Nat}
    {fin : Bool} {fs : Silmaril.Wasm.Validation.Ty (.list .field)} (hb : tyBnd (Silmaril.Wasm.Validation.Ty.struct fs) = true)
    (hi : l[i]? = some (tyV (Silmaril.Wasm.Validation.Ty.sub fin .nil (.struct fs) : CSubType))) :
    HSub B O (ctxRX ls gs l) (tyV (Silmaril.Wasm.Validation.Ty.recv i : CTypeUse)) (absV .struct) :=
  dderivesB_of_ruleAt ruleAt_recStruct (self_mem_conclAlts _)
    (recσX ls gs l i fin [("fieldtype*", tyV fs)])
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Round6.RefOkB.typedV_n i _ (valsOnly_bind _)) (QuantsOk.cons rfl
        ((Round5.Int.typesB B).final fin _ (valsOnly_bind _)) (QuantsOk.cons rfl
          ((typedV_tyList (tyBnd_struct' hb) fun _ h => h) _ (valsOnly_bind _)) QuantsOk.nil))))
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_case (Sim.evalExp_var rfl))
      (Round6.AgreeSub.evalExp_atomE "STRUCT"))
    (premsB_one (.ifPr (evalExp_recsEqX rfl rfl evalExp_recStructSubX hi)))

/-- **`Heaptype_sub/rec-array`** in `ctxRX ls gs l`. -/
theorem dd_recArrayX (O : ElseI) {ls gs l : List Value} (hc : CtxT B (ctxRX ls gs l)) {i : Nat}
    {fin : Bool} {f : CFieldType} (hb : tyBnd (Silmaril.Wasm.Validation.Ty.array f) = true)
    (hi : l[i]? = some (tyV (Silmaril.Wasm.Validation.Ty.sub fin .nil (.array f) : CSubType))) :
    HSub B O (ctxRX ls gs l) (tyV (Silmaril.Wasm.Validation.Ty.recv i : CTypeUse)) (absV .array) :=
  dderivesB_of_ruleAt ruleAt_recArray (self_mem_conclAlts _)
    (recσX ls gs l i fin [("fieldtype", tyV f)])
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Round6.RefOkB.typedV_n i _ (valsOnly_bind _)) (QuantsOk.cons rfl
        ((Round5.Int.typesB B).final fin _ (valsOnly_bind _))
        (QuantsOk.cons rfl (Round5.Pos.tyT_tyV (B := B) f hb _ (valsOnly_bind _))
          QuantsOk.nil))))
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_case (Sim.evalExp_var rfl))
      (Round6.AgreeSub.evalExp_atomE "ARRAY"))
    (premsB_one (.ifPr (evalExp_recsEqX rfl rfl (evalExp_case (evalExp_tup3
      (evalExp_finalIter rfl fun _ => rfl) (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩)
      (evalExp_case (Sim.evalExp_var rfl)))) hi)))

/-- The value of `SUB final? eps FUNC %(t_1*) -> %(t_2*)` under `recσX`. -/
theorem evalExp_recFuncSubX {ls gs l : List Value} {i : Nat} {fin : Bool} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)} :
    EvalExp (simEnv B)
      (VarEnv.empty.bindVals (recσX ls gs l i fin [("t_1*", tyV ps), ("t_2*", tyV rs)]))
      (.caseE "SUB" (.tupE [.iterE (.varE "final") (.mk .opt [.mk "final" (.varE "final?")]),
        .listE [], .caseE "FUNC%->%" (.tupE [Round6.AgreeOk.resE "t_1", Round6.AgreeOk.resE "t_2"])]))
      (tyV (Silmaril.Wasm.Validation.Ty.sub fin .nil (.func ps rs) : CSubType)) := by
  have hs : EvalExp (simEnv B)
      (VarEnv.empty.bindVals (recσX ls gs l i fin [("t_1*", tyV ps), ("t_2*", tyV rs)]))
      (.caseE "FUNC%->%" (.tupE [Round6.AgreeOk.resE "t_1", Round6.AgreeOk.resE "t_2"]))
      (tyV (Silmaril.Wasm.Validation.Ty.func ps rs)) := by
    rw [tyV, tyV_list, tyV_list]
    exact evalExp_case (evalExp_tup2 (evalExp_resE rfl fun _ => rfl)
      (evalExp_resE rfl fun _ => rfl))
  exact evalExp_case (evalExp_tup3 (evalExp_finalIter rfl fun _ => rfl)
    (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩) hs)

/-- **`Heaptype_sub/rec-func`** in `ctxRX ls gs l`. -/
theorem dd_recFuncX (O : ElseI) {ls gs l : List Value} (hc : CtxT B (ctxRX ls gs l)) {i : Nat}
    {fin : Bool} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)} (hb : tyBnd (Silmaril.Wasm.Validation.Ty.func ps rs) = true)
    (hi : l[i]? = some (tyV (Silmaril.Wasm.Validation.Ty.sub fin .nil (.func ps rs) : CSubType))) :
    HSub B O (ctxRX ls gs l) (tyV (Silmaril.Wasm.Validation.Ty.recv i : CTypeUse)) (absV .func) :=
  have hpr := tyBnd_func' hb
  dderivesB_of_ruleAt ruleAt_recFunc (self_mem_conclAlts _)
    (recσX ls gs l i fin [("t_1*", tyV ps), ("t_2*", tyV rs)])
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Round6.RefOkB.typedV_n i _ (valsOnly_bind _)) (QuantsOk.cons rfl
        ((Round5.Int.typesB B).final fin _ (valsOnly_bind _))
        (QuantsOk.cons rfl ((typedV_tyList hpr.1 fun _ h => h.1) _ (valsOnly_bind _))
          (QuantsOk.cons rfl ((typedV_tyList hpr.2 fun _ h => h.1) _ (valsOnly_bind _))
            QuantsOk.nil)))))
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_case (Sim.evalExp_var rfl))
      (Round6.AgreeSub.evalExp_atomE "FUNC"))
    (premsB_one (.ifPr (evalExp_recsEqX rfl rfl evalExp_recFuncSubX hi)))

/-- **`REC i` is below the kind of a parent-free `RECS[i]`**, in `ctxRX ls gs l`. -/
theorem dd_recKindX (O : ElseI) {ls gs l : List Value} (hc : CtxT B (ctxRX ls gs l)) {i : Nat}
    {fin : Bool} {ct : CCompType} (hb : tyBnd ct = true)
    (hi : l[i]? = some (tyV (Silmaril.Wasm.Validation.Ty.sub fin .nil ct : CSubType))) :
    HSub B O (ctxRX ls gs l) (tyV (Silmaril.Wasm.Validation.Ty.recv i : CTypeUse)) (absV (compAbs ct)) := by
  cases ct with
  | struct fs => exact dd_recStructX O hc hb hi
  | array f => exact dd_recArrayX O hc hb hi
  | func ps rs => exact dd_recFuncX O hc hb hi

/-- The scope of `rec-sub`. -/
def recSubσX (ls gs l : List Value) (i : Nat) (sups : Silmaril.Wasm.Validation.Ty (.list .use)) (j : Nat) (fin : Bool)
    (ct : CCompType) : List (IL.Id × Value) :=
  [("C", ctxRX ls gs l), ("i", natV i), ("typeuse*", tyV sups), ("j", natV j),
    ("final?", finalV fin), ("ct", tyV ct)]

/-- `typeuse*` under `recSubσX`. -/
theorem evalExp_recSubUsesX {env : Env} {ls gs l : List Value} {i : Nat} {sups : Silmaril.Wasm.Validation.Ty (.list .use)}
    {j : Nat} {fin : Bool} {ct : CCompType} :
    EvalExp env (VarEnv.empty.bindVals (recSubσX ls gs l i sups j fin ct)) typeusesE (tyV sups) := by
  have hu := evalExp_iterMap (env := env)
    (ρ := VarEnv.empty.bindVals (recSubσX ls gs l i sups j fin ct))
    (b := .varE "typeuse") (x := "typeuse") (y := "typeuse*") (ws := sups.toList.map tyV)
    (g := fun w => w) (by rw [← tyV_list]; rfl) (fun w _ => Sim.evalExp_var rfl)
  rw [List.map_id', ← tyV_list] at hu
  exact hu

/-- **`Heaptype_sub/rec-sub`** in `ctxRX ls gs l`. -/
theorem dd_recSubX (O : ElseI) {ls gs l : List Value} (hc : CtxT B (ctxRX ls gs l)) {i j : Nat}
    {fin : Bool} {sups : Silmaril.Wasm.Validation.Ty (.list .use)} {ct : CCompType} {u : CTypeUse}
    (hb : tyBnd (Silmaril.Wasm.Validation.Ty.sub fin sups ct : CSubType) = true)
    (hi : l[i]? = some (tyV (Silmaril.Wasm.Validation.Ty.sub fin sups ct : CSubType))) (hj : sups.toList[j]? = some u) :
    HSub B O (ctxRX ls gs l) (tyV (Silmaril.Wasm.Validation.Ty.recv i : CTypeUse)) (tyV u) :=
  have T := Round5.Int.typesB B
  have hb' := tyBnd_sub' hb
  dderivesB_of_ruleAt ruleAt_recSub (self_mem_conclAlts _) (recSubσX ls gs l i sups j fin ct)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Round6.RefOkB.typedV_n i _ (valsOnly_bind _)) (QuantsOk.cons rfl
        (T.typeuses sups hb'.1 _ (valsOnly_bind _)) (QuantsOk.cons rfl
          (Round6.RefOkB.typedV_natT j _ (valsOnly_bind _)) (QuantsOk.cons rfl
            (T.final fin _ (valsOnly_bind _)) (QuantsOk.cons rfl
              (T.comptype ct hb'.2 _ (valsOnly_bind _)) QuantsOk.nil))))))
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_case (Sim.evalExp_var rfl))
      (RefsGC.evalExp_sub_of (RefsGC.evalExp_idx (l := sups.toList.map tyV)
        (tyV_list sups ▸ evalExp_recSubUsesX) (Sim.evalExp_var rfl) (by simp [hj]))))
    (premsB_one (.ifPr (evalExp_recsEqX rfl rfl (evalExp_case (evalExp_tup3
      (evalExp_finalIter rfl fun _ => rfl) evalExp_recSubUsesX (Sim.evalExp_var rfl))) hi)))

/-! ## `$unrollht_` -/

set_option maxRecDepth 100000 in
/-- `REC i` is not a `deftype`. -/
theorem argSubOk_recX (c : Value) (i : Nat) :
    argSubOk (simEnv B) (VarEnv.empty.bindVal "C" c)
      (.subE (.varE "deftype") (.varT "deftype" []) (.varT "heaptype" []))
      (.case "REC" (natV i)) = false := by
  simp only [argSubOk, subCaseOk, VarEnv.findTyp?, VarEnv.bindVal]
  rw [Round5.Pos.findTyp_deftype]
  rfl

/-- **`$unrollht_(C, REC i) = C.RECS[i]`**, in `ctxRX ls gs l`. -/
theorem applies_unrollht_recX {ls gs l : List Value} {i : Nat} {w : Value} (hi : l[i]? = some w) :
    Applies (simEnv B) "unrollht_" [.val (ctxRX ls gs l), .val (tyV (Silmaril.Wasm.Validation.Ty.recv i : CTypeUse))] w := by
  obtain ⟨ps, t, hd⟩ := findDef_unrollht (B := B)
  refine ⟨ps, t, _, hd, Or.inl ?_⟩
  have hs : argSubOk (simEnv B) (VarEnv.empty.bindVal "C" (ctxRX ls gs l))
      (.subE (.varE "deftype") (.varT "deftype" []) (.varT "heaptype" []))
      (.case "REC" (natV i)) = false := argSubOk_recX (B := B) _ i
  refine tryClauses_skip_match (matchArgs_cons_undef_tail (matchArg_expA (matchExp_varE rfl))
    (matchArgs_cons_undef (Silmaril.SpecTec.Equiv.ExecBuiltins.matchArg_expA_undef_of_sub hs)))
    (tryClauses_skip_match (matchArgs_cons_undef_tail (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons_undef (Silmaril.SpecTec.Equiv.ExecBuiltins.matchArg_expA_undef
        (Silmaril.SpecTec.Equiv.ExecBuiltins.matchExp_caseE_undef_of_ne (by decide)))))
      (tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_varE rfl))) matchArgs_nil))
        premsHold_nil (evalExp_idxE_iff.2 ⟨.list l, i, evalExp_dotE_iff.2 ⟨ctxRX ls gs l,
          Sim.evalExp_var rfl, rfl⟩, Sim.evalExp_var rfl, hi⟩)))

set_option maxRecDepth 100000 in
/-- A defined type is a `deftype`. -/
theorem argSubOk_defX (c : Value) (g : CRecType) (k : Nat) :
    argSubOk (simEnv B) (VarEnv.empty.bindVal "C" c)
      (.subE (.varE "deftype") (.varT "deftype" []) (.varT "heaptype" []))
      (tyV (Silmaril.Wasm.Validation.Ty.defn g k : DefType)) = true := by
  simp only [argSubOk, subCaseOk, VarEnv.findTyp?, VarEnv.bindVal, tyV]
  rw [Round5.Pos.findTyp_deftype]
  rfl

/-- **`$unrollht_(C, deftype) = $unrolldt(deftype)`**, for the concrete `B`, in every context. -/
theorem applies_unrollht_dtX {c : Value} {d : DefType} {st : CSubType} (h : unrolldt d = some st) :
    Applies (simEnv (BI P hn host)) "unrollht_" [.val c, .val (tyV d)] (tyV st) := by
  obtain ⟨ps, t, hd⟩ := findDef_unrollht (B := BI P hn host)
  refine ⟨ps, t, _, hd, Or.inl ?_⟩
  cases d with
  | defn g k =>
  exact tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
    (matchArgs_cons (matchArg_expA (Aggregates.matchExp_subE (matchExp_varE rfl))
      (argSubOk_defX c g k)) matchArgs_nil)) premsHold_nil
    (evalExp_callArgs rfl (Equiv.evalArgs_cons (Sim.evalExp_var rfl) (evalArgs_nil _ _))
      ((Prims.applies_unrolldt (prof := P) hn host _ _).2 (by rw [h]; rfl)))

/-! ## `Deftype_ok` -/

/-- The scope of `Deftype_ok` at member `i` of `REC subtype*`, in `ctxRX ls gs l`. -/
def defNσX (ls gs l : List Value) (subs : Silmaril.Wasm.Validation.Ty (.list .sub)) (i : Nat) : List (IL.Id × Value) :=
  [("C", ctxRX ls gs l), ("rectype", tyV (Silmaril.Wasm.Validation.Ty.group subs : CRecType)), ("i", natV i),
    ("n", natV subs.toList.length), ("subtype*", .list (subs.toList.map tyV))]

/-- `subtype^n` under `defNσX`. -/
theorem evalExp_subsNX {ls gs l : List Value} {subs : Silmaril.Wasm.Validation.Ty (.list .sub)} {i : Nat} :
    EvalExp (simEnv B) (VarEnv.empty.bindVals (defNσX ls gs l subs i))
      (.iterE (.varE "subtype") Round6.RefOkB.subsNIt) (.list (subs.toList.map tyV)) := by
  have h := evalExp_iterNMap (env := simEnv B) (ρ := VarEnv.empty.bindVals (defNσX ls gs l subs i))
    (b := .varE "subtype") (x := "subtype") (y := "subtype*") (c := "n")
    (ws := subs.toList.map tyV) (g := fun w => w) (by simp [defNσX, VarEnv.findVal?,
      VarEnv.bindVals, Map.binds, Map.bind, natV]) rfl (fun w _ => Sim.evalExp_var rfl)
  rwa [List.map_id'] at h

set_option linter.unusedSimpArgs false in
/-- **`{RECS subtype^n} ⊕ C` is `ctxRX ls gs (subtype* ++ l)`.** -/
theorem evalExp_recsCtxNX {ls gs l : List Value} {subs : Silmaril.Wasm.Validation.Ty (.list .sub)} {i : Nat} :
    EvalExp (simEnv B) (VarEnv.empty.bindVals (defNσX ls gs l subs i)) Round6.RefOkB.recsCtxE
      (ctxRX ls gs (subs.toList.map tyV ++ l)) := by
  obtain ⟨n, hn⟩ := evalExp_subsNX (B := B) (ls := ls) (gs := gs) (l := l) (subs := subs) (i := i)
  have hn' := evalExp_ok_of_le (show n ≤ n + 2 by omega) hn
  refine evalExp_compE_iff.2 ⟨recsOnlyV (subs.toList.map tyV), ctxRX ls gs l,
    evalExp_strE_iff.2 ⟨_, ⟨n + 3, ?_⟩, rfl⟩, Sim.evalExp_var rfl, ?_⟩
  · simp [evalExpFields, evalExp, evalExps, hn', recsOnlyV]
  · simp [recsOnlyV, ctxRX, Value.comp?, Value.compFields?]

/-- **`Deftype_ok` at any member of any group**, in `ctxRX ls gs l`, from `Rectype_ok2` of the
group under `RECS = subtype* ++ l`. -/
theorem dd_deftypeOkX (O : ElseI) {ls gs l : List Value} (hc : CtxT B (ctxRX ls gs l))
    {subs : Silmaril.Wasm.Validation.Ty (.list .sub)} {i : Nat} (hb : tyBnd (Silmaril.Wasm.Validation.Ty.group subs : CRecType) = true)
    (hi : i < subs.toList.length)
    (hg : DDerivesB (simEnv B) O "Rectype_ok2" "%|-%:%" []
      (.tuple [ctxRX ls gs (subs.toList.map tyV ++ l), tyV (Silmaril.Wasm.Validation.Ty.group subs : CRecType),
        .case "OK" (natV 0)])) :
    DDerivesB (simEnv B) O "Deftype_ok" "%|-%:OK" []
      (.tuple [ctxRX ls gs l, tyV (Silmaril.Wasm.Validation.Ty.defn (.group subs) i : DefType)]) :=
  have hsubs : ∀ w ∈ subs.toList.map tyV, TypedV (simEnv B) (.varT "subtype" []) w :=
    Round5.Pos.tyT_list_of subs (Round5.Pos.tyT_tyV subs (Round5.Pos.tyBnd_group.1 hb).2)
  have hrt : EvalExp (simEnv B) (VarEnv.empty.bindVals (defNσX ls gs l subs i))
      (.caseE "REC" (.caseE "%" (.tupE [.iterE (.varE "subtype") Round6.RefOkB.subsNIt])))
      (tyV (Silmaril.Wasm.Validation.Ty.group subs : CRecType)) := by
    rw [tyV, tyV_list]
    exact evalExp_case (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons evalExp_subsNX
      evalExps_nil, rfl⟩))
  dderivesB_of_ruleAt Round6.RefOkB.ruleAt_deftypeOk (self_mem_conclAlts _) (defNσX ls gs l subs i)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Round5.Pos.tyT_tyV (Silmaril.Wasm.Validation.Ty.group subs : CRecType) hb _ (valsOnly_bind _)) (QuantsOk.cons rfl
        (Round6.RefOkB.typedV_n i _ (valsOnly_bind _)) (QuantsOk.cons rfl
          (Round6.RefOkB.typedV_n _ _ (valsOnly_bind _)) (QuantsOk.cons rfl
            (typedV_list_iff.2 hsubs _ (valsOnly_bind _)) QuantsOk.nil)))))
    (evalExp_tup2 (Sim.evalExp_var rfl) (evalExp_case (evalExp_tup2 (Sim.evalExp_var rfl)
      (Sim.evalExp_var rfl))))
    (Round6.RefOkB.premsB_cons (.rulePr (evalArgs_nil _ _) (evalExp_tup3 evalExp_recsCtxNX
        (Sim.evalExp_var rfl) (evalExp_case (evalExp_numE_iff.2 rfl))) hg) <|
      Round6.RefOkB.premsB_cons (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, Sim.evalExp_var rfl, hrt,
        by simp [cmpValues]⟩)) <|
      Round6.RefOkB.premsB_cons (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, Sim.evalExp_var rfl, Sim.evalExp_var rfl,
        by simp [cmpValues, natV, Num.cmp, hi]⟩)) premsB_nil)

end Silmaril.Wasm.SpecTec.Institution.Instr30W
