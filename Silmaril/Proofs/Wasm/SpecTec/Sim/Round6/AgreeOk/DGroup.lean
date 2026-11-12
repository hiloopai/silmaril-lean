module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.AgreeOk.Funcs

/-!
# Round 6: `Subtype_ok2` with a supertype, and `Deftype_ok`, under `DDerivesB`

Track refokbb proved `Subtype_ok2` without supertypes and `Deftype_ok` at one-member groups.
This file proves the general cases, in any typed context:

* `dd_subtypeOk2One`: **`Subtype_ok2` at a subtype with one declared supertype**, from
  `Typeuse_ok` of the supertype, `$before`, `$unrollht_` (as an `Applies` fact, which
  `Funcs.lean` provides), `Comptype_ok` and `Comptype_sub` against the unrolled supertype;
* `dd_deftypeOk`: **`Deftype_ok` at any member of any group**, from `Rectype_ok2` of the group in
  `{RECS subtype*} ⊕ C`, which is `RefOkB.ctxR (subtype* ++ l)` in `RefOkB.ctxR l`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_list natV finalV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Round6.Reading
open Round6.AgreeSub (CtxT)
open Round4 (tyBnd)

variable {B : Builtins}

/-! ## `Subtype_ok2` with one supertype -/

/-- The scope of `Subtype_ok2` at `SUB fin u ct`, whose supertype unrolls to
`SUB sups' ct'`. -/
def sub1σ (c : Value) (u : CTypeUse) (ct : CCompType) (i : Nat) (ct' : CCompType)
    (sups' : Ty (.list .use)) : List (IL.Id × Value) :=
  [("C", c), ("typeuse*", .list [tyV u]), ("comptype", tyV ct), ("i", natV i),
    ("comptype'*", .list [tyV ct']), ("typeuse'**", .list [tyV sups'])]

/-- A premise iterated over three domains, each bound to a one-element list. -/
theorem dpremB_iter3one {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {pr : Prem}
    {x₁ x₂ x₃ y₁ y₂ y₃ : IL.Id} {w₁ w₂ w₃ : Value}
    (h₁ : ρ.findVal? y₁ = some (.list [w₁])) (h₂ : ρ.findVal? y₂ = some (.list [w₂]))
    (h₃ : ρ.findVal? y₃ = some (.list [w₃]))
    (h : DPremB env O els (ρ.bindVals [(x₁, w₁), (x₂, w₂), (x₃, w₃)]) pr) :
    DPremB env O els ρ
      (.iterPr pr (.mk .list [.mk x₁ (.varE y₁), .mk x₂ (.varE y₂), .mk x₃ (.varE y₃)])) := by
  refine .iterList (k := 1) (xvs := [(x₁, .list [w₁]), (x₂, .list [w₂]), (x₃, .list [w₃])])
    (dls := [(x₁, [w₁]), (x₂, [w₂]), (x₃, [w₃])]) (.inl rfl)
    ⟨2, by simp [evalDoms, domVar, domSrc, evalExp, h₁, h₂, h₃, Res.ofOption]⟩ (by simp)
    (by simp [domLists, Value.asList?]) (by simp) ?_
  intro r hr
  simp only [iterRows, List.range_one, List.map_cons, List.map_nil, List.mem_singleton] at hr
  subst hr
  simpa [iterRow] using h

/-- `$unrollht_(C, typeuse) = SUB ε typeuse'* comptype'` in the row of the supertype. -/
theorem dpremB_unrollht {O : ElseI} {els : Prop} {c : Value} {u : CTypeUse} {ct ct' : CCompType}
    {i : Nat} {sups' : Ty (.list .use)}
    (hun : Applies (simEnv B) "unrollht_" [.val c, .val (tyV u)]
      (tyV (Ty.sub false sups' ct' : CSubType))) :
    DPremB (simEnv B) O els ((VarEnv.empty.bindVals (sub1σ c u ct i ct' sups')).bindVals
      [("comptype'", tyV ct'), ("typeuse", tyV u), ("typeuse'*", tyV sups')])
      (.ifPr (.cmpE .eqOp .boolT (.callE "unrollht_" [.expA (.varE "C"),
        .expA (.subE (.varE "typeuse") (.varT "typeuse" []) (.varT "heaptype" []))])
        (.caseE "SUB" (.tupE [.optE none, .iterE (.varE "typeuse'")
          (.mk .list [.mk "typeuse'" (.varE "typeuse'*")]), .varE "comptype'"])))) := by
  have hit := evalExp_iterMap (env := simEnv B) (b := .varE "typeuse'") (x := "typeuse'")
    (y := "typeuse'*") (ρ := (VarEnv.empty.bindVals (sub1σ c u ct i ct' sups')).bindVals
      [("comptype'", tyV ct'), ("typeuse", tyV u), ("typeuse'*", tyV sups')])
    (ws := sups'.toList.map tyV) (g := fun w => w) (by rw [← tyV_list]; rfl)
    (fun w _ => evalExp_var rfl)
  rw [List.map_id', ← tyV_list] at hit
  exact .ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_callArgs rfl
    (Equiv.evalArgs_cons (evalExp_var rfl) (Equiv.evalArgs_cons
      (RefsGC.evalExp_sub_of (evalExp_var rfl)) (evalArgs_nil _ _))) hun,
    evalExp_case (evalExp_tup3 (evalExp_optE_none_iff.2 rfl) hit (evalExp_var rfl)),
    by simp [cmpValues, tyV, finalV]⟩)

/-- `|typeuse*| ≤ 1` at one supertype. -/
theorem evalExp_usesLe1 {c : Value} {u : CTypeUse} {ct ct' : CCompType} {i : Nat}
    {sups' : Ty (.list .use)} :
    EvalExp (simEnv B) (VarEnv.empty.bindVals (sub1σ c u ct i ct' sups'))
      (.cmpE .leOp (.numT .natT) (.lenE (.iterE (.varE "typeuse") RefOkB.usesIt))
        (.numE (.natN 1))) (.bool true) :=
  evalExp_cmpE_iff.2 ⟨_, _, evalExp_lenE_iff.2 ⟨[tyV u],
    Silmaril.SpecTec.Equiv.Execution.evalExp_iterPat (by decide) rfl, rfl⟩,
    evalExp_numE_iff.2 rfl, by simp [cmpValues, Num.cmp]⟩

/-- The typing of `Subtype_ok2`'s variables at one supertype. -/
theorem quantsOk_sub1σ {c : Value} {u : CTypeUse} {ct ct' : CCompType} {i : Nat}
    {sups' : Ty (.list .use)} (hc : CtxT B c) (hbu : tyBnd u = true) (hbct : tyBnd ct = true)
    (hbct' : tyBnd ct' = true) (hbs : tyBnd sups' = true) :
    QuantsOk (simEnv B) (VarEnv.empty.bindVals (sub1σ c u ct i ct' sups'))
      [.expP "C" (.varT "context" []), .expP "typeuse*" (.iterT (.varT "typeuse" []) .list),
       .expP "comptype" (.varT "comptype" []), .expP "i" (.numT .natT),
       .expP "comptype'*" (.iterT (.varT "comptype" []) .list),
       .expP "typeuse'**" (.iterT (.iterT (.varT "typeuse" []) .list) .list)] :=
  have T := Round5.Int.typesB B
  have hu : TypedV (simEnv B) (.varT "typeuse" []) (tyV u) := (Round5.Pos.tyT_tyV u hbu).1
  have hs : TypedV (simEnv B) (.iterT (.varT "typeuse" []) .list) (tyV sups') := T.typeuses _ hbs
  QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
    (typedV_list_iff.2 (fun _ hw => List.mem_singleton.1 hw ▸ hu) _ (valsOnly_bind _))
    (QuantsOk.cons rfl (T.comptype ct hbct _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (RefOkB.typedV_natT i _ (valsOnly_bind _)) (QuantsOk.cons rfl
        (typedV_list_iff.2 (fun _ hw => List.mem_singleton.1 hw ▸ T.comptype ct' hbct')
          _ (valsOnly_bind _)) (QuantsOk.cons rfl
        (typedV_list_iff.2 (fun _ hw => List.mem_singleton.1 hw ▸ hs) _ (valsOnly_bind _))
          QuantsOk.nil)))))

/-- **`Subtype_ok2` at a subtype with one declared supertype.** -/
theorem dd_subtypeOk2One (O : ElseI) {c : Value} (hc : CtxT B c) (fin : Bool) (i : Nat)
    {u : CTypeUse} {ct ct' : CCompType} {sups' : Ty (.list .use)}
    (hbu : tyBnd u = true) (hbct : tyBnd ct = true) (hbct' : tyBnd ct' = true)
    (hbs : tyBnd sups' = true) (hb : before u i = true)
    (hun : Applies (simEnv B) "unrollht_" [.val c, .val (tyV u)]
      (tyV (Ty.sub false sups' ct' : CSubType)))
    (hu : DDerivesB (simEnv B) O "Typeuse_ok" "%|-%:OK" [] (.tuple [c, tyV u]))
    (hct : DDerivesB (simEnv B) O "Comptype_ok" "%|-%:OK" [] (.tuple [c, tyV ct]))
    (hsub : DDerivesB (simEnv B) O "Comptype_sub" "%|-%<:%" [] (.tuple [c, tyV ct, tyV ct'])) :
    DDerivesB (simEnv B) O "Subtype_ok2" "%|-%:%" []
      (.tuple [c, tyV (Ty.sub fin (.cons u .nil) ct : CSubType), .case "OK" (natV i)]) :=
  dderivesB_of_ruleAt RefOkB.ruleAt_subtypeOk2 (conclAlts_subtypeOk2 fin) (sub1σ c u ct i ct' sups')
    (quantsOk_sub1σ hc hbu hbct hbct' hbs)
    (evalExp_tup3 (evalExp_var rfl) (evalExp_case (evalExp_tup3 (evalExp_atomOptE "FINAL" fin)
      (Silmaril.SpecTec.Equiv.Execution.evalExp_iterPat (by decide) rfl) (evalExp_var rfl)))
      (evalExp_case (evalExp_var rfl)))
    (RefOkB.premsB_cons (.ifPr evalExp_usesLe1) <|
      RefOkB.premsB_cons (dpremB_iter1 rfl fun w hw => by
        rw [List.mem_singleton.1 hw]
        exact .rulePr (evalArgs_nil _ _) (evalExp_tup2 (evalExp_var rfl) (evalExp_var rfl)) hu) <|
      RefOkB.premsB_cons (dpremB_iter1 rfl fun w hw => by
        rw [List.mem_singleton.1 hw]
        exact .ifPr (evalExp_callArgs rfl (Equiv.evalArgs_cons (evalExp_var rfl)
          (Equiv.evalArgs_cons (evalExp_var rfl) (evalArgs_nil _ _))) (applies_before hb))) <|
      RefOkB.premsB_cons (dpremB_iter3one rfl rfl rfl (dpremB_unrollht hun)) <|
      RefOkB.premsB_cons (.rulePr (evalArgs_nil _ _)
        (evalExp_tup2 (evalExp_var rfl) (evalExp_var rfl)) hct) <|
      RefOkB.premsB_cons (dpremB_iter1 rfl fun w hw => by
        rw [List.mem_singleton.1 hw]
        exact .rulePr (evalArgs_nil _ _)
          (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl)) hsub) premsB_nil)

/-! ## `Deftype_ok` -/

/-- The scope of `Deftype_ok` at member `i` of `REC subtype*`. -/
def defNσ (l : List Value) (subs : Ty (.list .sub)) (i : Nat) : List (IL.Id × Value) :=
  [("C", RefOkB.ctxR l), ("rectype", tyV (Ty.group subs : CRecType)), ("i", natV i),
    ("n", natV subs.toList.length), ("subtype*", .list (subs.toList.map tyV))]

/-- `subtype^n` under `defNσ`. -/
theorem evalExp_subsN {l : List Value} {subs : Ty (.list .sub)} {i : Nat} :
    EvalExp (simEnv B) (VarEnv.empty.bindVals (defNσ l subs i))
      (.iterE (.varE "subtype") RefOkB.subsNIt) (.list (subs.toList.map tyV)) := by
  have h := evalExp_iterNMap (env := simEnv B) (ρ := VarEnv.empty.bindVals (defNσ l subs i))
    (b := .varE "subtype") (x := "subtype") (y := "subtype*") (c := "n")
    (ws := subs.toList.map tyV) (g := fun w => w) (by simp [defNσ, VarEnv.findVal?,
      VarEnv.bindVals, Map.binds, Map.bind, natV]) rfl (fun w _ => evalExp_var rfl)
  rwa [List.map_id'] at h

/-- The record `{RECS sts}` of `Deftype_ok`'s premise, with every other field empty. -/
def recsOnlyV (sts : List Value) : Value :=
  .struct [("TYPES", .list []), ("TAGS", .list []), ("GLOBALS", .list []), ("MEMS", .list []),
    ("TABLES", .list []), ("FUNCS", .list []), ("DATAS", .list []), ("ELEMS", .list []),
    ("LOCALS", .list []), ("LABELS", .list []), ("RETURN", .opt none), ("REFS", .list []),
    ("RECS", .list sts)]

set_option linter.unusedSimpArgs false in
/-- **`{RECS subtype^n} ⊕ C` is `RefOkB.ctxR (subtype* ++ l)`.** -/
theorem evalExp_recsCtxN {l : List Value} {subs : Ty (.list .sub)} {i : Nat} :
    EvalExp (simEnv B) (VarEnv.empty.bindVals (defNσ l subs i)) RefOkB.recsCtxE
      (RefOkB.ctxR (subs.toList.map tyV ++ l)) := by
  obtain ⟨n, hn⟩ := evalExp_subsN (B := B) (l := l) (subs := subs) (i := i)
  have hn' := evalExp_ok_of_le (show n ≤ n + 2 by omega) hn
  refine evalExp_compE_iff.2 ⟨recsOnlyV (subs.toList.map tyV), RefOkB.ctxR l,
    evalExp_strE_iff.2 ⟨_, ⟨n + 3, ?_⟩, rfl⟩, evalExp_var rfl, ?_⟩
  · simp [evalExpFields, evalExp, evalExps, hn', recsOnlyV]
  · simp [recsOnlyV, RefOkB.ctxR, Value.comp?, Value.compFields?]

/-- **`Deftype_ok` at any member of any group**, from `Rectype_ok2` of the group under
`RECS = subtype* ++ C.RECS`. -/
theorem dd_deftypeOk (O : ElseI) {l : List Value} (hc : CtxT B (RefOkB.ctxR l))
    {subs : Ty (.list .sub)} {i : Nat} (hb : tyBnd (Ty.group subs : CRecType) = true)
    (hi : i < subs.toList.length)
    (hg : DDerivesB (simEnv B) O "Rectype_ok2" "%|-%:%" []
      (.tuple [RefOkB.ctxR (subs.toList.map tyV ++ l), tyV (Ty.group subs : CRecType),
        .case "OK" (natV 0)])) :
    DDerivesB (simEnv B) O "Deftype_ok" "%|-%:OK" []
      (.tuple [RefOkB.ctxR l, tyV (Ty.defn (.group subs) i : DefType)]) :=
  have hsubs : ∀ w ∈ subs.toList.map tyV, TypedV (simEnv B) (.varT "subtype" []) w :=
    Round5.Pos.tyT_list_of subs (Round5.Pos.tyT_tyV subs (Round5.Pos.tyBnd_group.1 hb).2)
  have hrt : EvalExp (simEnv B) (VarEnv.empty.bindVals (defNσ l subs i))
      (.caseE "REC" (.caseE "%" (.tupE [.iterE (.varE "subtype") RefOkB.subsNIt])))
      (tyV (Ty.group subs : CRecType)) := by
    rw [tyV, tyV_list]
    exact evalExp_case (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons evalExp_subsN
      evalExps_nil, rfl⟩))
  dderivesB_of_ruleAt RefOkB.ruleAt_deftypeOk (self_mem_conclAlts _) (defNσ l subs i)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Round5.Pos.tyT_tyV (Ty.group subs : CRecType) hb _ (valsOnly_bind _)) (QuantsOk.cons rfl
        (RefOkB.typedV_n i _ (valsOnly_bind _)) (QuantsOk.cons rfl
          (RefOkB.typedV_n _ _ (valsOnly_bind _)) (QuantsOk.cons rfl
            (typedV_list_iff.2 hsubs _ (valsOnly_bind _)) QuantsOk.nil)))))
    (evalExp_tup2 (evalExp_var rfl) (evalExp_case (evalExp_tup2 (evalExp_var rfl)
      (evalExp_var rfl))))
    (RefOkB.premsB_cons (.rulePr (evalArgs_nil _ _) (evalExp_tup3 evalExp_recsCtxN
        (evalExp_var rfl) (evalExp_case (evalExp_numE_iff.2 rfl))) hg) <|
      RefOkB.premsB_cons (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_var rfl, hrt,
        by simp [cmpValues]⟩)) <|
      RefOkB.premsB_cons (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_var rfl, evalExp_var rfl,
        by simp [cmpValues, natV, Num.cmp, hi]⟩)) premsB_nil)

end Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk
