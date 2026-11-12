module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.RefOkB.Rules

/-!
# Round 6: the validation rules, under `DDerivesB`, one rule at a time

Each lemma fires one rule of the validation group under `DDerivesB`, from typed arguments and
derivations of its premises, under every reading of `otherwise`:

* `dderivesB_heaptypeOkUse`, `dderivesB_typeuseOkDef`, `dderivesB_valtypeOkRef`,
  `dderivesB_storagetypeOkVal`: the subsumption rules;
* `dderivesB_typeuseOkRec`: `REC i` is valid when `C.RECS[i]` is a subtype;
* `dderivesB_comptypeOkStruct1`: a one-field structure type;
* `dderivesB_subtypeOk2`: a subtype without declared supertypes, at both finalities (the
  `FINAL?` of its conclusion, read through `conclAlts`);
* `dderivesB_rectypeOk2Empty`, `dderivesB_rectypeOk2Cons`;
* `dderivesB_deftypeOk1`: a one-member group, checked under `{RECS st} ⊕ C`, whose `RECS` is
  `st :: C.RECS` (`ctxR`).

Contexts here are `ctxR l`: the empty context with `RECS = l`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (natV finalV)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading

variable {B : Builtins}

/-- The empty context with `RECS = l`. -/
def ctxR (l : List Value) : Value :=
  .struct [("TYPES", .list []), ("TAGS", .list []), ("GLOBALS", .list []), ("MEMS", .list []),
    ("TABLES", .list []), ("FUNCS", .list []), ("DATAS", .list []), ("ELEMS", .list []),
    ("LOCALS", .list []), ("LABELS", .list []), ("RETURN", .opt none), ("REFS", .list []),
    ("RECS", .list l)]

/-- `{}` is `ctxR []`. -/
theorem ctx0V_eq : ctx0V = ctxR [] := rfl

/-- **`ctxR l` is a typed `context`** when every member of `l` is a typed `subtype`. -/
theorem typedV_ctxR {l : List Value}
    (hl : ∀ u ∈ l, TypedV (simEnv B) (.varT "subtype" []) u) :
    TypedV (simEnv B) (.varT "context" []) (ctxR l) :=
  have hn : TypedV (simEnv B) (.iterT (.varT "resulttype" []) .opt) (.opt none) :=
    fun _ _ => hasTyp_iterT_opt_iff.2 (.inl rfl)
  have h0 {t : Typ} : TypedV (simEnv B) (.iterT t .list) (.list []) := Round5.RefOk.typedV_listNil
  Round5.Pos.typedV_struct findTyp_context <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of hn <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_one (typedV_list_iff.2 hl)

/-- A natural number is a `nat`. -/
theorem typedV_natT (i : Nat) : TypedV (simEnv B) (.numT .natT) (natV i) :=
  fun _ _ => hasTyp_numT_iff.2 ⟨_, rfl, by simp [Num.subTyp, Num.toTyp]⟩

/-- A natural number is an `n`. -/
theorem typedV_n (i : Nat) : TypedV (simEnv B) (.varT "n" []) (natV i) :=
  (Typing.stateTyping_simEnv B).nat i

/-- One more premise, under the new reading. -/
theorem premsB_cons {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {p : Prem} {ps : List Prem}
    (h : DPremB env O els ρ p) (hs : ∀ q ∈ ps, DPremB env O els ρ q) :
    ∀ q ∈ p :: ps, DPremB env O els ρ q := fun q hq =>
  (List.mem_cons.1 hq).elim (fun e => e ▸ h) (hs q)

/-- Two premises, under the new reading. -/
theorem premsB_two {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {p₁ p₂ : Prem}
    (h₁ : DPremB env O els ρ p₁) (h₂ : DPremB env O els ρ p₂) :
    ∀ p ∈ [p₁, p₂], DPremB env O els ρ p := by
  intro p hp
  rcases List.mem_pair.1 hp with rfl | rfl
  · exact h₁
  · exact h₂

/-! ## The subsumption rules -/

/-- **`Heaptype_ok/typeuse`.** -/
theorem dderivesB_heaptypeOkUse (O : ElseI) {c u : Value}
    (hc : TypedV (simEnv B) (.varT "context" []) c)
    (hu : TypedV (simEnv B) (.varT "typeuse" []) u)
    (hd : DDerivesB (simEnv B) O "Typeuse_ok" "%|-%:OK" [] (.tuple [c, u])) :
    DDerivesB (simEnv B) O "Heaptype_ok" "%|-%:OK" [] (.tuple [c, u]) :=
  dderivesB_of_ruleAt ruleAt_heaptypeOkUse (self_mem_conclAlts _) [("C", c), ("typeuse", u)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (hu _ (valsOnly_bind _))
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_var rfl) (RefsGC.evalExp_sub_of (evalExp_var rfl)))
    (premsB_one (.rulePr (evalArgs_nil _ _) (evalExp_tup2 (evalExp_var rfl) (evalExp_var rfl)) hd))

/-- **`Typeuse_ok/deftype`.** -/
theorem dderivesB_typeuseOkDef (O : ElseI) {c d : Value}
    (hc : TypedV (simEnv B) (.varT "context" []) c)
    (hdt : TypedV (simEnv B) (.varT "deftype" []) d)
    (hd : DDerivesB (simEnv B) O "Deftype_ok" "%|-%:OK" [] (.tuple [c, d])) :
    DDerivesB (simEnv B) O "Typeuse_ok" "%|-%:OK" [] (.tuple [c, d]) :=
  dderivesB_of_ruleAt ruleAt_typeuseOkDef (self_mem_conclAlts _) [("C", c), ("deftype", d)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (hdt _ (valsOnly_bind _))
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_var rfl) (RefsGC.evalExp_sub_of (evalExp_var rfl)))
    (premsB_one (.rulePr (evalArgs_nil _ _) (evalExp_tup2 (evalExp_var rfl) (evalExp_var rfl)) hd))

/-- **`Valtype_ok/ref`.** -/
theorem dderivesB_valtypeOkRef (O : ElseI) {c r : Value}
    (hc : TypedV (simEnv B) (.varT "context" []) c)
    (hr : TypedV (simEnv B) (.varT "reftype" []) r)
    (hd : DDerivesB (simEnv B) O "Reftype_ok" "%|-%:OK" [] (.tuple [c, r])) :
    DDerivesB (simEnv B) O "Valtype_ok" "%|-%:OK" [] (.tuple [c, r]) :=
  dderivesB_of_ruleAt ruleAt_valtypeOkRef (self_mem_conclAlts _) [("C", c), ("reftype", r)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (hr _ (valsOnly_bind _))
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_var rfl) (RefsGC.evalExp_sub_of (evalExp_var rfl)))
    (premsB_one (.rulePr (evalArgs_nil _ _) (evalExp_tup2 (evalExp_var rfl) (evalExp_var rfl)) hd))

/-- **`Storagetype_ok/val`.** -/
theorem dderivesB_storagetypeOkVal (O : ElseI) {c t : Value}
    (hc : TypedV (simEnv B) (.varT "context" []) c)
    (ht : TypedV (simEnv B) (.varT "valtype" []) t)
    (hd : DDerivesB (simEnv B) O "Valtype_ok" "%|-%:OK" [] (.tuple [c, t])) :
    DDerivesB (simEnv B) O "Storagetype_ok" "%|-%:OK" [] (.tuple [c, t]) :=
  dderivesB_of_ruleAt ruleAt_storagetypeOkVal (self_mem_conclAlts _) [("C", c), ("valtype", t)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (ht _ (valsOnly_bind _))
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_var rfl) (RefsGC.evalExp_sub_of (evalExp_var rfl)))
    (premsB_one (.rulePr (evalArgs_nil _ _) (evalExp_tup2 (evalExp_var rfl) (evalExp_var rfl)) hd))

/-! ## `REC i` -/

/-- `C.RECS[i] = st` evaluates to `true` in a context `ctxR l` with `l[i]? = some st`. -/
theorem evalExp_recsIdx {ρ : VarEnv} {l : List Value} {i : Nat} {st : Value}
    (hC : ρ.findVal? "C" = some (ctxR l)) (hI : ρ.findVal? "i" = some (natV i))
    (hS : ρ.findVal? "st" = some st) (hi : l[i]? = some st) :
    EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT (.idxE (.dotE (.varE "C") "RECS") (.varE "i"))
      (.varE "st")) (.bool true) :=
  evalExp_cmpE_iff.2 ⟨st, st, evalExp_idxE_iff.2 ⟨.list l, i,
    evalExp_dotE_iff.2 ⟨ctxR l, evalExp_var hC, rfl⟩, evalExp_var hI, hi⟩,
    evalExp_var hS, by simp [cmpValues]⟩

/-- **`Typeuse_ok/rec`**: `REC i` is valid in `ctxR l` when `l[i]` is a typed subtype. -/
theorem dderivesB_typeuseOkRec (O : ElseI) {l : List Value} {i : Nat} {st : Value}
    (hc : TypedV (simEnv B) (.varT "context" []) (ctxR l))
    (hst : TypedV (simEnv B) (.varT "subtype" []) st) (hi : l[i]? = some st) :
    DDerivesB (simEnv B) O "Typeuse_ok" "%|-%:OK" [] (.tuple [ctxR l, .case "REC" (natV i)]) :=
  dderivesB_of_ruleAt ruleAt_typeuseOkRec (self_mem_conclAlts _)
    [("C", ctxR l), ("i", natV i), ("st", st)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_n i _ (valsOnly_bind _)) (QuantsOk.cons rfl (hst _ (valsOnly_bind _))
        QuantsOk.nil)))
    (evalExp_tup2 (evalExp_var rfl) (evalExp_case (evalExp_var rfl)))
    (premsB_one (.ifPr (evalExp_recsIdx rfl rfl rfl hi)))

/-! ## One-field structures -/

/-- The scope of `Comptype_ok/struct` at a one-field structure. -/
def structσ (c f : Value) : List (IL.Id × Value) := [("C", c), ("fieldtype*", .list [f])]

/-- `Comptype_ok/struct`'s iterated premise, at one field. -/
theorem dpremB_fieldsOne (O : ElseI) {els : Prop} {c f : Value}
    (hd : DDerivesB (simEnv B) O "Fieldtype_ok" "%|-%:OK" [] (.tuple [c, f])) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals (structσ c f))
      (.iterPr (.rulePr "Fieldtype_ok" [] "%|-%:OK" (.tupE [.varE "C", .varE "fieldtype"]))
        fieldsIt) := by
  refine .iterList (k := 1) (xvs := [("fieldtype", .list [f])]) (dls := [("fieldtype", [f])])
    (.inl rfl)
    ⟨2, by simp [evalDoms, domVar, domSrc, evalExp, structσ, VarEnv.findVal?, VarEnv.bindVals,
      Map.binds, Map.bind]⟩ (by simp) (by simp [domLists, Value.asList?]) (by simp) ?_
  intro r hr
  simp only [iterRows, List.range_one, List.map_cons, List.map_nil, List.mem_singleton] at hr
  subst hr
  exact .rulePr (evalArgs_nil _ _) (evalExp_tup2 (evalExp_var (by
      simp [iterRow, structσ, VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind]))
    (evalExp_var (by simp [iterRow, VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind]))) hd

/-- **`Comptype_ok/struct`, at one field.** -/
theorem dderivesB_comptypeOkStruct1 (O : ElseI) {c f : Value}
    (hc : TypedV (simEnv B) (.varT "context" []) c)
    (hf : TypedV (simEnv B) (.varT "fieldtype" []) f)
    (hd : DDerivesB (simEnv B) O "Fieldtype_ok" "%|-%:OK" [] (.tuple [c, f])) :
    DDerivesB (simEnv B) O "Comptype_ok" "%|-%:OK" []
      (.tuple [c, .case "STRUCT" (.case "%" (.tuple [.list [f]]))]) :=
  dderivesB_of_ruleAt ruleAt_comptypeOkStruct (self_mem_conclAlts _) (structσ c f)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_list_iff.2 (fun u hu => by rw [List.mem_singleton.1 hu]; exact hf) _
        (valsOnly_bind _)) QuantsOk.nil))
    (evalExp_tup2 (evalExp_var rfl) (evalExp_case (evalExp_case (evalExp_tupE_iff.2
      ⟨[.list [f]], evalExps_cons (Silmaril.SpecTec.Equiv.Execution.evalExp_iterPat
        (by decide) rfl) evalExps_nil, rfl⟩))))
    (premsB_one (dpremB_fieldsOne O hd))

/-! ## Subtypes without supertypes -/

/-- The scope of `Subtype_ok2` at a subtype without declared supertypes. -/
def subσ (c ct : Value) (i : Nat) : List (IL.Id × Value) :=
  [("C", c), ("typeuse*", .list []), ("comptype", ct), ("i", natV i), ("comptype'*", .list []),
    ("typeuse'**", .list [])]

/-- Empty domain values read as empty lists. -/
theorem domLists_nil : ∀ ds : List Dom,
    domLists (ds.map fun d => (domVar d, Value.list [])) = some (ds.map fun d => (domVar d, []))
  | [] => rfl
  | d :: ds => by
    have ih := domLists_nil ds
    simp only [domLists, List.map_cons, List.mapM_cons] at ih ⊢
    rw [ih]
    rfl

/-- An iterated premise over empty domains holds. -/
theorem dpremB_iterNil (O : ElseI) {els : Prop} {c ct : Value} {i : Nat} {pr : Prem}
    {ds : List Dom} (hds : ds ≠ [])
    (hdoms : EvalDoms (simEnv B) (VarEnv.empty.bindVals (subσ c ct i)) ds
      (ds.map fun d => (domVar d, .list []))) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals (subσ c ct i)) (.iterPr pr (.mk .list ds)) :=
  .iterList (k := 0) (dls := ds.map fun d => (domVar d, [])) (.inl rfl) hdoms hds
    (domLists_nil ds) (by simp) (by simp [iterRows])

/-- Domains whose sources all evaluate to `[]`. -/
theorem mapM_doms_nil {ρ : VarEnv} : ∀ ds : List Dom,
    (∀ d ∈ ds, evalExp 1 (simEnv B) ρ (domSrc d) = .ok (.list [])) →
    ds.mapM (fun d => (fun v => (domVar d, v)) <$> evalExp 1 (simEnv B) ρ (domSrc d)) =
      .ok (ds.map fun d => (domVar d, .list []))
  | [], _ => rfl
  | d :: ds, h => by
    have h₁ : evalExp 1 (simEnv B) ρ (domSrc d) = .ok (.list []) := h d List.mem_cons_self
    have h₂ := mapM_doms_nil ds fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    simp [List.mapM_cons, h₁, h₂]

/-- The domains of an iteration of `Subtype_ok2`, all bound to `[]`, evaluate. -/
theorem evalDoms_subσ {c ct : Value} {i : Nat} {ds : List Dom}
    (hds : ∀ d ∈ ds, ∃ y, domSrc d = .varE y ∧
      (VarEnv.empty.bindVals (subσ c ct i)).findVal? y = some (.list [])) :
    EvalDoms (simEnv B) (VarEnv.empty.bindVals (subσ c ct i)) ds
      (ds.map fun d => (domVar d, .list [])) := by
  have hall : ∀ d ∈ ds, evalExp 1 (simEnv B) (VarEnv.empty.bindVals (subσ c ct i)) (domSrc d) =
      .ok (.list []) := fun d hd => by
    obtain ⟨y, hy, hv⟩ := hds d hd
    simp [hy, evalExp, hv, Res.ofOption]
  refine ⟨2, ?_⟩
  simp only [evalDoms]
  exact mapM_doms_nil ds hall

set_option linter.unusedSimpArgs false in
/-- `|typeuse*| ≤ 1`, at `typeuse* = []`. -/
theorem evalExp_usesLe {c ct : Value} {i : Nat} :
    EvalExp (simEnv B) (VarEnv.empty.bindVals (subσ c ct i))
      (.cmpE .leOp (.numT .natT) (.lenE (.iterE (.varE "typeuse") usesIt)) (.numE (.natN 1)))
      (.bool true) :=
  ⟨6, by simp [evalExp, evalIterE, evalIterList, evalRounds, evalDoms, usesIt, domVar, domSrc,
    subσ, VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, iterRows, Value.asList?,
    Value.len?, cmpValues, Num.cmp]⟩

/-- An iteration over `typeuse*` holds vacuously. -/
theorem dpremB_usesIt (O : ElseI) {els : Prop} {c ct : Value} {i : Nat} (pr : Prem) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals (subσ c ct i)) (.iterPr pr usesIt) :=
  dpremB_iterNil O (by simp) (evalDoms_subσ (by simp [domSrc, subσ, VarEnv.findVal?,
    VarEnv.bindVals, Map.binds, Map.bind]))

/-- The `$unrollht_` iteration holds vacuously. -/
theorem dpremB_unrollIt (O : ElseI) {els : Prop} {c ct : Value} {i : Nat} (pr : Prem) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals (subσ c ct i)) (.iterPr pr unrollIt) :=
  dpremB_iterNil O (by simp) (evalDoms_subσ (by simp [domSrc, subσ, VarEnv.findVal?,
    VarEnv.bindVals, Map.binds, Map.bind]))

/-- An iteration over `comptype'*` holds vacuously. -/
theorem dpremB_supsIt (O : ElseI) {els : Prop} {c ct : Value} {i : Nat} (pr : Prem) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals (subσ c ct i)) (.iterPr pr supsIt) :=
  dpremB_iterNil O (by simp) (evalDoms_subσ (by simp [domSrc, subσ, VarEnv.findVal?,
    VarEnv.bindVals, Map.binds, Map.bind]))

/-- The typing of `Subtype_ok2`'s variables, at a subtype without supertypes. -/
theorem quantsOk_subσ {c ct : Value} (i : Nat) (hc : TypedV (simEnv B) (.varT "context" []) c)
    (hct : TypedV (simEnv B) (.varT "comptype" []) ct) :
    QuantsOk (simEnv B) (VarEnv.empty.bindVals (subσ c ct i)) [.expP "C" (.varT "context" []),
      .expP "typeuse*" (.iterT (.varT "typeuse" []) .list),
      .expP "comptype" (.varT "comptype" []), .expP "i" (.numT .natT),
      .expP "comptype'*" (.iterT (.varT "comptype" []) .list),
      .expP "typeuse'**" (.iterT (.iterT (.varT "typeuse" []) .list) .list)] :=
  have h0 {t : Typ} : TypedV (simEnv B) (.iterT t .list) (.list []) := Round5.RefOk.typedV_listNil
  QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (h0 _ (valsOnly_bind _))
    (QuantsOk.cons rfl (hct _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_natT i _ (valsOnly_bind _)) (QuantsOk.cons rfl (h0 _ (valsOnly_bind _))
        (QuantsOk.cons rfl (h0 _ (valsOnly_bind _)) QuantsOk.nil)))))

/-- **`Subtype_ok2`, without declared supertypes**, at both finalities: from `Comptype_ok`. -/
theorem dderivesB_subtypeOk2 (O : ElseI) {c ct : Value} (fin : Bool) (i : Nat)
    (hc : TypedV (simEnv B) (.varT "context" []) c)
    (hct : TypedV (simEnv B) (.varT "comptype" []) ct)
    (hd : DDerivesB (simEnv B) O "Comptype_ok" "%|-%:OK" [] (.tuple [c, ct])) :
    DDerivesB (simEnv B) O "Subtype_ok2" "%|-%:%" []
      (.tuple [c, .case "SUB" (.tuple [finalV fin, .list [], ct]), .case "OK" (natV i)]) :=
  dderivesB_of_ruleAt ruleAt_subtypeOk2 (conclAlts_subtypeOk2 fin) (subσ c ct i)
    (quantsOk_subσ i hc hct)
    (evalExp_tup3 (evalExp_var rfl) (evalExp_case (evalExp_tup3 (evalExp_atomOptE "FINAL" fin)
      (Silmaril.SpecTec.Equiv.Execution.evalExp_iterPat (by decide) rfl) (evalExp_var rfl)))
      (evalExp_case (evalExp_var rfl)))
    (premsB_cons (.ifPr evalExp_usesLe) <| premsB_cons (dpremB_usesIt O _) <|
      premsB_cons (dpremB_usesIt O _) <| premsB_cons (dpremB_unrollIt O _) <|
      premsB_cons (.rulePr (evalArgs_nil _ _) (evalExp_tup2 (evalExp_var rfl) (evalExp_var rfl)) hd) <|
      premsB_cons (dpremB_supsIt O _) premsB_nil)

/-! ## Recursive groups -/

/-- **`Rectype_ok2/empty`.** -/
theorem dderivesB_rectypeOk2Empty (O : ElseI) {c : Value} (i : Nat)
    (hc : TypedV (simEnv B) (.varT "context" []) c) :
    DDerivesB (simEnv B) O "Rectype_ok2" "%|-%:%" []
      (.tuple [c, .case "REC" (.case "%" (.tuple [.list []])), .case "OK" (natV i)]) :=
  dderivesB_of_ruleAt ruleAt_rectypeOk2Empty (self_mem_conclAlts _) [("C", c), ("i", natV i)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_natT i _ (valsOnly_bind _)) QuantsOk.nil))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_case (evalExp_case (evalExp_tupE_iff.2
      ⟨[.list []], evalExps_cons (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩) evalExps_nil,
        rfl⟩))) (evalExp_case (evalExp_var rfl)))
    premsB_nil

/-- The scope of `Rectype_ok2/cons`. -/
def consσ (c st : Value) (sts : List Value) (i : Nat) : List (IL.Id × Value) :=
  [("C", c), ("subtype_1", st), ("subtype*", .list sts), ("i", natV i)]

set_option linter.unusedSimpArgs false in
/-- **`Rectype_ok2/cons`.** -/
theorem dderivesB_rectypeOk2Cons (O : ElseI) {c st : Value} {sts : List Value} (i : Nat)
    (hc : TypedV (simEnv B) (.varT "context" []) c)
    (hst : TypedV (simEnv B) (.varT "subtype" []) st)
    (hsts : ∀ u ∈ sts, TypedV (simEnv B) (.varT "subtype" []) u)
    (h₁ : DDerivesB (simEnv B) O "Subtype_ok2" "%|-%:%" [] (.tuple [c, st, .case "OK" (natV i)]))
    (h₂ : DDerivesB (simEnv B) O "Rectype_ok2" "%|-%:%" []
      (.tuple [c, .case "REC" (.case "%" (.tuple [.list sts])), .case "OK" (natV (i + 1))])) :
    DDerivesB (simEnv B) O "Rectype_ok2" "%|-%:%" []
      (.tuple [c, .case "REC" (.case "%" (.tuple [.list (st :: sts)])), .case "OK" (natV i)]) :=
  have hit : EvalExp (simEnv B) (VarEnv.empty.bindVals (consσ c st sts i))
      (.iterE (.varE "subtype") subsIt) (.list sts) :=
    Silmaril.SpecTec.Equiv.Execution.evalExp_iterPat (by decide) rfl
  dderivesB_of_ruleAt ruleAt_rectypeOk2Cons (self_mem_conclAlts _) (consσ c st sts i)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (hst _ (valsOnly_bind _))
      (QuantsOk.cons rfl (typedV_list_iff.2 hsts _ (valsOnly_bind _)) (QuantsOk.cons rfl
        (typedV_natT i _ (valsOnly_bind _)) QuantsOk.nil))))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_case (evalExp_case (evalExp_tupE_iff.2
      ⟨[.list (st :: sts)], evalExps_cons (evalExp_catE_iff.2 ⟨.list [st], .list sts,
        evalExp_listE_iff.2 ⟨[st], evalExps_cons (evalExp_var rfl) evalExps_nil, rfl⟩, hit,
        rfl⟩) evalExps_nil, rfl⟩))) (evalExp_case (evalExp_var rfl)))
    (premsB_two
      (.rulePr (evalArgs_nil _ _) (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl)
        (evalExp_case (evalExp_var rfl))) h₁)
      (.rulePr (evalArgs_nil _ _) (evalExp_tup3 (evalExp_var rfl) (evalExp_case (evalExp_case
        (evalExp_tupE_iff.2 ⟨[.list sts], evalExps_cons hit evalExps_nil, rfl⟩)))
        (evalExp_case ⟨3, by simp [evalExp, consσ, VarEnv.findVal?, VarEnv.bindVals, Map.binds,
          Map.bind, natV, binValues, boolShort, Num.bin]⟩)) h₂))

/-! ## One-member groups -/

/-- The scope of `Deftype_ok` at a one-member group. -/
def defσ (l : List Value) (st : Value) : List (IL.Id × Value) :=
  [("C", ctxR l), ("rectype", .case "REC" (.case "%" (.tuple [.list [st]]))), ("i", natV 0),
    ("n", natV 1), ("subtype*", .list [st])]

set_option linter.unusedSimpArgs false in
/-- `{RECS st} ⊕ ctxR l` is `ctxR (st :: l)`. -/
theorem evalExp_recsCtx {l : List Value} {st : Value} :
    EvalExp (simEnv B) (VarEnv.empty.bindVals (defσ l st)) recsCtxE (ctxR (st :: l)) :=
  ⟨10, by simp [recsCtxE, subsNIt, ctxR, defσ, evalExp, evalExps, evalExpFields, evalIterE,
    evalIterList, evalRounds, evalDoms, iterRows, iterRow, domVar, domSrc, VarEnv.findVal?,
    VarEnv.bindVals, Map.binds, Map.bind, Value.comp?, Value.compFields?, natV, Value.asNat?]⟩

set_option linter.unusedSimpArgs false in
/-- `rectype = REC subtype^n`. -/
theorem evalExp_rectypeEq {l : List Value} {st : Value} :
    EvalExp (simEnv B) (VarEnv.empty.bindVals (defσ l st)) (.cmpE .eqOp .boolT (.varE "rectype")
      (.caseE "REC" (.caseE "%" (.tupE [.iterE (.varE "subtype") subsNIt])))) (.bool true) :=
  ⟨10, by simp [subsNIt, defσ, evalExp, evalExps, evalIterE, evalIterList, evalRounds, evalDoms,
    iterRows, iterRow, domVar, domSrc, VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind,
    cmpValues, natV, Value.asNat?]⟩

set_option linter.unusedSimpArgs false in
/-- `i < n`, at `i = 0`, `n = 1`. -/
theorem evalExp_iLtN {l : List Value} {st : Value} :
    EvalExp (simEnv B) (VarEnv.empty.bindVals (defσ l st))
      (.cmpE .ltOp (.numT .natT) (.varE "i") (.varE "n")) (.bool true) :=
  ⟨3, by simp [defσ, evalExp, VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, cmpValues,
    natV, Num.cmp]⟩

/-- **`Deftype_ok`, at a one-member group**: the group is checked in `ctxR (st :: l)`, the
composition `{RECS st} ⊕ ctxR l` (SpecTec appends; Core's `TypeCtx.withRecs` replaces). -/
theorem dderivesB_deftypeOk1 (O : ElseI) {l : List Value} {st : Value}
    (hc : TypedV (simEnv B) (.varT "context" []) (ctxR l))
    (hrt : TypedV (simEnv B) (.varT "rectype" []) (.case "REC" (.case "%" (.tuple [.list [st]]))))
    (hst : TypedV (simEnv B) (.varT "subtype" []) st)
    (hd : DDerivesB (simEnv B) O "Rectype_ok2" "%|-%:%" []
      (.tuple [ctxR (st :: l), .case "REC" (.case "%" (.tuple [.list [st]])), .case "OK" (natV 0)])) :
    DDerivesB (simEnv B) O "Deftype_ok" "%|-%:OK" []
      (.tuple [ctxR l, .case "_DEF" (.tuple [.case "REC" (.case "%" (.tuple [.list [st]])),
        natV 0])]) :=
  dderivesB_of_ruleAt ruleAt_deftypeOk (self_mem_conclAlts _) (defσ l st)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (hrt _ (valsOnly_bind _))
      (QuantsOk.cons rfl (typedV_n 0 _ (valsOnly_bind _)) (QuantsOk.cons rfl
        (typedV_n 1 _ (valsOnly_bind _)) (QuantsOk.cons rfl
          (typedV_list_iff.2 (fun _ hu => List.mem_singleton.1 hu ▸ hst) _
            (valsOnly_bind _)) QuantsOk.nil)))))
    (evalExp_tup2 (evalExp_var rfl) (evalExp_case (evalExp_tup2 (evalExp_var rfl)
      (evalExp_var rfl))))
    (premsB_cons (.rulePr (evalArgs_nil _ _) (evalExp_tup3 evalExp_recsCtx (evalExp_var rfl)
        (evalExp_case (evalExp_numE_iff.2 rfl))) hd) <|
      premsB_cons (.ifPr evalExp_rectypeEq) <| premsB_cons (.ifPr evalExp_iLtN) premsB_nil)

end Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB
