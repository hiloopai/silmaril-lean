module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.RefOk.Subst

/-!
# Track refok: `$inst_reftype` on images (gap 4, `Residue.instReftype`)

```
def $inst_reftype(moduleinst, rt) = $subst_all_reftype(rt, moduleinst.TYPES)
def $subst_all_reftype(rt, tu^n) = $subst_reftype(rt, (_IDX i)^(i<n), tu^n)
def $subst_reftype(REF null? ht, tv*, tu*) = REF null? $subst_heaptype(ht, tv*, tu*)
```

With `Subst.lean`'s evaluation of `$subst_heaptype`, every clause here is premise-free and
evaluates on the images: `$inst_reftype(m, rt)` is `tyV (m.instRef rt)`, Core's
`(liftRef rt).substAll (m.types.map .dt)` (`instReftype_simEnv`, for every `B`). The index list
`(_IDX i)^(i<n)` is `idxList n`; the lookup of `_IDX x` in it against `m.TYPES` is the `x`-th
type when `x < |m.TYPES|` and `_IDX x` itself otherwise, which is `Subst.all`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.RefOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV absV matchExp_case_iff matchExp_tup_iff)
open Silmaril.SpecTec.Equiv.Execution (matchExps_two_iff matchExp_freshVar_iff
  matchExp_iterE_listN_iff matchIterList_single_iff bindsVar_varE)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

/-! ## The definitions -/

/-- `null?`, as a pattern and as an expression. -/
abbrev nullOpt : Exp := .iterE (.varE "null") (.mk .opt [.mk "null" (.varE "null?")])

/-- `tu^n`. -/
abbrev tuN : Exp := .iterE (.varE "tu") (.mk (.listN (.varE "n") none) [.mk "tu" (.varE "tu*")])

/-- `(_IDX i)^(i<n)`. -/
abbrev idxN : Exp :=
  .iterE (.caseE "_IDX" (.caseE "%" (.tupE [.varE "i"]))) (.mk (.listN (.varE "n") (some "i")) [])

/-- The three definitions above `$subst_heaptype`, as the script has them. -/
structure InstDefs (env : Env) : Prop where
  reftype : ∃ ps t q, env.findDef? "subst_reftype" = some (ps, t,
    [.defD q (.expA (.caseE "REF" (.tupE [nullOpt, .varE "ht"])) :: tvtuPats)
      (.caseE "REF" (.tupE [nullOpt, .callE "subst_heaptype" (.expA (.varE "ht") :: tvtuPats)]))
      []])
  allReftype : ∃ ps t q, env.findDef? "subst_all_reftype" = some (ps, t,
    [.defD q [.expA (.varE "rt"), .expA tuN]
      (.callE "subst_reftype" [.expA (.varE "rt"), .expA idxN, .expA tuN]) []])
  instReftype : ∃ ps t q, env.findDef? "inst_reftype" = some (ps, t,
    [.defD q [.expA (.varE "moduleinst"), .expA (.varE "rt")]
      (.callE "subst_all_reftype" [.expA (.varE "rt"), .expA (.subE (.dotE (.varE "moduleinst")
        "TYPES") (.iterT deftypeT .list) (.iterT typeuseT .list))]) []])

set_option maxRecDepth 100000 in
/-- `simEnv B` has them. -/
theorem instDefs_simEnv (B : Builtins) : InstDefs (simEnv B) :=
  ⟨⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩

/-! ## `(_IDX i)^(i<n)` -/

/-- The value of `(_IDX i)^(i<n)`. -/
def idxList (n : Nat) : List Value :=
  (List.range n).map fun j => .case "_IDX" (.case "%" (.tuple [.num (.natN j)]))

/-- `idxList n` has `n` elements. -/
@[simp] theorem length_idxList (n : Nat) : (idxList n).length = n := by simp [idxList]

/-- `mapM` in `Res` of a function that always succeeds. -/
theorem mapM_res_ok {α β : Type} (f : α → Res β) (g : α → β) (hf : ∀ a, f a = .ok (g a)) :
    ∀ l : List α, l.mapM f = .ok (l.map g)
  | [] => rfl
  | a :: l => by
    simp [List.mapM_cons, hf a, mapM_res_ok f g hf l, Bind.bind, Except.bind, Pure.pure,
      Except.pure]

/-- `(_IDX i)^(i<n)` evaluates to `idxList n` when `n` is bound to a numeral. -/
theorem evalExp_idxN {env : Env} {ρ : VarEnv} {n : Nat}
    (hn : ρ.findVal? "n" = some (.num (.natN n))) : EvalExp env ρ idxN (.list (idxList n)) := by
  refine ⟨9, ?_⟩
  have hr : ∀ j : Nat, evalExp 5 env (ρ.bindVals (iterRow [] (some "i") j))
      (.caseE "_IDX" (.caseE "%" (.tupE [.varE "i"]))) =
        .ok (.case "_IDX" (.case "%" (.tuple [.num (.natN j)]))) := by
    intro j
    simp [evalExp, evalExps, iterRow, VarEnv.bindVals, VarEnv.findVal?, Map.binds, Map.bind,
      Map.find?, Res.ofOption, Bind.bind, Except.bind, Functor.map, Except.map, List.mapM_cons,
      Pure.pure, Except.pure]
  have hm := mapM_res_ok (fun j => evalExp 5 env (ρ.bindVals (iterRow [] (some "i") j))
      (.caseE "_IDX" (.caseE "%" (.tupE [.varE "i"]))))
    (fun j => Value.case "_IDX" (.case "%" (.tuple [.num (.natN j)]))) hr (List.range n)
  have hnv : evalExp 7 env ρ (.varE "n") = .ok (.num (.natN n)) := by
    simp [evalExp, hn, Res.ofOption]
  have hd : evalDoms 7 env ρ [] = .ok [] := by simp [evalDoms]; rfl
  rw [evalExp]
  simp only [evalIterE, hd, hnv, evalIterList, evalRounds, iterRows, Res.ofOption, Value.asNat?,
    Bind.bind, Except.bind, List.mapM_nil, Res.assert, List.mapM_map]
  simp [Function.comp_def, hm, idxList, Pure.pure]

/-! ## `$subst_reftype` -/

/-- The scope of `$subst_reftype`'s clause. -/
abbrev refScope (N H : Value) (tvs tus : List Value) : VarEnv :=
  (((VarEnv.empty.bindVal "null?" N).bindVal "ht" H).bindVal "tv*" (.list tvs)).bindVal "tu*"
    (.list tus)

/-- `REF null? ht` binds `null?` and `ht`. -/
theorem matchExp_refPat {env : Env} (o : Option Value) (H : Value) :
    MatchExp env VarEnv.empty (.caseE "REF" (.tupE [nullOpt, .varE "ht"]))
      (.case "REF" (.tuple [.opt o, H]))
      ((VarEnv.empty.bindVal "null?" (.opt o)).bindVal "ht" H) :=
  matchExp_case_iff.2 ⟨_, rfl, matchExp_tup_iff.2 ⟨_, rfl, matchExps_two_iff.2 ⟨_, _, _, rfl,
    (Equiv.ExecReadAggregate.matchExp_optVar_iff rfl rfl (by decide)).2 ⟨o, rfl, rfl⟩,
    (matchExp_freshVar_iff rfl).2 rfl⟩⟩⟩

/-- `$subst_reftype(REF null? ht, tv*, tu*)` substitutes in `ht`. -/
theorem tryClauses_substReftype (B : Builtins) (o : Option Value) (H H' : Value)
    (tvs tus : List Value)
    (hh : ∃ cs, (∃ ps t, (simEnv B).findDef? "subst_heaptype" = some (ps, t, cs)) ∧
      TryClauses (simEnv B) cs [.val H, .val (.list tvs), .val (.list tus)] H') :
    ∃ cs, (∃ ps t, (simEnv B).findDef? "subst_reftype" = some (ps, t, cs)) ∧
      TryClauses (simEnv B) cs [.val (.case "REF" (.tuple [.opt o, H])), .val (.list tvs),
        .val (.list tus)] (.case "REF" (.tuple [.opt o, H'])) := by
  obtain ⟨ps, t, q, hd⟩ := (instDefs_simEnv B).reftype
  obtain ⟨cs, ⟨ps', t', hd'⟩, hc⟩ := hh
  refine ⟨_, ⟨ps, t, hd⟩, tryClauses_hit (ρ₀ := refScope (.opt o) H tvs tus)
    (matchArgs_cons (matchArg_expA (matchExp_refPat o H)) (matchArgs_cons
      (matchArg_expA (matchExp_star rfl rfl (by decide))) (matchArgs_cons
        (matchArg_expA (matchExp_star rfl rfl (by decide))) matchArgs_nil)))
    premsHold_nil (evalExp_case (evalExp_tup2 ?_ ?_))⟩
  · exact IntNumeric.evalExp_iterOpt rfl (fun w hw => ⟨w, hw, evalExp_var (by simp [hw]; rfl)⟩)
      (fun hn => hn)
  · exact evalExp_callE_iff.2 (callDef_of_tryClauses rfl hd' (Equiv.evalArgs_cons
      (evalExp_var rfl) (Equiv.evalArgs_cons (Equiv.Execution.evalExp_iterPat (by decide) rfl)
        (Equiv.evalArgs_cons (Equiv.Execution.evalExp_iterPat (by decide) rfl)
          Equiv.evalArgs_nil))) hc)

/-! ## The lookup against `m.TYPES` -/

/-- The image `_IDX %(j)` of the type variable `j`. -/
abbrev idxTV (j : Nat) : Value := .case "_IDX" (.case "%" (.tuple [.num (.natN j)]))

/-- The lookup of `_IDX x` against `(_IDX (k + i))^(i<|tus|)`. -/
theorem typevarLookup_range' (x : Nat) :
    ∀ (k : Nat) (tus : List DefType),
      typevarLookup (idxTV x) ((List.range' k tus.length).map idxTV) (tus.map tyV) =
        if k ≤ x then ((tus[x - k]?).map tyV).getD (idxTV x) else idxTV x
  | k, [] => by split <;> simp [typevarLookup]
  | k, d :: ds => by
    have ih := typevarLookup_range' x (k + 1) ds
    simp only [List.length_cons, List.range'_succ, List.map_cons, typevarLookup]
    by_cases hx : x = k
    · subst hx
      simp
    · have hne : idxTV x ≠ idxTV k := by simp [idxTV, hx]
      simp only [hne, ↓reduceIte, ih]
      by_cases hk : k ≤ x
      · have hk' : k + 1 ≤ x := by omega
        have he : x - k = (x - (k + 1)) + 1 := by omega
        simp only [hk', hk, ↓reduceIte, he, List.getElem?_cons_succ]
      · have hk' : ¬ k + 1 ≤ x := by omega
        simp only [hk', hk, ↓reduceIte]

/-- Looking `_IDX x` up in `(_IDX i)^(i<n)` against `tu^n` is `Subst.all`. -/
theorem typevarLookup_idxList (x : Nat) (tus : List DefType) :
    typevarLookup (idxTV x) (idxList tus.length) (tus.map tyV) =
      tyV (((Subst.all (tus.map .dt)) (.idx x)).getD (.idx x)) := by
  have h := typevarLookup_range' x 0 tus
  rw [← List.range_eq_range'] at h
  simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero] at h
  rw [idxList, h, Subst.all, List.getElem?_map]
  cases tus[x]? <;> rfl

/-! ## `$inst_reftype` -/

/-- The image of a source heap type is the image of its lift. -/
theorem encode_heap (h : HeapType) : Encode.toValue h = tyV (liftHeap h) := by
  rcases h with a | x
  · cases a <;> rfl
  · rfl

/-- The image of a source reference type. -/
theorem encode_refType (r : RefType) : Encode.toValue r =
    .case "REF" (.tuple [.opt (if r.nullable then some (.case "NULL" (.tuple [])) else none),
      tyV (liftHeap r.heap)]) := by
  obtain ⟨b, h⟩ := r
  rw [← encode_heap]
  cases b <;> rfl

/-- `tu^n` binds `n` and `tu*` to a list. -/
theorem matchExp_tuN {env : Env} {ρ : VarEnv} {vs : List Value} (hn : ρ.findVal? "n" = none)
    (htu : (ρ.bindVal "n" (.num (.natN vs.length))).findVal? "tu" = none)
    (hts : (ρ.bindVal "n" (.num (.natN vs.length))).findVal? "tu*" = none) :
    MatchExp env ρ tuN (.list vs)
      ((ρ.bindVal "n" (.num (.natN vs.length))).bindVal "tu*" (.list vs)) :=
  matchExp_iterE_listN_iff.2 ⟨vs, _, rfl, (matchExp_freshVar_iff hn).2 rfl,
    (matchIterList_single_iff (bindsVar_varE "tu") htu (by decide)).2
      ((matchExp_freshVar_iff hts).2 rfl)⟩

/-- `$subst_all_reftype(rt, tu^n)` for `tu^n` the images of `ds`, by the heap-type step `hh`. -/
theorem evalExp_substAllReftype (B : Builtins) {ρ : VarEnv}
    (hρ : ρ.findDef? "subst_all_reftype" = none) {e₁ e₂ : Exp} (o : Option Value) (H H' : Value)
    (ds : List DefType)
    (hh : ∃ cs, (∃ ps t, (simEnv B).findDef? "subst_heaptype" = some (ps, t, cs)) ∧
      TryClauses (simEnv B) cs [.val H, .val (.list (idxList ds.length)),
        .val (.list (ds.map tyV))] H')
    (h₁ : EvalExp (simEnv B) ρ e₁ (.case "REF" (.tuple [.opt o, H])))
    (h₂ : EvalExp (simEnv B) ρ e₂ (.list (ds.map tyV))) :
    EvalExp (simEnv B) ρ (.callE "subst_all_reftype" [.expA e₁, .expA e₂])
      (.case "REF" (.tuple [.opt o, H'])) := by
  obtain ⟨ps, t, q, hd⟩ := (instDefs_simEnv B).allReftype
  obtain ⟨cs, ⟨ps', t', hd'⟩, hc⟩ := tryClauses_substReftype B o H H' _ _ hh
  have hlen : (ds.map tyV).length = ds.length := List.length_map ..
  refine evalExp_callE_iff.2 (callDef_of_tryClauses hρ hd (Equiv.evalArgs_cons h₁
    (Equiv.evalArgs_cons h₂ Equiv.evalArgs_nil)) (tryClauses_hit
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
        (matchArg_expA (matchExp_tuN rfl rfl rfl)) matchArgs_nil)) premsHold_nil ?_))
  refine evalExp_callE_iff.2 (callDef_of_tryClauses rfl hd' (Equiv.evalArgs_cons
    (evalExp_var rfl) (Equiv.evalArgs_cons ?_ (Equiv.evalArgs_cons
      (Equiv.ExecReadAggregate.evalExp_iterNVar (by decide) rfl rfl) Equiv.evalArgs_nil))) hc)
  rw [← hlen]
  exact evalExp_idxN rfl

/-- The `TYPES` field of an encoded module instance. -/
theorem field_types (m : ModuleInst) :
    (RefsGC.moduleInstToValue' m).field? "TYPES" = some (.list (m.types.map tyV)) := by
  simp [RefsGC.moduleInstToValue', Equiv.RuntimeBridge.moduleInstToValue, Value.field?]

/-- **`$inst_reftype(m, rt)` is the image of Core's `m.instRef rt`**, in every `simEnv B`. -/
theorem instReftype_simEnv (B : Builtins) (ρ : VarEnv) (e₁ e₂ : Exp) (m : ModuleInst)
    (rt : RefType) (hρ : ρ.findDef? "inst_reftype" = none)
    (h₁ : EvalExp (simEnv B) ρ e₁ (RefsGC.moduleInstToValue' m))
    (h₂ : EvalExp (simEnv B) ρ e₂ (Encode.toValue rt)) :
    EvalExp (simEnv B) ρ (.callE "inst_reftype" [.expA e₁, .expA e₂])
      (CT.elemType (m.instRef rt)) := by
  obtain ⟨ps, t, q, hd⟩ := (instDefs_simEnv B).instReftype
  obtain ⟨b, h⟩ := rt
  refine evalExp_callE_iff.2 (callDef_of_tryClauses hρ hd (Equiv.evalArgs_cons h₁
    (Equiv.evalArgs_cons h₂ Equiv.evalArgs_nil)) (tryClauses_hit
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
        (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)) premsHold_nil ?_))
  have hT : EvalExp (simEnv B) ((VarEnv.empty.bindVal "moduleinst" (RefsGC.moduleInstToValue' m)).bindVal
      "rt" (Encode.toValue (RefType.mk b h))) (.subE (.dotE (.varE "moduleinst") "TYPES")
        (.iterT deftypeT .list) (.iterT typeuseT .list)) (.list (m.types.map tyV)) :=
    evalExp_subE_iff.2 (evalExp_dotE_iff.2 ⟨_, evalExp_var rfl, field_types m⟩)
  rw [encode_refType] at hT ⊢
  rcases h with a | x
  · convert evalExp_substAllReftype B rfl (if b then some (.case "NULL" (.tuple [])) else none)
      _ _ m.types (tryClauses_substHeaptype_abs B a _ _) (evalExp_var (x := "rt") (by rfl))
      hT using 1
    cases b <;> rfl
  · convert evalExp_substAllReftype B rfl (if b then some (.case "NULL" (.tuple [])) else none)
      _ _ m.types (tryClauses_substHeaptype_idx B (.case "%" (.tuple [.num (.natN x.toNat)]))
        (idxList m.types.length) (m.types.map tyV) (by simp))
      (evalExp_var (x := "rt") (by rfl)) hT using 1
    rw [typevarLookup_idxList]
    cases b <;> rfl

end Silmaril.Wasm.SpecTec.Sim.RefOk
