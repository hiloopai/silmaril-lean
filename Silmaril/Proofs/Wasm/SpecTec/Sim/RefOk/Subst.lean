module

public import Silmaril.Wasm.SpecTec.Sim.Prims.Thms
public import Silmaril.Wasm.SpecTec.Sim.Integrate.Thms

/-!
# Track refok: `$subst_typevar` and `$subst_heaptype` on images (gap 4, `$inst_reftype`)

`$inst_reftype(m, rt) = $subst_all_reftype(rt, m.TYPES)`, and

```
def $subst_all_reftype(rt, tu^n) = $subst_reftype(rt, (_IDX i)^(i<n), tu^n)
def $subst_reftype(REF null? ht, tv*, tu*) = REF null? $subst_heaptype(ht, tv*, tu*)
def $subst_heaptype(tv', tv*, tu*) = $subst_typevar(tv', tv*, tu*)      -- tv' : typevar
def $subst_heaptype(dt, tv*, tu*) = $subst_deftype(dt, tv*, tu*)        -- dt : deftype
def $subst_heaptype(ht, tv*, tu*) = ht                                  -- otherwise
def $subst_typevar(tv, eps, eps) = tv
def $subst_typevar(tv, tv_1 tv'*, tu_1 tu'*) = tu_1                     -- if tv = tv_1
def $subst_typevar(tv, tv_1 tv'*, tu_1 tu'*) = $subst_typevar(tv, tv'*, tu'*)  -- otherwise
```

This file evaluates the last two: `$subst_typevar` is a first-match lookup (`typevarLookup`,
`tryClauses_substTypevar`, by induction on the list), and `$subst_heaptype` on the image of a
source heap type is the identity on abstract heap types and the lookup on `_IDX x`
(`callDef_substHeaptype_abs`, `callDef_substHeaptype_idx`). The typevar test of the first
clause and the deftype test of the second are the evaluator's `SubE` argument test
(`Sem.argSubOk`, the typing track's upstream item U1): `_IDX x` is a `typevar`, no abstract heap
type is, and neither is a `deftype`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.RefOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (TryClausesUndef)
open Silmaril.SpecTec.Equiv.Validation (tyV absV matchExp_list_iff)
open Silmaril.SpecTec.Equiv.Execution (matchExps_one_iff matchExp_freshVar_iff patLen_listE
  matchExp_catE_ofLeft)
open Silmaril.Wasm
open Silmaril.Wasm.Validation

/-! ## Patterns -/

/-- `x*` over the domain `xs`, as a list iteration. -/
abbrev starE (x xs : IL.Id) : Exp := .iterE (.varE x) (.mk .list [.mk x (.varE xs)])

/-- `[y] ++ x*`, the cons pattern of `$subst_typevar`. -/
abbrev consPat (y x xs : IL.Id) : Exp := .catE (.listE [.varE y]) (starE x xs)

/-- The IL type `typevar`. -/
abbrev typevarT : Typ := .varT "typevar" []
/-- The IL type `typeuse`. -/
abbrev typeuseT : Typ := .varT "typeuse" []
/-- The IL type `heaptype`. -/
abbrev heaptypeT : Typ := .varT "heaptype" []
/-- The IL type `deftype`. -/
abbrev deftypeT : Typ := .varT "deftype" []

/-- The argument patterns of the second and third clauses of `$subst_typevar`. -/
abbrev typevarConsPats : List Arg :=
  [.expA (.varE "tv"), .expA (consPat "tv_1" "tv'" "tv'*"), .expA (consPat "tu_1" "tu'" "tu'*")]

/-- The tail arguments `tv*, tu*` of every `$subst_*` clause. -/
abbrev tvtuPats : List Arg := [.expA (starE "tv" "tv*"), .expA (starE "tu" "tu*")]

/-- The definitions, as the script has them (quantifiers and unused bodies left open). -/
structure SubstDefs (env : Env) : Prop where
  typevar : ∃ ps t q₁ q₂ q₃, env.findDef? "subst_typevar" = some (ps, t,
    [.defD q₁ [.expA (.varE "tv"), .expA (.listE []), .expA (.listE [])]
        (.subE (.varE "tv") typevarT typeuseT) [],
      .defD q₂ typevarConsPats (.varE "tu_1") [.ifPr (.cmpE .eqOp .boolT (.varE "tv") (.varE "tv_1"))],
      .defD q₃ typevarConsPats (.callE "subst_typevar" [.expA (.varE "tv"),
        .expA (starE "tv'" "tv'*"), .expA (starE "tu'" "tu'*")]) [.elsePr]])
  heaptype : ∃ ps t q₁ q₂ q₃ b₂, env.findDef? "subst_heaptype" = some (ps, t,
    [.defD q₁ (.expA (.subE (.varE "tv'") typevarT heaptypeT) :: tvtuPats)
        (.subE (.callE "subst_typevar" (.expA (.varE "tv'") :: tvtuPats)) typeuseT heaptypeT) [],
      .defD q₂ (.expA (.subE (.varE "dt") deftypeT heaptypeT) :: tvtuPats) b₂ [],
      .defD q₃ (.expA (.varE "ht") :: tvtuPats) (.varE "ht") [.elsePr]])

set_option maxRecDepth 100000 in
/-- `simEnv B` has them. -/
theorem substDefs_simEnv (B : Builtins) : SubstDefs (simEnv B) :=
  ⟨⟨_, _, _, _, _, rfl⟩, ⟨_, _, _, _, _, _, rfl⟩⟩

/-! ## Matching -/

/-- `x*` binds its domain to a list. -/
theorem matchExp_star {env : Env} {ρ : VarEnv} {x xs : IL.Id} {vs : List Value}
    (hx : ρ.findVal? x = none) (hxs : ρ.findVal? xs = none) (hx' : x ≠ "_") :
    MatchExp env ρ (starE x xs) (.list vs) (ρ.bindVal xs (.list vs)) :=
  (Equiv.Execution.matchExp_iterE_list_iff (Equiv.Execution.bindsVar_varE x) hx hx').2
    ⟨vs, rfl, (matchExp_freshVar_iff hxs).2 rfl⟩

/-- `[y] ++ x*` binds the head and the tail of a non-empty list. -/
theorem matchExp_consPat {env : Env} {ρ : VarEnv} {y x xs : IL.Id} {a : Value}
    {al : List Value} (hy : ρ.findVal? y = none) (hx : (ρ.bindVal y a).findVal? x = none)
    (hxs : (ρ.bindVal y a).findVal? xs = none) (hx' : x ≠ "_") :
    MatchExp env ρ (consPat y x xs) (.list (a :: al)) ((ρ.bindVal y a).bindVal xs (.list al)) :=
  matchExp_catE_ofLeft (j := 1) (m := 1) patLen_listE (by simp)
    (matchExp_list_iff.2 ⟨[a], by simp, matchExps_one_iff.2 ⟨a, rfl,
      (matchExp_freshVar_iff hy).2 rfl⟩⟩)
    (by simpa using (Equiv.Execution.matchExp_iterE_list_iff (Equiv.Execution.bindsVar_varE x) hx
      hx').2 ⟨al, rfl, (matchExp_freshVar_iff hxs).2 rfl⟩)

/-- `[]` fails definitely on a non-empty list. -/
theorem matchArg_nil_undef {env : Env} {ρ : VarEnv} {a : Value} {al : List Value} :
    ∃ n, matchArg n env ρ (.expA (.listE [])) (.val (.list (a :: al))) = .error .undef :=
  ⟨3, by simp [matchArg, argSubOk, matchExp, matchExps, Value.asList?, Bind.bind, Except.bind]⟩

/-! ## `$subst_typevar` -/

/-- The first-match lookup `$subst_typevar` computes. -/
def typevarLookup (tv : Value) : List Value → List Value → Value
  | a :: al, b :: bl => if tv = a then b else typevarLookup tv al bl
  | _, _ => tv

/-- The scope of the cons clauses. -/
abbrev consScope (TV a b : Value) (al bl : List Value) : VarEnv :=
  ((((VarEnv.empty.bindVal "tv" TV).bindVal "tv_1" a).bindVal "tv'*" (.list al)).bindVal
    "tu_1" b).bindVal "tu'*" (.list bl)

/-- The cons clauses' patterns bind head and tail of both lists. -/
theorem matchArgs_typevarCons {env : Env} (TV a b : Value) (al bl : List Value) :
    MatchArgs env VarEnv.empty typevarConsPats [.val TV, .val (.list (a :: al)),
      .val (.list (b :: bl))] (consScope TV a b al bl) :=
  matchArgs_cons (matchArg_expA (matchExp_varE rfl))
    (matchArgs_cons (matchArg_expA (matchExp_consPat rfl rfl rfl (by decide)))
      (matchArgs_cons (matchArg_expA (matchExp_consPat rfl rfl rfl (by decide))) matchArgs_nil))

/-- `$subst_typevar(tv, eps, eps) = tv`. -/
theorem tryClauses_substTypevar_nil {env : Env} {q₁ : List Param} {cs : List Clause}
    (TV : Value) :
    TryClauses env (.defD q₁ [.expA (.varE "tv"), .expA (.listE []), .expA (.listE [])]
        (.subE (.varE "tv") typevarT typeuseT) [] :: cs) [.val TV, .val (.list []), .val (.list [])]
      (typevarLookup TV [] []) :=
  tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
    (matchArgs_cons (matchArg_expA (matchExp_list_iff.2 ⟨[], rfl,
      Equiv.Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩)) (matchArgs_cons (matchArg_expA
        (matchExp_list_iff.2 ⟨[], rfl, Equiv.Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩))
          matchArgs_nil))) premsHold_nil (evalExp_subE_iff.2 (evalExp_var (by rfl)))

/-- The cons clauses, when the head is the variable looked up. -/
theorem tryClauses_typevarCons_hit {env : Env} {q₂ : List Param} {cs : List Clause}
    (TV b : Value) (al bl : List Value) :
    TryClauses env (.defD q₂ typevarConsPats (.varE "tu_1")
        [.ifPr (.cmpE .eqOp .boolT (.varE "tv") (.varE "tv_1"))] :: cs)
      [.val TV, .val (.list (TV :: al)), .val (.list (b :: bl))]
      (typevarLookup TV (TV :: al) (b :: bl)) := by
  have hv : typevarLookup TV (TV :: al) (b :: bl) = b := by simp [typevarLookup]
  have hc : cmpValues .eqOp TV TV = .ok (.bool true) := by simp [cmpValues]
  rw [hv]
  exact tryClauses_hit (matchArgs_typevarCons TV TV b al bl) (premsHold_ifPr
    (evalExp_cmpE_iff.2 ⟨TV, TV, evalExp_var rfl, evalExp_var rfl, hc⟩)) (evalExp_var rfl)

/-- The cons clauses, when the head is another variable: the recursive call. -/
theorem tryClauses_typevarCons_skip {env : Env} {ps : List Param} {t : Typ}
    {cs : List Clause} (hd : env.findDef? "subst_typevar" = some (ps, t, cs))
    {q₂ q₃ : List Param} (TV a b : Value) (al bl : List Value) (he : TV ≠ a)
    (hrec : TryClauses env cs [.val TV, .val (.list al), .val (.list bl)]
      (typevarLookup TV al bl)) :
    TryClauses env [.defD q₂ typevarConsPats (.varE "tu_1")
        [.ifPr (.cmpE .eqOp .boolT (.varE "tv") (.varE "tv_1"))],
      .defD q₃ typevarConsPats (.callE "subst_typevar" [.expA (.varE "tv"),
        .expA (starE "tv'" "tv'*"), .expA (starE "tu'" "tu'*")]) [.elsePr]]
      [.val TV, .val (.list (a :: al)), .val (.list (b :: bl))]
      (typevarLookup TV (a :: al) (b :: bl)) := by
  have hv : typevarLookup TV (a :: al) (b :: bl) = typevarLookup TV al bl := by
    simp [typevarLookup, he]
  have hc : cmpValues .eqOp TV a = .ok (.bool false) := by simp [cmpValues, he]
  have hm : MatchArgs env VarEnv.empty typevarConsPats [.val TV, .val (.list (a :: al)),
      .val (.list (b :: bl))] (consScope TV a b al bl) := matchArgs_typevarCons TV a b al bl
  have hargs : EvalArgs env (consScope TV a b al bl) [.expA (.varE "tv"),
      .expA (starE "tv'" "tv'*"), .expA (starE "tu'" "tu'*")]
      [.val TV, .val (.list al), .val (.list bl)] :=
    Equiv.evalArgs_cons (evalExp_var rfl) (Equiv.evalArgs_cons
      (Equiv.Execution.evalExp_iterPat (by decide) rfl)
      (Equiv.evalArgs_cons (Equiv.Execution.evalExp_iterPat (by decide) rfl) Equiv.evalArgs_nil))
  rw [hv]
  exact tryClauses_skip_prem hm (premsUndef_ifPr (evalExp_cmpE_iff.2
    ⟨TV, a, evalExp_var rfl, evalExp_var rfl, hc⟩))
    (tryClauses_hit hm premsHold_elsePr
      (evalExp_callE_iff.2 (callDef_of_tryClauses rfl hd hargs hrec)))

/-- **`$subst_typevar` is the first-match lookup**, on lists of equal length. -/
theorem tryClauses_substTypevar {env : Env} (D : SubstDefs env) (TV : Value) :
    ∀ (tvs tus : List Value), tvs.length = tus.length →
      ∃ cs, (∃ ps t, env.findDef? "subst_typevar" = some (ps, t, cs)) ∧
        TryClauses env cs [.val TV, .val (.list tvs), .val (.list tus)]
          (typevarLookup TV tvs tus) := by
  obtain ⟨ps, t, q₁, q₂, q₃, hd⟩ := D.typevar
  intro tvs
  induction tvs with
  | nil =>
    intro tus hl
    obtain rfl : tus = [] := List.eq_nil_of_length_eq_zero hl.symm
    exact ⟨_, ⟨ps, t, hd⟩, tryClauses_substTypevar_nil TV⟩
  | cons a al ih =>
    intro tus hl
    obtain ⟨b, bl, rfl⟩ : ∃ b bl, tus = b :: bl := List.exists_cons_of_length_eq_add_one hl.symm
    obtain ⟨cs, ⟨ps', t', hd'⟩, hrec⟩ := ih bl (by simpa using hl)
    rw [hd] at hd'
    cases hd'
    refine ⟨_, ⟨ps, t, hd⟩, tryClauses_skip_match (matchArgs_cons_undef_tail
      (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons_undef matchArg_nil_undef)) ?_⟩
    by_cases he : TV = a
    · subst he
      exact tryClauses_typevarCons_hit TV b al bl
    · exact tryClauses_typevarCons_skip hd TV a b al bl he hrec

/-- `$subst_typevar(tv, tv*, tu*)` as a call, for argument expressions with those values. -/
theorem evalExp_substTypevar {env : Env} (D : SubstDefs env) {ρ : VarEnv}
    (hρ : ρ.findDef? "subst_typevar" = none) {e₁ e₂ e₃ : Exp} {TV : Value}
    {tvs tus : List Value} (hl : tvs.length = tus.length) (h₁ : EvalExp env ρ e₁ TV)
    (h₂ : EvalExp env ρ e₂ (.list tvs)) (h₃ : EvalExp env ρ e₃ (.list tus)) :
    EvalExp env ρ (.callE "subst_typevar" [.expA e₁, .expA e₂, .expA e₃])
      (typevarLookup TV tvs tus) := by
  obtain ⟨cs, ⟨ps, t, hd⟩, hc⟩ := tryClauses_substTypevar D TV tvs tus hl
  exact evalExp_callE_iff.2 (callDef_of_tryClauses hρ hd
    (Equiv.evalArgs_cons h₁ (Equiv.evalArgs_cons h₂ (Equiv.evalArgs_cons h₃ Equiv.evalArgs_nil)))
    hc)

/-! ## `$subst_heaptype` -/

set_option maxRecDepth 100000 in
/-- `_IDX x` is a `typevar`. -/
theorem argSubOk_typevar_idx (B : Builtins) (w : Value) :
    argSubOk (simEnv B) VarEnv.empty (.subE (.varE "tv'") typevarT heaptypeT) (.case "_IDX" w) =
      true := by
  rw [argSubOk, Aggregates.subCaseOk_case]
  rfl

set_option maxRecDepth 100000 in
/-- No abstract heap type is a `typevar`. -/
theorem argSubOk_typevar_abs (B : Builtins) (a : AbsHeapType) :
    argSubOk (simEnv B) VarEnv.empty (.subE (.varE "tv'") typevarT heaptypeT) (absV a) = false := by
  cases a <;> rfl

set_option maxRecDepth 100000 in
/-- `_IDX x` is not a `deftype`. -/
theorem argSubOk_deftype_idx (B : Builtins) (w : Value) :
    argSubOk (simEnv B) VarEnv.empty (.subE (.varE "dt") deftypeT heaptypeT) (.case "_IDX" w) =
      false := by
  rw [argSubOk, Aggregates.subCaseOk_case]
  rfl

set_option maxRecDepth 100000 in
/-- No abstract heap type is a `deftype`. -/
theorem argSubOk_deftype_abs (B : Builtins) (a : AbsHeapType) :
    argSubOk (simEnv B) VarEnv.empty (.subE (.varE "dt") deftypeT heaptypeT) (absV a) = false := by
  cases a <;> rfl

/-- The scope of `$subst_heaptype`'s clauses. -/
abbrev heapScope (x : IL.Id) (H : Value) (tvs tus : List Value) : VarEnv :=
  ((VarEnv.empty.bindVal x H).bindVal "tv*" (.list tvs)).bindVal "tu*" (.list tus)

/-- `$subst_heaptype` on an abstract heap type is the identity. -/
theorem tryClauses_substHeaptype_abs (B : Builtins) (a : AbsHeapType) (tvs tus : List Value) :
    ∃ cs, (∃ ps t, (simEnv B).findDef? "subst_heaptype" = some (ps, t, cs)) ∧
      TryClauses (simEnv B) cs [.val (absV a), .val (.list tvs), .val (.list tus)] (absV a) := by
  obtain ⟨ps, t, q₁, q₂, q₃, b₂, hd⟩ := (substDefs_simEnv B).heaptype
  refine ⟨_, ⟨ps, t, hd⟩, tryClauses_skip_match (matchArgs_cons_undef
    (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub (argSubOk_typevar_abs B a)))
    (tryClauses_skip_match (matchArgs_cons_undef
      (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub (argSubOk_deftype_abs B a))) ?_)⟩
  exact tryClauses_hit (ρ₀ := heapScope "ht" (absV a) tvs tus)
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
      (matchArg_expA (matchExp_star rfl rfl (by decide))) (matchArgs_cons
        (matchArg_expA (matchExp_star rfl rfl (by decide))) matchArgs_nil)))
    premsHold_elsePr (evalExp_var rfl)

/-- `$subst_heaptype` on a type variable `_IDX x` is the lookup. -/
theorem tryClauses_substHeaptype_idx (B : Builtins) (w : Value) (tvs tus : List Value)
    (hl : tvs.length = tus.length) :
    ∃ cs, (∃ ps t, (simEnv B).findDef? "subst_heaptype" = some (ps, t, cs)) ∧
      TryClauses (simEnv B) cs [.val (.case "_IDX" w), .val (.list tvs), .val (.list tus)]
        (typevarLookup (.case "_IDX" w) tvs tus) := by
  obtain ⟨ps, t, q₁, q₂, q₃, b₂, hd⟩ := (substDefs_simEnv B).heaptype
  refine ⟨_, ⟨ps, t, hd⟩, tryClauses_hit (ρ₀ := heapScope "tv'" (.case "_IDX" w) tvs tus)
    (matchArgs_cons (matchArg_expA (Prims.matchExp_subE (matchExp_varE rfl))
      (argSubOk_typevar_idx B w)) (matchArgs_cons
      (matchArg_expA (matchExp_star rfl rfl (by decide))) (matchArgs_cons
        (matchArg_expA (matchExp_star rfl rfl (by decide))) matchArgs_nil)))
    premsHold_nil ?_⟩
  exact evalExp_subE_iff.2 (evalExp_substTypevar (substDefs_simEnv B) rfl hl (evalExp_var rfl)
    (Equiv.Execution.evalExp_iterPat (by decide) rfl)
    (Equiv.Execution.evalExp_iterPat (by decide) rfl))

end Silmaril.Wasm.SpecTec.Sim.RefOk
